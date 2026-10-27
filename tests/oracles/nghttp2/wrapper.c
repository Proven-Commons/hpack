/*
  The nghttp2 oracle for tests/run_tests.py: the HPACK inflater of
  libnghttp2 (nghttp2_hd_inflate_hd2), driven line by line. It is built
  against the system library, whose version tests/run_tests.py checks.

  Each line of standard input is one request in the form `hpack serve`
  reads (octets in lower-case hex, `-` for none; numbers in decimal),
  and each answer is in the form it writes, "OK ..." or "FAIL". A
  request the inflater cannot answer is answered "n/a", and a line this
  program cannot read "error".

    strdec HEX          the header block 00 01 61 and the octets: a
                        literal header field without indexing, with the
                        name "a" and the string literal as its value.
                        The inflater returns as soon as it gives the
                        field, with the number of octets it read; the
                        octets after those are the rest.
    huffdec HEX         the same, with the octets framed as a Huffman
                        string literal: H = 1 and their length.
    static I            the indexed header field I.
    intmax 5 MAX HEX    a dynamic table size update (top bits 001, then
                        the integer with a 5-bit prefix), with the
                        table size the settings allow set to MAX, for
                        MAX up to 2^32 - 1. The value is the maximum
                        table size the inflater has after it, from
                        nghttp2_hd_inflate_get_max_dynamic_table_size;
                        the end of the integer is the least number of
                        octets the inflater reads as a whole update.

  `version` is answered "OK" and the version of the library that runs.
  Everything else is "n/a". The integer encodings that frame a static
  index or a Huffman string are written here; they are framing, not
  what is under test.
*/

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <nghttp2/nghttp2.h>

static int hexval(int c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  return -1;
}

/* The octets of a field in a new buffer with `extra` free octets in
   front; their number goes in *len. NULL for a field that is not `-`
   or hex in pairs. */
static uint8_t *field(const char *f, size_t extra, size_t *len) {
  size_t n = strlen(f);
  uint8_t *out;
  if (strcmp(f, "-") == 0) {
    *len = 0;
    return calloc(extra + 1, 1);
  }
  if (n == 0 || n % 2 != 0) return NULL;
  out = calloc(extra + n / 2 + 1, 1);
  for (size_t j = 0; j < n / 2; ++j) {
    int hi = hexval(f[2 * j]), lo = hexval(f[2 * j + 1]);
    if (hi < 0 || lo < 0) {
      free(out);
      return NULL;
    }
    out[extra + j] = (uint8_t) (hi * 16 + lo);
  }
  *len = n / 2;
  return out;
}

/* A decimal field: 0 when it is one and fits in 64 bits, 1 when it is
   not decimal, 2 when it is too large. */
static int number(const char *f, uint64_t *out) {
  uint64_t n = 0;
  if (*f == 0) return 1;
  for (const char *p = f; *p; ++p)
    if (*p < '0' || *p > '9') return 1;
  for (const char *p = f; *p; ++p) {
    if (n > (UINT64_MAX - (uint64_t) (*p - '0')) / 10) return 2;
    n = n * 10 + (uint64_t) (*p - '0');
  }
  *out = n;
  return 0;
}

static void put_field(const uint8_t *b, size_t n) {
  if (n == 0) {
    fputs("-", stdout);
    return;
  }
  for (size_t j = 0; j < n; ++j) printf("%02x", b[j]);
}

/* Frames n as an integer with a 7-bit prefix and the top bit set. */
static size_t varint7(uint8_t *out, uint64_t n) {
  size_t k = 0;
  if (n < 127) {
    out[k++] = (uint8_t) (0x80 | n);
    return k;
  }
  out[k++] = 0xff;
  n -= 127;
  while (n >= 128) {
    out[k++] = (uint8_t) (n % 128 + 128);
    n /= 128;
  }
  out[k++] = (uint8_t) n;
  return k;
}

/* Inflates the first header field of block: 1 and the field in *nv,
   with the octets read in *used, or 0 when the inflater fails or the
   block ends first. */
static int first_field(nghttp2_hd_inflater *inf, const uint8_t *block, size_t len,
                       nghttp2_nv *nv, size_t *used) {
  size_t off = 0;
  for (;;) {
    int flags = 0;
    ssize_t rv = nghttp2_hd_inflate_hd2(inf, nv, &flags, block + off, len - off, 1);
    if (rv < 0) return 0;
    off += (size_t) rv;
    if (flags & NGHTTP2_HD_INFLATE_EMIT) {
      *used = off;
      return 1;
    }
    if ((flags & NGHTTP2_HD_INFLATE_FINAL) || rv == 0) return 0;
  }
}

/* Answers with the first field of block: its value, after its name
   when want_name is NULL (else the name must be want_name), and with
   with_rest the octets of the block after the field. FAIL when there
   is none. */
static void answer_field(const uint8_t *block, size_t len, const char *want_name,
                         int with_rest) {
  nghttp2_hd_inflater *inf;
  nghttp2_nv nv;
  size_t used = 0;
  if (nghttp2_hd_inflate_new(&inf) != 0) {
    puts("unreadable inflate_new");
    return;
  }
  if (!first_field(inf, block, len, &nv, &used)) {
    puts("FAIL");
  } else if (want_name && (nv.namelen != strlen(want_name) ||
                           memcmp(nv.name, want_name, nv.namelen) != 0)) {
    puts("unreadable name");
  } else {
    fputs("OK ", stdout);
    if (!want_name) {
      put_field(nv.name, nv.namelen);
      putchar(' ');
    }
    put_field(nv.value, nv.valuelen);
    if (with_rest) {
      putchar(' ');
      put_field(block + used, len - used);
    }
    putchar('\n');
  }
  nghttp2_hd_inflate_del(inf);
}

static void strdec(const char *h) {
  size_t len;
  uint8_t *b = field(h, 3, &len);
  if (b == NULL) {
    puts("error");
    return;
  }
  b[0] = 0x00;
  b[1] = 0x01;
  b[2] = 'a';
  answer_field(b, len + 3, "a", 1);
  free(b);
}

static void huffdec(const char *h) {
  size_t len;
  uint8_t *d = field(h, 0, &len);
  if (d == NULL) {
    puts("error");
    return;
  }
  uint8_t *b = malloc(len + 16);
  size_t k = 0;
  b[k++] = 0x00;
  b[k++] = 0x01;
  b[k++] = 'a';
  k += varint7(b + k, len);
  memcpy(b + k, d, len);
  answer_field(b, k + len, "a", 0);
  free(b);
  free(d);
}

static void static_entry(const char *f) {
  uint64_t i;
  int r = number(f, &i);
  if (r == 1) {
    puts("error");
    return;
  }
  if (r == 2) {
    puts("n/a");
    return;
  }
  uint8_t b[16];
  size_t k = varint7(b, i);
  answer_field(b, k, NULL, 0);
}

/* Reads block as a dynamic table size update with the settings' table
   size `max`. Returns 1 when the whole block is one update, with the
   table size it sets in *value; 0 when it ends first; -1 when the
   inflater fails. */
static int update(const uint8_t *block, size_t len, uint64_t max, uint64_t *value) {
  nghttp2_hd_inflater *inf;
  nghttp2_nv nv;
  int flags = 0, result;
  if (nghttp2_hd_inflate_new(&inf) != 0) return -1;
  if (nghttp2_hd_inflate_change_table_size(inf, (size_t) max) != 0) {
    nghttp2_hd_inflate_del(inf);
    return -1;
  }
  ssize_t rv = nghttp2_hd_inflate_hd2(inf, &nv, &flags, block, len, 0);
  if (rv < 0 || (flags & NGHTTP2_HD_INFLATE_EMIT)) {
    result = -1;
  } else {
    flags = 0;
    rv = nghttp2_hd_inflate_hd2(inf, &nv, &flags, block + len, 0, 1);
    if (rv < 0) {
      result = 0; /* the update is not whole */
    } else {
      result = 1;
      *value = nghttp2_hd_inflate_get_max_dynamic_table_size(inf);
    }
  }
  nghttp2_hd_inflate_del(inf);
  return result;
}

static void intmax(const char *n, const char *m, const char *h) {
  uint64_t max, value = 0;
  size_t len;
  int r = number(m, &max);
  uint8_t *b = field(h, 0, &len);
  if (r == 1 || b == NULL || number(n, &value) == 1) {
    puts("error");
    free(b);
    return;
  }
  if (strcmp(n, "5") != 0 || r == 2 || max > UINT32_MAX) {
    puts("n/a");
    free(b);
    return;
  }
  if (len > 0) b[0] = (uint8_t) (0x20 | (b[0] & 0x1f));
  for (size_t k = 1; k <= len; ++k) {
    int u = update(b, k, max, &value);
    if (u < 0) break;
    if (u > 0) {
      printf("OK %llu ", (unsigned long long) value);
      put_field(b + k, len - k);
      putchar('\n');
      free(b);
      return;
    }
  }
  puts("FAIL");
  free(b);
}

int main(void) {
  static char line[1 << 20];
  while (fgets(line, sizeof line, stdin)) {
    size_t n = strlen(line);
    while (n && (line[n - 1] == '\n' || line[n - 1] == '\r')) line[--n] = 0;
    char *parts[6];
    int k = 0;
    char *p = line;
    while (k < 6) {
      parts[k++] = p;
      p = strchr(p, ' ');
      if (p == NULL) break;
      *p++ = 0;
    }
    if (k == 1 && strcmp(parts[0], "version") == 0) printf("OK %s\n", nghttp2_version(0)->version_str);
    else if (k == 2 && strcmp(parts[0], "strdec") == 0) strdec(parts[1]);
    else if (k == 2 && strcmp(parts[0], "huffdec") == 0) huffdec(parts[1]);
    else if (k == 2 && strcmp(parts[0], "static") == 0) static_entry(parts[1]);
    else if (k == 4 && strcmp(parts[0], "intmax") == 0) intmax(parts[1], parts[2], parts[3]);
    else if (k >= 2 && (strcmp(parts[0], "int") == 0 || strcmp(parts[0], "intmax") == 0 ||
                        strcmp(parts[0], "encint") == 0 || strcmp(parts[0], "huffenc") == 0 ||
                        strcmp(parts[0], "strenc") == 0))
      puts("n/a");
    else puts("error");
  }
  return 0;
}
