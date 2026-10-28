// The Go oracle for tests/run_tests.py: package hpack of
// golang.org/x/net/http2/hpack, at the version go.mod pins (go.sum
// holds its hash).
//
// Each line of standard input is one request in the form `hpack serve`
// reads (octets in lower-case hex, `-` for none; numbers in decimal),
// and each answer is in the form it writes, `OK ...` or `FAIL`. A
// request the package cannot answer is answered `n/a`, and a line this
// program cannot read `error`.
//
//	huffdec HEX         HuffmanDecode
//	huffenc HEX         AppendHuffmanString
//	strdec HEX          a Decoder made by NewDecoder(4096, nil) reads,
//	                    with DecodeFull, the header block 00 01 61 and
//	                    the string literal: a literal header field
//	                    without indexing, with the name "a" and the
//	                    literal as its value. The octets after the
//	                    literal are the rest. Where the literal ends is
//	                    found by writing the block one octet at a time
//	                    to another Decoder, until it gives a field or
//	                    an error.
//	static I            DecodeFull of the indexed header field I.
//	intmax 5 MAX HEX    a dynamic table size update (top bits 001, then
//	                    the integer with a 5-bit prefix), read by a
//	                    Decoder that allows tables up to MAX, for MAX up
//	                    to 2^32 - 1. The value is the least allowed size
//	                    the Decoder accepts the update under, found by
//	                    bisection; the end of the integer is the least
//	                    number of octets the Decoder reads as a whole
//	                    update.
//	encint 5 1 V        what an Encoder writes for a dynamic table size
//	                    update to V, for V up to 2^32 - 1.
//
// Everything else (int, intmax and encint with other prefixes or
// limits, strenc) is `n/a`. The integer encodings that frame a static
// index or a Huffman string are written here; they are framing, not
// what is under test.
package main

import (
	"bufio"
	"bytes"
	"encoding/hex"
	"fmt"
	"io"
	"math"
	"os"
	"strconv"
	"strings"

	"golang.org/x/net/http2/hpack"
)

func field(f string) ([]byte, bool) {
	if f == "-" {
		return []byte{}, true
	}
	if f == "" || strings.ToLower(f) != f {
		return nil, false
	}
	b, err := hex.DecodeString(f)
	return b, err == nil
}

func toField(b []byte) string {
	if len(b) == 0 {
		return "-"
	}
	return hex.EncodeToString(b)
}

// number reads a decimal field: ok is false when it is not one, and
// big is true when it does not fit in a uint64.
func number(f string) (n uint64, ok bool, big bool) {
	if f == "" || strings.Trim(f, "0123456789") != "" {
		return 0, false, false
	}
	n, err := strconv.ParseUint(f, 10, 64)
	return n, true, err != nil
}

// varint7 frames n as an integer with a 7-bit prefix and the top bit
// set, as an indexed field or a Huffman string length is framed.
func varint7(n uint64) []byte {
	if n < 127 {
		return []byte{0x80 | byte(n)}
	}
	out := []byte{0xff}
	n -= 127
	for n >= 128 {
		out = append(out, byte(n%128)|0x80)
		n /= 128
	}
	return append(out, byte(n))
}

// strdec reads the literal at the start of in, as the value of a
// literal header field without indexing with a new name.
func strdec(in []byte) string {
	block := append([]byte{0x00, 0x01, 0x61}, in...)
	// Where the field ends: the octet after which a streaming Decoder
	// gives it, or gives an error.
	end := len(block)
	got := 0
	d := hpack.NewDecoder(4096, func(hpack.HeaderField) { got++ })
	for k := 0; k < len(block); k++ {
		_, err := d.Write(block[k : k+1])
		if err != nil || got > 0 {
			end = k + 1
			break
		}
	}
	fields, err := hpack.NewDecoder(4096, nil).DecodeFull(block[:end])
	if err != nil {
		return "FAIL"
	}
	if len(fields) != 1 || fields[0].Name != "a" {
		return fmt.Sprintf("unreadable %d fields", len(fields))
	}
	return "OK " + toField([]byte(fields[0].Value)) + " " + toField(block[end:])
}

// update reads block, a dynamic table size update, with a Decoder that
// allows tables up to allowed: ok when the whole block is read as an
// update, done when the Decoder gave an error (not one for the block
// ending early).
func update(block []byte, allowed uint32) (ok bool, done bool) {
	d := hpack.NewDecoder(allowed, nil)
	if _, err := d.Write(block); err != nil {
		return false, true
	}
	if err := d.Close(); err != nil {
		return false, false
	}
	return true, true
}

func intmax5(max uint64, in []byte) string {
	if len(in) == 0 {
		// An empty block is no update at all.
		return "FAIL"
	}
	block := append([]byte{0x20 | in[0]&0x1f}, in[1:]...)
	end := -1
	for k := 1; k <= len(block); k++ {
		ok, done := update(block[:k], uint32(max))
		if ok {
			end = k
			break
		}
		if done {
			return "FAIL"
		}
	}
	if end < 0 {
		return "FAIL"
	}
	lo, hi := uint64(0), max // the least allowed size that reads it
	for lo < hi {
		mid := lo + (hi-lo)/2
		if ok, _ := update(block[:end], uint32(mid)); ok {
			hi = mid
		} else {
			lo = mid + 1
		}
	}
	return fmt.Sprintf("OK %d %s", lo, toField(block[end:]))
}

func encint5(v uint64) string {
	var buf bytes.Buffer
	e := hpack.NewEncoder(&buf)
	e.SetMaxDynamicTableSizeLimit(math.MaxUint32)
	e.SetMaxDynamicTableSize(uint32(v))
	if err := e.WriteField(hpack.HeaderField{Name: ":method", Value: "GET"}); err != nil {
		return "unreadable " + strconv.Quote(err.Error())
	}
	out := buf.Bytes()
	// The update, then 82 for the indexed field :method: GET.
	if len(out) < 2 || out[len(out)-1] != 0x82 {
		return "unreadable " + toField(out)
	}
	return "OK " + toField(out[:len(out)-1])
}

func answer(line string) string {
	parts := strings.Split(line, " ")
	switch {
	case len(parts) == 2 && parts[0] == "huffdec":
		d, ok := field(parts[1])
		if !ok {
			return "error"
		}
		var out bytes.Buffer
		if _, err := hpack.HuffmanDecode(&out, d); err != nil {
			return "FAIL"
		}
		return "OK " + toField(out.Bytes())
	case len(parts) == 2 && parts[0] == "huffenc":
		s, ok := field(parts[1])
		if !ok {
			return "error"
		}
		return "OK " + toField(hpack.AppendHuffmanString(nil, string(s)))
	case len(parts) == 2 && parts[0] == "strdec":
		b, ok := field(parts[1])
		if !ok {
			return "error"
		}
		return strdec(b)
	case len(parts) == 2 && parts[0] == "static":
		i, ok, big := number(parts[1])
		if !ok {
			return "error"
		}
		if big {
			return "n/a"
		}
		fields, err := hpack.NewDecoder(4096, nil).DecodeFull(varint7(i))
		if err != nil {
			return "FAIL"
		}
		if len(fields) != 1 {
			return fmt.Sprintf("unreadable %d fields", len(fields))
		}
		return "OK " + toField([]byte(fields[0].Name)) + " " + toField([]byte(fields[0].Value))
	case len(parts) == 4 && parts[0] == "intmax":
		max, ok1, big := number(parts[2])
		b, ok2 := field(parts[3])
		if !ok1 || !ok2 {
			return "error"
		}
		if parts[1] != "5" || big || max > math.MaxUint32 {
			return "n/a"
		}
		return intmax5(max, b)
	case len(parts) == 4 && parts[0] == "encint":
		v, ok, big := number(parts[3])
		if !ok {
			return "error"
		}
		if parts[1] != "5" || parts[2] != "1" || big || v > math.MaxUint32 {
			return "n/a"
		}
		return encint5(v)
	case len(parts) >= 2 && (parts[0] == "int" || parts[0] == "strenc" ||
		parts[0] == "intmax" || parts[0] == "encint"):
		return "n/a"
	}
	return "error"
}

func main() {
	in := bufio.NewReaderSize(os.Stdin, 1<<20)
	out := bufio.NewWriterSize(os.Stdout, 1<<20)
	defer out.Flush()
	for {
		line, err := in.ReadString('\n')
		if len(line) > 0 {
			fmt.Fprintln(out, answer(strings.TrimRight(line, "\r\n")))
		}
		if err == io.EOF {
			return
		}
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
	}
}
