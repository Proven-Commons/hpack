# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Oracle: the model of RFC 7541 in `tests/run_tests.py`, with the Huffman code of Appendix B and the static table of Appendix A read from `tests/rfc7541.txt`, and the implementations below
- Python hpack: hpack 4.2.0 (python-hyper), the wheel pinned by SHA-256 858ac0b02280fa582b5080d68db0899c62a80375e0e5413a74970c5e518b6986, on Python 3.13.17
- Go: package hpack of golang.org/x/net/http2 v0.50.0 (h1:ucWh9eiCGyDR3vtzso0WMQinm2Dnt8cFMuQa9K33J60=), built with go version go1.24.7 linux/amd64
- nghttp2: libnghttp2 1.59.0, the HPACK inflater `nghttp2_hd_inflate_hd2` (Debian package libnghttp2-14 1.59.0-1ubuntu0.4), through `tests/oracles/nghttp2/wrapper.c` compiled with cc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0
- Oracles left out: none
- Seed: 20261027
- Inputs: 311294
- By kind: Appendix C encint 63, Appendix C huffdec 12, Appendix C huffenc 12, Appendix C int 63, Appendix C static 35, Appendix C strdec 29, Appendix C strenc 29, Appendix C, with an oracle's limit intmax 65, Huffman, 0 to 2 octets huffdec 65793, Huffman, EOS and ones huffdec 12, Huffman, EOS inserted huffdec 8000, Huffman, a zero in the padding huffdec 6705, Huffman, bit flipped huffdec 7617, Huffman, every octet huffdec 256, Huffman, every octet huffenc 257, Huffman, last octet cut huffdec 7617, Huffman, padding extended huffdec 8256, Huffman, padding of zeros huffdec 6943, integer encint 6250, integer int 5579, integer, cut short int 20092, integer, cut short, with an oracle's limit intmax 22633, integer, every high-bits value encint 2550, integer, every high-bits value int 2550, integer, every high-bits value, with an oracle's limit intmax 2630, integer, extra zero octets int 960, integer, extra zero octets, with a limit intmax 1920, integer, extra zero octets, with an oracle's limit intmax 1080, integer, with a limit intmax 11150, integer, with an oracle's limit intmax 6250, random octets encint 4000, random octets int 4000, random octets, with a limit intmax 4004, random octets, with an oracle's limit intmax 4501, random string huffdec 8000, random string huffenc 8000, random string literal strdec 16000, random string literal, H flipped strdec 16000, random string literal, cut short strdec 30468, random string literal, non-minimal length strdec 4596, random string strenc 16000, static static 108, string, edge strdec 41, string, edge strenc 28, string, edge, H flipped strdec 28, string, edge, cut short strdec 48, string, edge, non-minimal length strdec 64
- Answers that differ from the model: 0
- RFC 7541: `tests/rfc7541.txt`, SHA-256 2239d7f8fb839b69ae2e928e685559b11376888269f131512197a0e3bacf7f7a; Appendix B: 257 codes, the bits, hex and length columns agree, and the code is prefix-free and complete; Appendix A: 61 entries
- Appendix C read by the model as the RFC reads it: the integers of C.1, 3 of 3; the header blocks of C.2 to C.6, 16 of 16, each decoded to its header list and written again octet for octet
- Integers read (`int` and `intmax`): 87477, of which 27365 give a value; why the model refuses the others: the input ends first 46383, above the limit 7690, written in more octets than it needs 6039
- Huffman strings read: 119211, of which 33658 decode; why the model refuses the others: padding not all ones 65610, padding over 7 bits 11917, EOS 8026
- String literals read: 67274, of which 26932 decode; why the model refuses the others: the input ends before the string data 30508, the Huffman data: padding not all ones 5143, the length: written in more octets than it needs 4661, the length: the input ends first 16, the Huffman data: padding over 7 bits 14
- Static indices asked: 143, of which 82 are in the table
- Encodings asked for: integers 12863, Huffman 8269, string literals 16057
- Inputs the code refuses for an integer written in more octets than it needs: 10700
- Agreement with each oracle over the requests it answers: Python hpack 267580 of 270974, Go 196785 of 200466, nghttp2 189206 of 191657
- Requests each oracle answers, by operation: Python hpack: encint 12863, huffdec 119211, huffenc 8269, intmax 47157, static 143, strdec 67274, strenc 16057; Go: encint 540, huffdec 119211, huffenc 8269, intmax 5031, static 141, strdec 67274; nghttp2: huffdec 119211, intmax 5031, static 141, strdec 67274
- Malformed requests answered `error`: 75 of 75; odd but well-formed requests answered as the model says: 20 of 20
- Requests ending in CR LF: every seventh, 44470
- Last lines sent alone, with no LF, with CR LF, or with a lone CR, answered right: 4 of 4
- Failures: 0

## Where the oracles differ

Each disagreement is counted under the reason the model confirms, with the first input that showed it. The tool refuses each of these, and the oracle answers.

### Python hpack

- decode_integer reads an integer written in more octets than it needs (a last continuation octet 0 after another), up to five continuation octets, in a string length: 2330; for example `strdec ff8200ffde3d7c48dcce7fdc1ff4e6470231e91f799de7c3ffa4d3d7469e6d6efffdffdffda09fe7ff97a2fffa3d09fdffde79ffe4dff3f7ffc4fffcc9e9baaefff3161f7fff668fffea2aebbf17ffb73ffc1e9f07fef37fcfe1e5bfd191f177ac1e168c377fcb9feb8fffeffcffad3a5cff3bffd... (271 characters)`
- decode_integer reads an integer written in more octets than it needs (a last continuation octet 0 after another), up to five continuation octets: 1064; for example `intmax 1 34359738368 618000`

### Go

- readVarInt reads an integer written in more octets than it needs (a last continuation octet 0 after another), up to nine continuation octets, in a string length: 3495; for example `strdec ff8200ffde3d7c48dcce7fdc1ff4e6470231e91f799de7c3ffa4d3d7469e6d6efffdffdffda09fe7ff97a2fffa3d09fdffde79ffe4dff3f7ffc4fffcc9e9baaefff3161f7fff668fffea2aebbf17ffb73ffc1e9f07fef37fcfe1e5bfd191f177ac1e168c377fcb9feb8fffeffcffad3a5cff3bffd... (271 characters)`
- readVarInt reads an integer written in more octets than it needs (a last continuation octet 0 after another), up to nine continuation octets: 186; for example `intmax 5 4294967295 7f80000f`

### nghttp2

- the inflater reads an integer written in more octets than it needs (a last continuation octet 0 after another), up to five continuation octets, in a string length: 2330; for example `strdec ff8200ffde3d7c48dcce7fdc1ff4e6470231e91f799de7c3ffa4d3d7469e6d6efffdffdffda09fe7ff97a2fffa3d09fdffde79ffe4dff3f7ffc4fffcc9e9baaefff3161f7fff668fffea2aebbf17ffb73ffc1e9f07fef37fcfe1e5bfd191f177ac1e168c377fcb9feb8fffeffcffad3a5cff3bffd... (271 characters)`
- the inflater reads an integer written in more octets than it needs (a last continuation octet 0 after another), up to five continuation octets: 121; for example `intmax 5 4294967295 7f80000f`
