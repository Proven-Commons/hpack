# hpack

A Lean rewrite of the stateless part of HPACK, the header compression format for HTTP/2. This is a Proven Commons project: it rebuilds a widely used format in Lean and proves the new code follows its written specification.

Status: not verified. No code has landed yet. The first slice is in progress and will arrive as a draft pull request. The specification has not been approved by a reviewer, so do not call this verified.

## First slice

HPACK is defined in RFC 7541. The first slice covers only the part with no state.

- Prefix integers, as in section 5.1 of RFC 7541.
- String literals with the Huffman code of Appendix B.
- Lookup in the 61 entry static table of Appendix A.

The dynamic table and its size updates are the second slice. The first slice also serves QPACK, the HTTP/3 format, which uses the same prefix integer and Huffman code.

## Main claim

Integer decoding inverts encoding for every prefix size, and the decoder returns an error instead of reading past the end of its input or past a stated limit. Huffman decoding accepts exactly the encoder outputs, which pins down the padding and end of string rules of section 5.2.

## Test oracles

- RFC 7541 Appendix C, which works through examples byte by byte.
- The hpack test case corpus, with encoder output from nghttp2, Go, Python, Node, Haskell, and Swift NIO.
- Python hpack and Go hpack.

## Score

16 out of 18, from two scorers, in the round 3 sheet in the mission repo. The sheet is mission pull request 17.

## What is not in this slice

- The dynamic table.
- Header field compression as a whole.
- Any claim about a full HTTP/2 implementation.

## Layout, when the first slice lands

The layout follows the Proven Commons template in the mission repo, under bar/template. Spec.lean holds the statements a reviewer approves. Proofs.lean holds the proofs under the same names. Main.lean holds the command line tool used by the tests. The bar check runs in CI on every change.
