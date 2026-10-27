# Planted bugs

Written by `tests/plant_bugs.py`. Each bug is a change of one line, or two for the first `Main.lean` bug, to `Hpack/Basic.lean` unless it names `Main.lean`, tested with `tests/run_tests.py --count 1000 --no-oracles`, which builds only the executable and compares it with the model alone. Every bug must give failures, and the unchanged code none. A bug that does not build, or a run that gives up or dies, counts as missed.

| Planted bug | Failures |
|---|---|
| none | 0 |
| the prefix is off by one: 2^N - 1 is written in the prefix alone | 398 |
| the decoder reads the prefix one bit wider | 43331 |
| the decoder keeps the bits above the prefix | 3377 |
| non-minimal integers are accepted | 3754 |
| the continuation bit is tested as 0x40, not 0x80 | 3389 |
| long integers: the first half is shifted by the length of the first half, not the second | 4 |
| the encoder writes 128 as a last octet | 427 |
| the limit test is < instead of ≤ | 5597 |
| EOS is not checked | 1014 |
| padding of 8 bits is allowed | 219 |
| padding may hold zeros | 53472 |
| the encoder pads with zeros | 1955 |
| one Huffman table entry is wrong: the code of ~ ends in e, not d | 1583 |
| string data one octet short is accepted | 1407 |
| the H flag is ignored | 1943 |
| the Huffman lookup compares bits with the codes one bit longer | 18589 |
| a Huffman literal gives the length of the string, not of its encoding | 801 |
| the static table is indexed from 0 | 85 |
| Main.lean: `intmax` takes any prefix size | 2 |
| Main.lean: `huffman-decode` exits with 0 when the input does not decode | 5 |

Bugs caught: 20 of 20
