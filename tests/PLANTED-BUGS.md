# Planted bugs

Written by `tests/plant_bugs.py`. Each bug is a one-line change to `Hpack/Basic.lean`, tested with `tests/run_tests.py --count 1000 --no-oracles`, which builds only the executable and compares it with the model alone. Every bug must give failures, and the unchanged code none. A bug that does not build, or a run that gives up or dies, counts as missed.

| Planted bug | Failures |
|---|---|
| none | 0 |
| the prefix is off by one: 2^N - 1 is written in the prefix alone | 398 |
| the decoder reads the prefix one bit wider | 43314 |
| the decoder keeps the bits above the prefix | 3376 |
| non-minimal integers are accepted | 3754 |
| the continuation bit is tested as 0x40, not 0x80 | 3389 |
| the encoder writes 128 as a last octet | 427 |
| the limit test is < instead of ≤ | 5597 |
| EOS is not checked | 1009 |
| padding of 8 bits is allowed | 218 |
| padding may hold zeros | 53470 |
| the encoder pads with zeros | 1948 |
| one Huffman table entry is wrong: the code of ~ ends in e, not d | 1577 |
| the string length check is off by one and reads past the end | 1407 |
| the H flag is ignored | 1936 |
| a Huffman literal gives the length of the string, not of its encoding | 799 |
| the static table is indexed from 0 | 85 |

Bugs caught: 16 of 16
