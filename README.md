# NeST

This is the code repository for NeST, the Neuro-Symbolic Transpiler.

### Instructions

The code herein should compile readily. The intended way of getting your libraries in order is via the haskell tool Stack. You can find it [here](https://docs.haskellstack.org/en/stable/) , or on linux download it like so:

```
curl -sSL https://get.haskellstack.org/ | sh
```

From there,
```
stack run
```
should run the software.

Currently, the transpiler lacks convenience features such as a front end. Use the Lib or Main files to hard-code the program you wish, then observe stdout for the transpiled program. See the Examples file for example programs.

### About

Some of the features of NeST we have described are implemented in a Proof of Concept manner and may not work as intended in all cases. If you believe you have encountered such a case, feel free to reach out. Contribuations are of course also welcome.

You can cite this work as such: Viktor Pfanschilling, Hikaru Shindo, Devendra Singh Dhami, Kristian Kersting (2022): Sum-Product Loop Programming: From Probabilistic Circuits to Loop Programming. In Proceedings of the 19th International Conference on Principles of Knowledge Representation and Reasoning (KR).

This repository is somewhat temporary. We intend to move the repository soon.
