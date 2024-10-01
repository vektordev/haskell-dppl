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
should run the compiler. Use -- to pass arguments to NeST rather than the build system. You can use

```
stack run -- -i yourCode.spll -o output.py -l python
```
to generate python inference code from the code in the input file. 

### About

Some of the features of NeST we have described are implemented in a Proof of Concept manner and may not work as intended in all cases. If you believe you have encountered such a case, feel free to reach out or create an issue. Contribuations are of course also welcome.

You can cite this work as such: Viktor Pfanschilling, Hikaru Shindo, Devendra Singh Dhami, Kristian Kersting (2022): Sum-Product Loop Programming: From Probabilistic Circuits to Loop Programming. In Proceedings of the 19th International Conference on Principles of Knowledge Representation and Reasoning (KR).
