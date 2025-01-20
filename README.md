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
stack run -- -i yourCode.spll compile -o output.py -l python
```
to generate python inference code from the code in the input file. 

You can also run the program directly from the command line using the built-in interpreter:

```
stack run -- -i yourCode.spll generate
stack run -- -i yourCode.spll probability -x 0.5
stack run -- -i yourCode.spll integrate -l 0 -h 1
```

to run the program in the forward direction, the prior distribution at x=0.5 and integrate the prior distribution from 0 to 1.

### Using the haskell interface

The functions in [Prelude.hs](src/SPLL/Prelude.hs) provide an easy to use interface for probabilistic programming. The following example declares a program, that represents the sum of two dice, generates a random sample from that program and inferes the probability of that value being produced by the program.

```
showcase :: IO ()
showcase = do
  let twoDice = Program [("main", dice 6 #<+># dice 6)] []
  let conf = CompilerConfig {verbose=0, topKThreshold=Nothing, countBranches=False, optimizerLevel=2}
  gen <- evalRandIO (runGen conf twoDice [])
  putStrLn ("Generated value: " ++ show gen)
  let VTuple (VFloat prob) (VFloat dim) = runProb conf twoDice [] gen
  putStrLn ("Probability of that value occuring: " ++ show prob)
```

You can also decare continuous distributions using the ```uniform``` or ```normal``` functions from [Prelude.hs](src/SPLL/Prelude.hs). The resulting infered probability is then a density instead of a mass. The following example samples from a normal distribution, with a standart deviation of 2 and a mean of 1. Again the program samples one value from this distribution and outputs the probability density for that value.

```
showcase2 :: IO ()
showcase2 = do
  let dist = Program [("main", normal #*# constF 2 #+# constF 1)] []
  let conf = CompilerConfig {verbose=2, topKThreshold=Nothing, countBranches=False, optimizerLevel=2}
  gen <- evalRandIO (runGen conf dist [])
  putStrLn ("Generated value: " ++ show gen)
  let VTuple (VFloat prob) (VFloat dim) = runProb conf dist [] gen
  putStrLn ("Probability density of that value occuring: " ++ show prob)
```

### About

Some of the features of NeST we have described are implemented in a Proof of Concept manner and may not work as intended in all cases. If you believe you have encountered such a case, feel free to reach out or create an issue. Contribuations are of course also welcome.

You can cite this work as such: Viktor Pfanschilling, Hikaru Shindo, Devendra Singh Dhami, Kristian Kersting (2022): Sum-Product Loop Programming: From Probabilistic Circuits to Loop Programming. In Proceedings of the 19th International Conference on Principles of Knowledge Representation and Reasoning (KR).
