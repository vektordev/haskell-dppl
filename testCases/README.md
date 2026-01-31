# Test Cases

This folder contains the test cases for the automatic End-to-End testing framework.

Every test case consists of a program specified in a ".ppl" file and a set of assertions specified in a ".tst" file.

## What is tested
The automatic End-to-End testing framework tests that every program provided compiles correctly and produces a value in the generative direction. We test that for given sample values in the TST file, the value of the PDF matches the provided expected value. All of these steps are done with the built-in interpreter and a version of the program compiled into Python as well as Julia.

Further tests are employed for programs that declare neural networks. The Interpreter is capable of mimicking the functionality of neural networks. These Mock-Neural Networks have two modes: an NN outputting completely random results or a NN producing a probability spike at a given value.

For all programs declaring an NN, we generate a large number of outputs and test whether the resulting PDF is normalized. Furthermore, we can take custom tests for neural programs, which test whether the output of a program is what we would expect given a well-trained NN.

## Creating a test case
Create two files with the same name, except for the file extension. One with the ".ppl" file extension and one with ".tst". The ".ppl" contains a program that will be executed for every assertion specified in the ".tst" file.

### Syntax for the PPL file
Create a file with normal DPPL Syntax, containing a function called "main". The main may have additional parameters, which have to be specified in the TST file. This will be the function on which probabilistic inference is performed.

### Syntax of the TST file
The TST file consists of any number of assertions for the probabilistic inference of a PPL file. There are multiple types of assertions, but all of them must be in exactly one line. Make sure that there is no empty line at the end of the file.

Test cases, regardless of type, take Values as inputs. Make sure that the values you pass only use Value syntax and not expression syntax. E.g., Either types can be created using the uppercase "Left" or lowercase "left" syntax in expressions. The first is Value syntax, while the latter is expression syntax and invokes the "left" constructor. In this case, only the uppercase version may be used.

ADTs are currently not supported by the test case parser, because they depend on the ADT declaration in the PPL file.

#### PDF/CDF assertions
These are the most basic types of assertions. They test that the PDF or CDF has an expected value at a given position. The following snippet shows one PDF and one CDF assertion:

```
p(1.5)=(0.5, 1.0)
cdf(1.5)=(0.75, 0.0)
```

The assertions test that the probability density of the main function is 0.5 at the position x=1.5 and has a dimensionality of 1 (density). The cumulative density at position x=1.5 has to be 0.75 with a dimensionality of 0 (mass).

If the main function has parameters, list them, comma-separated, after the sample point, like this:

```
p(1.5, False, [0.2])=(0.5, 1.0)
cdf(1.5, False, [0.2])=(0.75, 0.0)
```
False and [0.2] would be passed as parameters to the main function in both cases.

#### Argmax_p assertions
Especially when dealing with neural networks, testing for exact probability densities becomes infeasible. The argmax_p assertion allows to specify which output should be the most likely. This is done using a MockNN in the interpreter that behaves like a well-trained NN.

The argmax_p assertion works on programs that take a symbol as an input. For this type of testing, we pass a value as a symbol to the MockNN, and it behaves as if it recognized the value it was given. The test syntax looks like this:
```
argmax_p(3)=3
```
The key difference to PDF/CDF testing is that we don't specify a test point. All arguments of the argmax_p assertion are directly passed to the main function. Any neural network that takes a symbol as input behaves as if it recognized the value in its symbol input.

For example, an MNist addition program, that would normally take two images as symbol inputs, could be tested using: ```argmax_p(3, 7)=10``` to test that for an image showing a 3 and an image showing a 7, 10 would be the most likely outcome of the program.