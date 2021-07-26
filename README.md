# FO-prover

This is a first order tautology prover.

To build the program use the Makefile, ie. run
```
make
```
The Makefile uses stack. If you are using old stack version, the build might 
fail. stack 2.5.1 or newer should work.


To check if a first order formula is a tautology, run
```
cat [FILE] | ./FO-prover
```
The program will output `1` if the formula is a tautology, otherwise it will
output `0`.

To see the syntax of formulas accepted by the program, checkout examples in
`tests/A`, `tests/B` and `tests/C`


