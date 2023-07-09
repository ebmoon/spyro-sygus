# Spyro[SMT] OOPSLA 2023 Artifact

This is the artifact for paper #481 "Synthesizing Specifications". 

spyro synthesizes provably sound, most-precise specifications from given function definitions.


## Claims

The artifact supports the following claims:

1. Spyro[SMT] can synthesize best L-properties for 6/10 benchmark problems

2. Properties synthesized by Spyro[SMT] are equivalent to the properties in Fig. 3.

3. Relative running time for each benchmark ratio to the numbers of Table 1.


## Setup

### Requirements

The artifact requires dependencies if you try to run on your local machine

* python (version >= 3.6), including packages:
    * cvc5
    * z3

## Running the evaluation

To run spyro on default setting, run `python spyro.py <PATH-TO-INPUT-FILE>`.
This will synthesize minimized properties from input file, and print the result to `stdout`.


## Running Spyro[SMT] for other examples

### Flags

* `infile`: Input file. Default is `stdin`
* `outfile`: Output file. Default is `stdout`
* `-v, --verbose`: Print descriptive messages, and leave all the temporary files.
* `--keep-neg-may`: Disable freezing negative examples.
* `--inline-bnd`: Number of inlining/unrolling. Default is 5.