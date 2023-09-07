# Spyro[SMT] OOPSLA 2023 Artifact

This is the artifact for paper #481 "Synthesizing Specifications". 

spyro synthesizes provably sound, most-precise specifications from given function definitions.


## Claims

### Claims supported by this artifact

The artifact supports the following claims:

1. Spyro[SMT] can synthesize best L-properties for 6/10 benchmark problems, and guarantee those 6 are best L-conjunction.

2. The Algorithm 1 with line 12 is faster than the Algorithm 1 without line 12.


### Claims not supported by this artifact

This artifact may not support some claims of the paper. Specifically,

1. The running time and number of SMT calls may be different to Table 1 or Table 2.

2. Each conjunct synthesized by Spyro[SMT] may be different to the Fig. 3, while the L-conjunctions are equivalent.

#### Reason

All the evaluation data of paper (including Table 1, 2 and Fig. 3) were generated from Apple M1 8-core CPU with 8GB RAM.
SMT / SyGuS tools compiled for different architecture / OS may produce different results.
Spyro[SMT] has a high variance in running time. To obtain reliable results, it is recommended to execute it with a minimum of three random seeds.

## Setup

### Requirements

The artifact requires dependencies if you try to run on your local machine

* python (version >= 3.6), including packages:
    * cvc5
    * z3-solver
    * numpy (only for `run_benchmarks.py`)


## Structure of this artifact

* `benchmarks` contains all the Spyro[SMT] benchmarks.

* `results` contains the result of execution.



## Running the evaluation

### Running Spyro[SMT] for single example

To run spyro on default setting, run `python3 spyro.py <PATH-TO-INPUT-FILE>`.
This will synthesize minimized properties from input file, and print the result to `stdout`.

### Flags

* `infile`: Input file. Default is `stdin`
* `outfile`: Output file. Default is `stdout`
* `-v, --verbose`: Print descriptive messages, and leave all the temporary files.
* `--keep-neg-may`: Disable freezing negative examples.
* `--inline-bnd`: Number of inlining/unrolling. Default is 5.


### Understanding Spyro[SMT] input

Each input to Spyro[SMT] must contain `target_fun`, `declare-language` and `declare-semantics`.


#### Function definition

Each input file must include one or more `target-fun` definitions. 
Input and output variables must have different identifiers, even if the they are defined in different functions,

```
(target-fun max2 
    ((x1 Int) (x2 Int))     ;; Input variables
    (o Int)                 ;; Output variable
    (ite (<= x2 x1) x1 x2)  ;; Function term
)
```

#### Grammar definition (i.e. search space)

The search space is defined as a context-free grammar. 
ㅅThe first parenthesis lists nonterminals, and the nonterminal at the beginning is treated as the start symbol. The second parenthesis defines production rules for each nonterminal.
For example, the nonterminal `B` can produce `$t`, `$or_1 AP`, `$or_2 AP AP` or `$or_3 AP AP AP`.

```
(declare-language
    
    ;; Nonterminals
    ((B Bool) (AP Bool) (I Int))

    ;; Syntax
    ((($t) ($or_1 AP) ($or_2 AP AP) ($or_3 AP AP AP))
     (($eq I I) ($le I I) ($ge I I) ($lt I I) ($gt I I) ($neq I I))
     (($x1) ($x2) ($o)))
)
```



#### Semantics definition

The semantics of grammar must be provided explicitly, in form of `(nonterminal) (syntactic rule) (interpretation)`.
Currently, Spyro[SMT] only supports LIA and Boolean operations of SMT-LIB.

```
(declare-semantics 
    (B ($t) true)
    (B ($or_1 apt1) apt1)
    (B ($or_2 apt1 apt2) (or apt1 apt2))
    (B ($or_3 apt1 apt2 apt3) (or apt1 apt2 apt3))

    (AP ($eq it1 it2) (= it1 it2))
    (AP ($le it1 it2) (<= it1 it2))
    (AP ($ge it1 it2) (>= it1 it2))
    (AP ($lt it1 it2) (< it1 it2))
    (AP ($gt it1 it2) (> it1 it2))
    (AP ($neq it1 it2) (distinct it1 it2))

    (I ($x1) x1)
    (I ($x2) x2)
    (I ($o) o)
)
```

### Understanding Spyro[SMT] output

The synthesize properties are given as a function that returns a Boolean value.

For example, the following is synthesized properties of `sygus/max2.sp`:

```
Property 0

(lambda ((x1 Int) (x2 Int) (o Int)) (or (< x2 x1) (= x2 o)))

Property 1

(lambda ((x1 Int) (x2 Int) (o Int)) (or (< x1 x2) (= x1 o)))
```

The property 0 means
$$(x_2 < x_1) \vee (x_2 = o)$$
must be true.

The property 1 means
$$(x_1 < x_2) \vee (x_1 = o)$$
must be true.

### Running Spyro[SMT] for benchmark set

Command `python3 run_benchmarks.py -a` will run Spyro[SMT] for every benchmark problem with three differents random seeds `[32, 64, 128]`. Running `python3 run_benchmarks.py -a` will take about 3 hours.

This will generate files containing synthesized properties and CSV files containing statistics in the `results` directory. For example, `smt_default_32.csv` contains statistics for seed 32, and `smt_nofreeze_128.csv` contains statistics for seed 128, executed without freezing negative examples.
It also creates files with suffix `_median`, which has median running time among three runs.

`python3 run_benchmarks_median.py` does the same to `python3 run_benchmarks.py`, but only run each benchmark problem with single random seed value, which generated the median value on our local machine. The output file of `run_benchmarks_median.py` will have suffix `_median`. Running `python run_benchmarks_median.py -a` will take about 1 hour. 
