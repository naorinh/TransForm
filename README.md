# TransForm

TransForm is a framework for formal specification of memory transistency models and automated synthesis of enhanced litmus test (ELT) suites.

## Installation

No installation is needed. The `.als` files can be opened and executed using [Alloy](http://alloy.mit.edu).

## Usage

To use TransForm's synthesis engine, you will need:

* a Java compiler `javac`
* `python` (tested on version 2.7)
* the Alloy 4.2 [.jar file](http://alloy.mit.edu/alloy/downloads/alloy4.2.jar)

Run `make` to build our slightly-customized command-line interface for Alloy that uses the MiniSat solver.  (The particular set of command line flags have been changed and generation has been set to run until exhaustion.)

Basic usage:

    ./run.sh <.als input file> <test size bound> <test name>

For example:

    $ ./run.sh tso_transistency_perturbed.als 5 sc_per_loc
      Command match: sc_per_loc
    Scope bound 5 overrides default bound of 4
    # ['./deduplicate.py', '20200507-145546-sc_per_loc-5']
    New hash (1/1) 2020-05-07 14:55:48.092927: _T_WPTEa0_Ia1_Ra1_ptwa0
    New hash (2/2) 2020-05-07 14:55:48.153009: _T_Ra0_Wa0_ptwa1
    New hash (3/3) 2020-05-07 14:55:48.160712: _T_WPTEa0_Ia1_Wa1_ptwa0
    New hash (4/4) 2020-05-07 14:55:48.215382: _T_Wa0_Ra0_ptwa1
    New hash (5/6) 2020-05-07 14:55:48.289100: _T_Ra0_ptwa1_Wa0_ptwa1
    New hash (6/9) 2020-05-07 14:55:48.381116: _T_Ra0_ptwa1_Wa0
    New hash (7/10) 2020-05-07 14:55:48.435337: _T_Wa0_ptwa1_Ra0
    New hash (8/20) 2020-05-07 14:55:48.883320: _T_Wa0_ptwa1_Ra0_ptwa1
    New hash (9/38) 2020-05-07 14:55:49.694108: _T_Wa0_ptwa1_Wa0
    New hash (10/39) 2020-05-07 14:55:49.699325: _T_Wa0_Wa0_ptwa1
    #,Filename,Command,Unique,Total
    Results,tso_transistency_perturbed.als,sc_per_loc,10,214

    real    0m7.093s
    user    0m23.045s
    sys     0m1.652s


This lists ten tests that are minimal with respect to the x86t_elt axiom sc_per_loc, in no particular order.

In this case, Alloy generated 214 instances, of which 10 were unique post-deduplication.

The hashes themselves are composed of the following:

Hash item | Meaning
----------|--------
T | start of thread
R | Read
W | Write
WPTE | PTE Write
ptw | ptwalk
F | MFENCE
I | INVLPG
a*n* | Address *n*
m | Read from a read-modify-write

## Test Comparison

To compare tests that can be synthesized by TransForm against existing tests, we have a script that categorizes inputted tests as:
1. minimal and synthesizable verbatim
2. can be minimized and then synthesized
3. uninteresting or requires a higher bound

The comparison tool uses a default bound of 9 instructions with the x86t_elt model and ELTs from prior work to check if the ELTs from prior work fall into these categories. This bound can be changed in each tso_transistency_perturbed_*.als model in the fact under the `// check if synthesized` comment. ELTs that are compared are listed in the tests.txt file. Using a different set of tests requires adding the tests to each model file and listing them in tests.txt.

Usage:

    $PYTHON test_comparison.py

## Questions?

Please contact Naorin Hossain at nhossain@princeton.edu.

## Disclaimer

Several files (deduplicate.py, run.sh, tso_transistency_perturbed.als) have been built off of [prior work](https://github.com/NVlabs/litmustestgen) on automated litmus test suite synthesis by Daniel Lustig, Andy Wright, Alexandros Papakonstantinou, and Olivier Giroux. We have left much of the deduplication script in tact so that other memory models explored in this prior work can easily be used and extended with TransForm to define their transistency models and synthesize their respective ELT suites.