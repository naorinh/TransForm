# TransForm

TransForm is a framework for formal specification of transistency models and automated synthesis of enhanced litmus test (ELT) suites.

## Installation

No installation is needed. The `.als` files can be opened and executed using [Alloy](http://alloy.mit.edu).

## Usage

To use the canonicalizer script, you will need:

* a Java compiler `javac`
* `python` (tested on version 2.7)
* the Alloy 4.2 [.jar file](http://alloy.mit.edu/alloy/downloads/alloy4.2.jar)

Run `make` to build our ever-so-slightly-customized command-line interface for Alloy.  (The particular set of command line flags have been changed and generation has been set to run until exhaustion.)

Basic usage:

    ./run.sh <.als input file> -m <test size bound> <test name>

For example:

    $ ./run.sh tso_transistency_perturbed.als -m 6 sc_per_loc
      Command match: sc_per_loc
    Scope bound 6 overrides default bound of 4
    # ['./canon.py', '20191123-175237-sc_per_loc-6']
    New hash (1/1): _T_Wa0_Ra0_ptwa1
    New hash (2/2): _T_WPTEa0_Ia1_Ra1_ptwa0
    New hash (3/3): _T_WPTEa0_Ia1_Wa1_ptwa0
    New hash (4/46): _T_Ra0_Wa0_ptwa1
    New hash (5/48): _T_Ra0_ptwa1_Wa0_ptwa1
    New hash (6/75): _T_Wa0_ptwa1_Ra0_ptwa1
    New hash (7/92): _T_Wa0_ptwa1_Ra0
    New hash (8/94): _T_Ra0_ptwa1_Wa0
    #,Filename,Command,Unique,Total
    Results,tso_transistency_perturbed.als,sc_per_loc,8,222

    real    0m17.866s
    user    0m25.364s
    sys     0m1.185s

This lists eight tests that are minimal with respect to the TSO sc_per_loc axiom, in no particular order.

In this case, Alloy generated 222 hashes, of which 8 were unique post-canonicalization.

The hashes themselves are composed of the following:

Hash item | Meaning
----------|--------
T | start of thread
R | Read
W | Write
ptw | ptwalk
F | MFENCE
I | INVLPG
a*n* | Address *n*
m | Read half of a read-modify-write

## Test Comparison

To compare tests that can be synthesized by TransForm against existing tests, we have a script that categorizes inputted tests as:
1. minimal and synthesizable as-is
2. can be minimized and then synthesized
3. always permitted but can be synthesized as subset of larger test

The comparison tool uses a default bound of 10 instructions to check if tests fall into these categories. If not, they require a higher bound. This bound can be changed in each tso_transistency_perturbed_*.als model in the fact under the `// check if synthesized` comment.

Usage:

    python test_comparison.py

## Questions?

Please contact Naorin Hossain at nhossain@princeton.edu.

## Disclaimer

Most files (canon.py, MainClass.java, run.sh, tso_transistency_perturbed.als + all variants) have been derived from [prior work](https://github.com/NVlabs/litmustestgen) on automated litmus test suite synthesis by Daniel Lustig, Andy Wright, Alexandros Papakonstantinou, and Olivier Giroux. We have left much of the structure of the tool in tact so that memory models explored in this prior work can easily be used and extended with TransForm to define their transistency models and synthesize their respective ELT suites.