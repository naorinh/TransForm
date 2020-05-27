# TransForm

TransForm is a framework for formal specification of memory transistency models (MTMs) and automated synthesis of enhanced litmus test (ELT) suites.

## Installation

No installation is needed. The `.als` files can be opened and executed using [Alloy](http://alloy.mit.edu).

## Usage

To use TransForm's synthesis engine, you will need:

* a Java compiler `javac`
* `python` (tested on version 2.7)
* the Alloy 4.2 [.jar file](http://alloy.mit.edu/alloy/downloads/alloy4.2.jar)

Run `make` to build our slightly-customized command-line interface for Alloy that uses the MiniSat solver.  (The particular set of command line flags and options have been changed and generation has been set to run until exhaustion.)

Basic usage:

    ./run.sh <.als input file> <test size bound> <test name>

For example:

    $ ./run.sh tso_transistency_perturbed.als 5 sc_per_loc
      Command match: sc_per_loc
    Scope bound 5 overrides default bound of 4
    # ['./deduplicate.py', '20200525-185124-sc_per_loc-5']
    New hash (1/1) 2020-05-25 18:51:27.673382: _T_WPTEa0_Ia1_Ra1_ptwa0
    New hash (2/2) 2020-05-25 18:51:27.804312: _T_Wa0_Ra0_ptwa1
    New hash (3/3) 2020-05-25 18:51:27.806360: _T_Wa0_ptwa1_Ra0
    New hash (4/4) 2020-05-25 18:51:27.925560: _T_WPTEa0_Ia1_Wa1_ptwa0
    New hash (5/6) 2020-05-25 18:51:28.005904: _T_Ra0_Wa0_ptwa1
    New hash (6/9) 2020-05-25 18:51:28.114794: _T_Ra0_ptwa1_Wa0_ptwa1
    New hash (7/15) 2020-05-25 18:51:28.291084: _T_Wa0_ptwa1_Ra0_ptwa1
    New hash (8/21) 2020-05-25 18:51:28.481840: _T_Ra0_ptwa1_Wa0
    New hash (9/26) 2020-05-25 18:51:28.718248: _T_Wa0_ptwa1_Wa0
    New hash (10/32) 2020-05-25 18:51:28.876608: _T_Wa0_Wa0_ptwa1
    New hash (11/48) 2020-05-25 18:51:29.455400: _T_Wa0_ptwa1_WPTEa1_Ia0
    #,Filename,Command,Unique,Total
    Results,tso_transistency_perturbed.als,sc_per_loc,11,48

    real    0m4.772s
    user    0m15.671s
    sys     0m1.154s


This lists the eleven synthesized tests that are minimal with respect to the x86t_elt axiom sc_per_loc, in no particular order.

In this case, Alloy generated 48 instances, of which 11 were unique post-deduplication.

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
m | Read for a read-modify-write

## Test Comparison

To compare tests that can be synthesized by TransForm against existing tests, we have a script that categorizes inputted tests as:
1. minimal and synthesizable verbatim
2. can be minimized and then synthesized
3. uninteresting or requires a higher bound

The comparison tool uses a default bound of 10 instructions with the x86t_elt model and ELTs from prior work to check if the ELTs from prior work fall into these categories. This bound can be changed in each tso_transistency_perturbed_*.als model in the fact under the `// check if synthesized` comment. ELTs that are compared are listed in the tests.txt file. Using a different set of tests requires adding the tests to each model file and listing them in tests.txt.

Usage:

    $PYTHON test_comparison.py

## Generating Graphs

To generate graphs of synthesized ELTs, the synthesized instances must be outputted to a file:

    java -classpath $ALLOYPATH:$ALLOYPATH/alloy4.2.jar MainClass -f <.als input file> -b <test size bound> <test_name> > <instance_output_file>

Then, the instances found in the outputted file can be parsed to generate graphs as follows:

    $PYTHON generate-graphs-elts.py -i <input file> -o <output file prefix> -g <directory to create graph directory in>

where the input file should be the instance_output_file. A full directory of instance_output_files can also be directly used to generate graphs for all included instance_output_files. To do so, name the directory rather than the input file with the -i flag and follow up with -d:

    $PYTHON generate-graphs-elts.py -i <input directory> -d -g <directory to create graph directory in>

In this case, the output file prefix is not needed as the filenames of files in the input directory will be used as the output file prefixes.

Next, generate PNG images of the graphs:

    $PYTHON generate-images-elts.py -i <input graph directory> -o <output imgs directory>

## Updating Relation Placement Rules and Regression Testing to Compare Synthesized ELTs

The relation placement rules that have been used for the TransForm work (described briefly below) can be modified to make different assumptions about how these relations should be inserted in synthesized ELTs. To compare modified models against prior iterations of a model, we provide a regression test script (test_suite_regression.py) that will output whether the synthesized suites of unique ELTs are identical between model updates or which ELTs are unique to each suite (original vs. modified model).

To use the regression test script:

    $PYTHON test_suite_regression.py -o <original model ELT suite> -n <new model ELT suite>

where the outputted list of unique ELTs from deduplicate.py for each model version is provided as input.

## Current Relation Placement Rules and Assumptions

The following rules are defined in the tso_transistency_perturbed.als file for relations used to define ELTs and MTMs.

* **po**: Relates a user-facing or support instruction to up to one other user-facing or support instruction that follows it in program order on a thread.
* **rf**: Relates writes to reads that they source. This includes 1) user-facing writes that source user-facing reads accessing the same PA, and 2) PTE writes and dirty bit updates that update PTEs that are accessed by PT walks.
* **co**: Relates writes to the same PA in a coherence order. This includes 1) user-facing writes accessing the same PA, and 2) PTE writes and dirty bit updates that write to the same PTE.
* **fr**: Relates reads to co-successors of writes that they are sourced from. This includes 1) user-facing writes that are co-successors of user-facing writes that source user-facing reads accessing the same PA, and 2) PTE writes and dirty bit updates that are co-successors of the PTE write or dirty bit update that updates the PTE that is accessed by a PT walk.
* **ghost**: Relates user-facing instructions to invoked ghost instructions. Each ghost instruction is related to one user-facing instruction by ghost but multiple ghost isntructions can be related to the same user-facing instruction.
* **rf_ptw**: Relates PT walks to user-facing instructions that access the TLB entry loaded by the PT walk. The TLB entry can be accessed by multiple user-facing instructions so rf_ptw can relate one PT walk to multiple user-facing instructions.
* **rf_pa**: Relates PTE writes to user-facing instructions that access a PA based on the address mapping written by the PTE write. By extension, the PT walk that a user-facing instruction is related to by rf_ptw must come after the PTE write in **^com** (where ^ is the transitive closure and com is the set of rf + co + fr relations) and there must be no intervening PTE write between them in ^com. This ensures that a user-facing instruction related to a PTE write by rf_pa accesses a TLB entry reflecting the address mapping written by the same PTE write.
* **co_pa**: Relates PTE writes that map virtual addresses (VAs) to the same physical address (PA) in a total order.
* **fr_pa**: Relates user-facing instructions to PTE writes that are co_pa-successors of the PTE write that sources the address mapping that is accessed by the user-facing instruction in the TLB.
* **fr_va**: Relates a user-facing instruction to a PTE write that changes the address mapping of the VA accessed by the user-facing instruction to a different PA. By extension, the PT walk that the user-facing instruction is related to by rf_ptw must come before the PTE write in ^com so that it accesses a previous address mapping stored in the PTE.
* **remap**: Relates PTE writes to INVLPGs that they invoke to invalidate stale address mappings in TLBs on each core. The INVLPG invoked on the same thread as the PTE write follows immediately after the PTE write in **po**.

## Questions?

Please contact Naorin Hossain at nhossain@princeton.edu.

## Disclaimer

Several files (deduplicate.py, tso_transistency_perturbed\*.als) have been adapted from [prior work](https://github.com/NVlabs/litmustestgen) on automated litmus test suite synthesis by Daniel Lustig, Andy Wright, Alexandros Papakonstantinou, and Olivier Giroux. We have left much of the deduplication script (adapted from canon.py in prior work) in tact so that other memory models explored in this prior work can easily be used and extended with TransForm to define their transistency models and synthesize their respective ELT suites. See NVIDIA LICENSE for details on the BSD-3 license that the corresponding files from prior work are licensed under.