#!/usr/bin/env python

# TransForm: Formally Specifying Transistency Models and Synthesizing Enhanced Litmus Tests
# Naorin Hossain, Caroline Trippel, Margaret Martonosi
# ISCA 2020
#
# Copyright (c) 2020 Naorin Hossain
#
# This file is licensed under the GNU General Public License.  See LICENSE for details.

import sys
import re
import getopt
import os

if __name__ == '__main__':

    original_file = ""
    new_file = ""

    usage_string = "\nusage: \t test_suite_regression.py [arguments] \
                    \n\nDescription: \tRegression testing on updated iterations of ELT suite synthesis. \
                    \n\nArguments: \
                    \n\t-h or --help \t\t\t\t Display this help and exit \
                    \n\t-o or --original <original_outputfile> \t\t File containing original TransForm-synthesized ELT suites \
                    \n\t-n or --new <new_outputfile> \t\t File containing new TransForm-synthesized ELT suites";

    try:
        opts, args = getopt.getopt(sys.argv[1:],"ho:n:",["help","original","new"]);

    except getopt.GetoptError:
        print usage_string;
        sys.exit(1)

    for opt, arg in opts:
        if opt in ("-h", "--help"):
          print usage_string;
          sys.exit()

        elif opt in ("-o", "--original"):
          original_file = arg 

        elif opt in ("-n", "--new"):
          new_file = arg

    if not os.path.isfile(os.path.expanduser(original_file)):
        print "ERROR: select a valid original output file"
        print usage_string;
        sys.exit(1)

    if not os.path.isfile(os.path.expanduser(new_file)):
        print "ERROR: select a valid new output file"
        print usage_string;
        sys.exit(1)

    original_tests = []
    new_tests = []

    unique_to_original = []
    unique_to_new = []
        
    with open(original_file, 'r') as file_object:
        line = file_object.readline()
        while line:
            if "New hash" in line:
                test_hash = re.search("New\shash\s\([0-9]+/[0-9]+\)\s[0-9]+-[0-9]+-[0-9]+\s[0-9]+:[0-9]+:[0-9]+\.?[0-9]+?:\s(.*)$", line)
                if test_hash:
                    test = test_hash.group(1)
                    original_tests.append(test)
            line = file_object.readline()
        file_object.close()

    with open(new_file, 'r') as file_object:
        line = file_object.readline()
        while line:
            if "New hash" in line:
                test_hash = re.search("New\shash\s\([0-9]+/[0-9]+\)\s[0-9]+-[0-9]+-[0-9]+\s[0-9]+:[0-9]+:[0-9]+\.?[0-9]+?:\s(.*)$", line)
                if test_hash:
                    test = test_hash.group(1)
                    new_tests.append(test)
            line = file_object.readline()
        file_object.close()

    original_tests.sort()
    new_tests.sort()

    if original_tests == new_tests:
        print "Test suites identical."

    else:
        print "Tests in original, not new:"
        print list(set(original_tests) - set(new_tests))

        print "Tests in new, not original:"
        print list(set(new_tests) - set(original_tests))