#!/usr/bin/env python

# TransForm: Formally Specifying Transistency Models and Synthesizing Enhanced Litmus Tests
# Naorin Hossain, Caroline Trippel, Margaret Martonosi
# ISCA 2020
#
# Copyright (c) 2020 Naorin Hossain
#
# This file is licensed under the GNU General Public License.  See LICENSE for details.

import time
import subprocess

def main():
  tests = {}
 
  fout = open("handwritten_test_comparison_bound10.txt", 'w') # TODO: this should be a path to an output file -- can be anything

  with open("tests.txt", 'r') as fin: # TODO: path to tests.txt
    for line in fin:
      line_array = (line.strip()).split(' ')
      tests[line_array[0]] = line_array[1]

  fin.close()

  for test in tests:
    test_time_start = time.time()
    p = subprocess.Popen(["java", "-classpath", ".:./alloy4.2.jar", # TODO: this should be a path to Alloy
                         "MainClass", "-n", "1",  
                         "-f", "tso_transistency_perturbed_minimality_check.als", test], stdout=subprocess.PIPE) # TODO: this should be a path to the minimality_check.als model
    out, _  = p.communicate()
    test_time_elapsed = time.time() - test_time_start

    fout.write(test + ": ")
    if "<instance" in out:
      fout.write("minimal ")

    else:
      test_time_start = time.time()
      p1 = subprocess.Popen(["java", "-classpath", ".:./alloy4.2.jar", # TODO: this should be a path to Alloy
                           "MainClass", "-n", "1",  
                           "-f", "tso_transistency_perturbed_minimize.als", test], stdout=subprocess.PIPE) # TODO: this should be a path to the minimize.als model
      out1, _  = p1.communicate()
      test_time_elapsed = time.time() - test_time_start

      if "<instance" in out1:
        fout.write("can be minimized ")

      else:
        fout.write("uninteresting or out of bounds ")
       
    fout.write(str(test_time_elapsed) + " sec\n")

  fout.close()

main()
