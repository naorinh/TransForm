#!/usr/bin/env python

# TransForm: Formally Specifying Transistency Models and Synthesizing Enhanced Litmus Tests
# Naorin Hossain, Caroline Trippel, Margaret Martonosi
# ISCA 2020
#
# Copyright (c) 2020 Naorin Hossain
#
# This file is licensed under the GNU General Public License.  See LICENSE for details.

import subprocess
import re
import sys
import os
import getopt
import xml.etree.ElementTree as ET

Event = {}
Edge = {}
po = {}
ghost = {}
thread = []
num_inst = {}
pte = {}
addr_map = {}
address = {}
atoms = {}

class Atom:
  def __init__(self, label, sig_label):
    self._label = label
    self._sig_label = sig_label
  def __repr__(self):
    "just list all the properties"
    d = {}
    for a in dir(self): # guaranteed to be alphabetical
      if a[:2] != "__":
        d[a] = getattr(self, a)
    return str(d)

def follow_edge(atom, edge):
  "Return atom.edge.  There should only be one choice"
  candidates = []
  if not hasattr(atom, edge):
    return None
  for c in getattr(atom, edge):
    candidates.append(c)
  if len(candidates) != 1:
    if edge == "ghost":
      return candidates
    raise Exception("multiple %s edges?" % edge)
  return [candidates[0]]

def follow_edge_tr(atoms, atom, edge):
  "like follow_edge, but for transitively closed relations"
  candidates = []
  if not hasattr(atom, edge):
    return None
  # first, add all adjacent atoms
  for c in getattr(atom, edge):
    candidates.append(c)
  # now, prune out all atoms which are at least two steps away
  for c1 in getattr(atom, edge):
    a1 = atoms[c1]
    if hasattr(a1, edge):
      for c2 in getattr(a1, edge):
        if c2 in candidates:
          candidates.remove(c2)
  # there should only be one candidate lett
  if len(candidates) != 1:
    raise Exception("multiple %s edges?" % edge)
  return candidates[0]

def follow_po_edge(atoms, atom):
  "like follow_edge, but for po or sb specifically"
  x = follow_edge(atom, "po")
  if x:
    return x
  x = follow_edge_tr(atoms, atom, "sb")
  if x:
    return x
  return None

def printHeader(fout):
  # Print header
  fout.write("digraph G {\n")
  fout.write("\tlayout=neato;\n")
  fout.write("\toverlap=scale;\n")
  fout.write("\tsplines=true;\n")

def createEvents(fout):
  # Event labels
  # E.g., n3_0_label [label="Read x 1\n";pos="5,0.5!";shape=oval];

  inst_id = 0
  intra_inst_id = 0
  row_idx = 1
  for thd_id in range(len(thread)):
    first_inst = thread[thd_id]

    (Event[first_inst])[0] = inst_id
    (Event[first_inst])[1] = thd_id
    (Event[first_inst])[2] = row_idx

    fout.write("\tn" + str(inst_id) + "_0_label [label=\"")

    fout.write(first_inst + "_" + str(intra_inst_id))

    if first_inst in address:
      fout.write(" " + address[first_inst])
    if address[first_inst] in pte:
      fout.write(": " + addr_map[pte[address[first_inst]]])
    fout.write("\\n\";pos=\"" + str(thd_id*3) + "," + str(row_idx) + "!\";shape=oval];\n")

    # ghost instructions will be placed below user-facing instructions that invoke them
    if first_inst in ghost:
      for inst in ghost[first_inst]:
        inst_id += 1
        row_idx -= 1
        num_inst[first_inst] += 1
        
        (Event[inst])[0] = inst_id
        (Event[inst])[1] = thd_id
        (Event[inst])[2] = row_idx

        fout.write("\tn" + str(inst_id) + "_0_label [label=\"")

        fout.write(inst + "_" + str(intra_inst_id))

        fout.write(" " + address[inst])
        if address[inst] in pte:
          fout.write(": " + addr_map[pte[address[inst]]])

        fout.write("\\n\";pos=\"" + str(thd_id*3) + "," + str(row_idx) + "!\";shape=oval];\n")



    inst_id += 1
    intra_inst_id += 1
    row_idx -= 1

    curr_inst = first_inst
    while curr_inst in po:
      num_inst[first_inst] += 1
      curr_inst = po[curr_inst]

      (Event[curr_inst])[0] = inst_id
      (Event[curr_inst])[1] = thd_id
      (Event[curr_inst])[2] = row_idx

      fout.write("\tn" + str(inst_id) + "_0_label [label=\"")
      
      fout.write(curr_inst + "_" + str(intra_inst_id))

      if curr_inst in address:
        fout.write(" " + address[curr_inst])
      if address[curr_inst] in pte:
          fout.write(": " + addr_map[pte[address[curr_inst]]])

      fout.write("\\n\";pos=\"" + str(thd_id*3) + "," + str(row_idx) + "!\";shape=oval];\n")

      if curr_inst in ghost:
        for inst in ghost[curr_inst]:
          inst_id += 1
          row_idx -= 1
          num_inst[first_inst] += 1
          
          (Event[inst])[0] = inst_id
          (Event[inst])[1] = thd_id
          (Event[inst])[2] = row_idx

          fout.write("\tn" + str(inst_id) + "_0_label [label=\"")

          fout.write(inst + "_" + str(intra_inst_id))

          fout.write(" " + address[inst])
          if address[inst] in pte:
            fout.write(": " + addr_map[pte[address[inst]]])

          fout.write("\\n\";pos=\"" + str(thd_id*3) + "," + str(row_idx) + "!\";shape=oval];\n")
      


      inst_id += 1
      intra_inst_id += 1
      row_idx -= 1

    row_idx = 1

def createEdges(fout):
  # Create edges
  # E.g., n2_0_label -> n4_0_label [label="rf";constraint=false;color="red";fontcolor="red";];
  colors = { "po"                           : "black",
             "rf"                           : "red",
             "co"                           : "blue",
             "fr"                           : "orange",
             "rf_ptw"                       : "purple",
             "remap"	                      : "brown",
             "rf_pa"                        : "turquoise4",
             "co_pa"                        : "cyan4",
             "fr_pa"                        : "lightseagreen",
             "fr_va"                        : "darkturquoise",
             "default"                      : "black",
             "rmw"                          : "forestgreen",
             "dep"                          : "limegreen",
           }

  for edge_set in Edge:
    for edge in Edge[edge_set]:
      edge_array = edge.split("->")

      event0 = edge_array[0]
      inst_id0_str = str((Event[event0])[0])

      event1 = edge_array[1]
      inst_id1_str = str((Event[event1])[0])

      if edge_set in colors:
        color = colors[edge_set]
      else:
        color = colors["default"]

      fout.write("\tn" + inst_id0_str + "_0_label" + " -> n"  + inst_id1_str + "_0_label" + "[label=\"" + edge_set + "\";constraint=false;color=\"" + color + "\";fontcolor=\"" + color + "\";];\n")

# Print footer
def printFooter(fout):
  fout.write("}\n")

def createSets(atom):
  global Edge
  global po
  global ghost
  global thread
  global num_inst
  global pte
  global addr_map
  global address

  # add attributes of instructions like edges to appropriate sets

  if hasattr(atom, "po"):
    if "po" in Edge.keys():
      Edge["po"].append(str(atom._label + "->" + getattr(atom, "po")[0]))
    else:
      Edge["po"] = [str(atom._label + "->" + getattr(atom, "po")[0])]
    po[atom._label] = getattr(atom, "po")[0]

  if hasattr(atom, "rf"):
    for dst in getattr(atom, "rf"):
      if "rf" in Edge.keys():
        Edge["rf"].append(str(atom._label + "->" + dst))
      else:
        Edge["rf"] = [str(atom._label + "->" + dst)]

  if hasattr(atom, "co"):
    for dst in getattr(atom, "co"):
      if "co" in Edge.keys():
        Edge["co"].append(str(atom._label + "->" + dst))
      else:
        Edge["co"] = [str(atom._label + "->" + dst)]

  if hasattr(atom, "fr_set"):
    for dst in getattr(atom, "fr_set"):
      if "fr" in Edge.keys():
        Edge["fr"].append(str(atom._label + "->" + dst))
      else:
        Edge["fr"] = [str(atom._label + "->" + dst)]

  if hasattr(atom, "rf_ptw"):
    for dst in getattr(atom, "rf_ptw"):
      if "rf_ptw" in Edge.keys():
        Edge["rf_ptw"].append(str(atom._label + "->" + dst))
      else:
        Edge["rf_ptw"] = [str(atom._label + "->" + dst)]

  if hasattr(atom, "remap"):
    for dst in getattr(atom, "remap"):
      if "remap" in Edge.keys():
        Edge["remap"].append(str(atom._label + "->" + dst))
      else:
        Edge["remap"] = [str(atom._label + "->" + dst)]

  if hasattr(atom, "r_rf_pa"):
    for dst in getattr(atom, "r_rf_pa"):
      if "rf_pa" in Edge.keys():
        Edge["rf_pa"].append(str(atom._label + "->" + dst))
      else:
        Edge["rf_pa"] = [str(atom._label + "->" + dst)]

  if hasattr(atom, "w_rf_pa"):
    for dst in getattr(atom, "w_rf_pa"):
      if "rf_pa" in Edge.keys():
        Edge["rf_pa"].append(str(atom._label + "->" + dst))
      else:
        Edge["rf_pa"] = [str(atom._label + "->" + dst)]

  if hasattr(atom, "co_pa"):
    for dst in getattr(atom, "co_pa"):
      if "co_pa" in Edge.keys():
        Edge["co_pa"].append(str(atom._label + "->" + dst))
      else:
        Edge["co_pa"] = [str(atom._label + "->" + dst)]

  if hasattr(atom, "r_fr_pa"):
    for dst in getattr(atom, "r_fr_pa"):
      if "fr_pa" in Edge.keys():
        Edge["fr_pa"].append(str(atom._label + "->" + dst))
      else:
        Edge["fr_pa"] = [str(atom._label + "->" + dst)]

  if hasattr(atom, "w_fr_pa"):
    for dst in getattr(atom, "w_fr_pa"):
      if "fr_pa" in Edge.keys():
        Edge["fr_pa"].append(str(atom._label + "->" + dst))
      else:
        Edge["fr_pa"] = [str(atom._label + "->" + dst)]

  if hasattr(atom, "r_fr_va_set"):
    for dst in getattr(atom, "r_fr_va_set"):
      if "fr_va" in Edge.keys():
        Edge["fr_va"].append(str(atom._label + "->" + dst))
      else:
        Edge["fr_va"] = [str(atom._label + "->" + dst)]

  if hasattr(atom, "w_fr_va_set"):
    for dst in getattr(atom, "w_fr_va_set"):
      if "fr_va" in Edge.keys():
        Edge["fr_va"].append(str(atom._label + "->" + dst))
      else:
        Edge["fr_va"] = [str(atom._label + "->" + dst)]

  if hasattr(atom, "rmw"):
    if "rmw" in Edge.keys():
      Edge["rmw"].append(str(atom._label + "->" + getattr(atom, "rmw")[0]))
    else:
      Edge["rmw"] = [str(atom._label + "->" + getattr(atom, "rmw")[0])]

  if hasattr(atom, "dep"):
    if "dep" in Edge.keys():
      Edge["dep"].append(str(atom._label + "->" + getattr(atom, "dep")[0]))
    else:
      Edge["dep"] = [str(atom._label + "->" + getattr(atom, "dep")[0])]

  if hasattr(atom, "ghost"):
    for dst in getattr(atom, "ghost"):
      if not atom._label in ghost.keys():
        ghost[atom._label] = []
      ghost[atom._label].append(dst)

  if (atom._sig_label == "Read" or atom._sig_label == "Write" or atom._sig_label == "ptwalk" or atom._sig_label == "dirtybit" or atom._sig_label == "MFENCE" or atom._sig_label == "INVLPG"):
    thread.append(atom._label)
    Event[atom._label] = [-1, -1, -1]

  if (hasattr(atom, "address") or hasattr(atom, "page")):
    addr = ""
    if hasattr(atom, "address"):
      addr = getattr(atom, "address")[0]
      if hasattr(atoms[addr], "pte"):
        pte[re.sub("VirtualAddress", "VA", addr)] = getattr(atoms[addr], "pte")[0]
        addr_map[getattr(atoms[addr], "pte")[0]] = re.sub("VirtualAddress", "VA", getattr(atoms[getattr(atoms[addr], "pte")[0]], "map")[0])
    else:
      addr = getattr(atom, "page")[0]
    addr = re.sub("VirtualAddress", "VA", addr)
    address[atom._label] = addr

def parse(instance):
  global Edge
  global po
  global ghost
  global thread
  global num_inst
  global pte
  global addr_map
  global address
  global atoms
  atoms = {}

  # Parse the Alloy XML dump

  # first, parse all the sigs in the instance
  for sig in instance.findall("sig"):
    sig_label = re.sub(".*/", "", sig.attrib["label"])
    # parse all the atoms which are members of this sig
    for atom in sig.findall("atom"):
      label = re.sub("\$", "", re.sub(".*/", "", atom.attrib["label"]))
      atoms[label] = Atom(label, sig_label)

  # parse all the relations in the instance
  for field in instance.findall("field"):
    field_label = re.sub(".*/", "", field.attrib["label"])
    # parse each individual edge in the relation
    for tup in field.findall("tuple"):
      # parse the atoms in each edge.  there should be two: a source and a
      # destination
      tuple_atoms = []
      for atom in tup.findall("atom"):
        tuple_atoms.append(re.sub("\$", "", re.sub(".*/", "", atom.attrib["label"])))
      if len(tuple_atoms) == 2:
        src = tuple_atoms[0]
        dst = tuple_atoms[1]
        if hasattr(atoms[src], field_label):
          val = getattr(atoms[src], field_label)
        else:
          val = []
        val.append(dst)
        setattr(atoms[src], field_label, val)
      else:
        raise Exception("illegal tuple arity")

  return atoms

def parseFile(infile):
  instance_text = ""
  global Edge
  global po
  global ghost
  global thread
  global num_inst
  global pte
  global addr_map
  global address
  global atoms
  global index

  with open(infile, 'r') as fin:
    for line in fin:

      if line == "": #EOF
        break

      # pre-parse the XML to search for individual instances of the latest command
      if "<instance" in line:
        instance_text = ""
      instance_text += line
      if "</instance" in line:
        # we've reached the end of an instance, so parse this instance
        atoms = parse(ET.fromstring(instance_text))

        for t in atoms.iteritems():
          if t[0][:6] == "Thread":
            # iterate through the events in the thread, and add relations for each event
            s = follow_edge(t[1], "start")
            while s is not None:
              a = atoms[s[0]]
              createSets(a)
              g = follow_edge(a, "ghost")
              if g is not None:
                if len(g) == 1:
                  b = atoms[g[0]]
                  createSets(b)
                else:
                  for gx in g:
                    b = atoms[gx]
                    createSets(b)
              s = follow_po_edge(atoms, a)

        # remove all but first instruction on a thread from thread array
        removal = []
        for event in thread:
          if event in po:
            removal.append(po[event])
          if event in ghost:
            for ghostinstr in ghost[event]:
              removal.append(ghostinstr)

        for event in removal:
          thread.remove(event)

        for event in thread:
          num_inst[event] = 1

        fout = open(graphdir + "/" + ofile_prefix + '-' + str(index) + '.gv', 'w')

        # write to .gv file
        printHeader(fout)
        createEvents(fout)
        createEdges(fout)
        printFooter(fout)

        fout.close()
        
        Event = {}
        Edge = {}
        po = {}
        ghost = {}
        thread = []
        num_inst = {}
        pte = {}
        addr_map = {}
        address = {}
        atoms = {}

        index += 1
  fin.close()

def main(argv):
  global Event
  global Edge
  global po
  global ghost
  global thread
  global num_inst
  global pte
  global addr_map
  global address
  global atoms
  global graphdir
  global ofile_prefix
  global index

  Event = {}
  Edge = {}
  po = {}
  ghost = {}
  thread = []
  num_inst = {}
  pte = {}
  addr_map = {}
  address = {}
  atoms = {}

  index = 0;

  infile = ""
  ofile_prefix = ""
  indir = False
  graphdir = "."

  usage_string = "\nusage: \t generate-graphs-elts.py [arguments] \
                 \n\nDescription: \tConvert Alloy output file into ELT graphs (.gv files). \
                 \n\nArguments: \
                 \n\t-h or --help \t\t\t\t Display this help and exit \
                 \n\t-i or --input <Alloy_outfile> \t\t File containing TransForm-synthesized RMF output \
                 \n\t-d or --directory \t\t Indicates input is a directory \
                 \n\t-o or --output <graph_prefix> \t\t Prefix for output graph files \
                 \n\t-g or --graphs <graph_dir> \t\t Directory for outputs graph files; default is current directory";

  try:
    opts, args = getopt.getopt(argv,"hi:do:g:",["help","input","directory","output","graphs"]);

  except getopt.GetoptError:
    print usage_string;
    sys.exit(1)

  for opt, arg in opts:
    if opt in ("-h", "--help"):
      print usage_string;
      sys.exit()

    elif opt in ("-i", "--input"):
      infile = arg

    elif opt in ("-d", "--directory"):
      indir = True    

    elif opt in ("-o", "--output"):
      ofile_prefix = arg

    elif opt in ("-g", "--graphs"):
      graphdir = arg

  if not (os.path.isfile(os.path.expanduser(infile)) or os.path.isdir(os.path.expanduser(infile))):
    print "ERROR: select a valid Alloy input file"
    print usage_string;
    sys.exit(1)

  if not os.path.isdir(os.path.expanduser(graphdir)):
    print "ERROR: invalid graph output directory"
    print usage_string;
    sys.exit(1)

  graphdir += "/graphs"
  if not (os.path.exists(graphdir) and os.path.isdir(graphdir)):
    os.makedirs(graphdir);

  if indir:
    for file in os.listdir(infile):
      print file
      ofile_prefix = re.sub(".*/", "", re.sub("\..*", "", file))
      index = 0
      parseFile(infile + "/" + file)
  else:
    print infile
    ofile_prefix = re.sub(".*/", "", re.sub("\..*", "", infile))
    parseFile(infile)

  return

if __name__ == "__main__":
   main(sys.argv[1:])
