### Title: PDP-8 Instruction Set Simulator
### Date: March 24th, 2015
### Author: Elizabeth Reed
### Comments: ECE 586 Project: Version 3 in Python!
###   Takes three command line parameters:
###      1. input file (in output form for verilog's readmemh)
###      2. debug flag (1 = print debug statements; 0 = silent)
###      3. Switch Register value

# parse the command line arguments
import argparse
parser = argparse.ArgumentParser()
parser.add_argument('input_filename', type=str,
	help = 'input file name')
parser.add_argument('--debug','-d', action='store_true',
	help = 'turn on display of basic debug print statements')
parser.add_argument('--debug_verbose','-v', action='store_true',
	help = 'turn on display of verbose debug print statements')
parser.add_argument('--SR','--sr', nargs='?', const=0, default=0,
	help = 'value of the switch register (SR) in octal')
args = parser.parse_args()

if args.debug == True:
	print ("Debug Mode On")
if args.debug_verbose == True:
	print ("Verbose Debug Mode On")

# Note: the SR argument will be stored as a simple string by default.
if args.SR != 0:
	SR = int(args.SR,8)	# convert to an int
else: 
	SR = 0

import pdp8_isa.py
myPDP8 = PDP8(args.debug,args.debug_verbose,SR) # instantiate a PDP8 object
# clear trace files and load the memory image
myPDP8.init_tracefiles()
myPDP8.loadmemory(input_filename)
halt = 0
myPDP8.open_tracefiles()	# open trace files for append
# execute until a halt instruction is encountered
while not halt:
	halt = pdp8_isa.execute()	# execute next instruction
myPDP8.close_tracefiles()	# close trace files
