### Title: pdp8 module
###        for PDP-8 Instruction Set Simulator
### Date: March 24th, 2015
### Author: Elizabeth Reed
### Comments: This module contains the main functions and
###           data structures for the pdp-8 simulator

# import the logarithmic function
from math import log, bin, hex, oct

# Default Output Trace File Names
TRACE_FILE_NAME = 'trace.txt'
BRANCH_FILE_NAME = 'branch.txt'
# Default Starting Address
START_ADDR = 0o200  # 200 octal

# Architecture Constants
PDP8_ADDR_SIZE = 12  # in bits
PDP8_WORD_SIZE = 12
PDP8_WORDS_PER_PAGE = 128
PDP8_PAGE_NUM = 32
PDP8_OPCODE_SIZE = 3   # opcode size in bits
# Special Bit Positions for Memory Reference Addressing
ADDR_INDIRECT_ADDR_BIT = 3
ADDR_MEMORY_PAGE_BIT = 4
# Calculated Constants
MEM_SIZE = PDP8_WORDS_PER_PAGE * PDP8_PAGE_NUM
PAGE_BITS = log(PDP8_PAGE_NUM, 2)
# Address Indices for page and offset
ADDR_PAGE_LOW = 0
ADDR_PAGE_HIGH = PAGE_BITS - 1
ADDR_OFFSET_LOW = PAGE_BITS
ADDR_OFFSET_HIGH = PDP8_ADDR_SIZE - 1

# Dictionaries for memory operations saved to trace file,
# and for branch trace file operations.
trace_type = {
    'READ': 0, 
    'WRITE': 1, 
    'FETCH': 2
}

branch_type = {
    'NO_BRANCH': 0, 
    'UNCONDITIONAL': 1, 
    'CONDITIONAL': 2
}

opcode_type = {
    'AND': 0,
    'TAD': 1,
    'ISZ': 2,
    'DCA': 3,
    'JMS': 4,
    'JMP': 5,
    'IO': 6,
    'UI': 7
}

# Class for the statistic tracking variables
# for instruction counts and total cycles used,
# and total numbers of branches taken/not taken.
class Statistics(object):
    def __init__(self):
	    self.instr_count = 0
		self.instr_cycles = 0
		self.and_count = 0
		self.and_cycles = 0 
		self.tad_count = 0
		self.tad_cycles = 0
		self.isz_count = 0
		self.isz_cycles = 0
		self.dca_count = 0
		self.dca_cycles = 0
		self.jms_count = 0
		self.jms_cycles = 0
		self.jmp_count = 0
		self.jmp_cycles = 0		
		self.io_count = 0
		self.io_cycles = 0
		self.ui_count = 0 
		self.ui_cycles = 0
		self.branch_total_uncond_t = 0 
		self.branch_JMS_t = 0 
		self.branch_JMP_t = 0 
		self.branch_UI_uncond_t = 0 
		self.branch_total_cond_t = 0 
		self.branch_total_cond_nt = 0 
		self.branch_ISZ_t = 0 
		self.branch_ISZ_nt = 0 
		self.branch_UI_cond_t = 0 
		self.branch_UI_cond_nt = 0

# Create an instance of the statistics class
stats = Statistics()		

# Function: open_tracefiles
# Description: Opens trace files for appending.
def open_tracefiles():
    tracefile = open(TRACE_FILE_NAME,'a')
	branchfile = open(BRANCH_FILE_NAME,'a')

# Function: close_tracefiles
# Description: Closes trace files
def close_tracefiles():
    tracefile.close()
	branchfile.close()

# Function: load_memory
# Description: Takes input filename as parameter, and 
#   assigns values accordingly to the main memory array.
def load_memory(filename):
    mem = []
    memvalid = []
	curr_addr = 0
	# Set all valid bits to 0
    for i in range (MEM_SIZE - 1)
        memvalid.append(0)
	# read from file
    srcfile = open(filename)
    line = srcfile.readline()
	# Set starting address to the first address given in the file
	if line_char[0] == '@':
	    START_ADDR = int('0x'+line_char[1:])
    
	while line != '':
	    line_char = list(line)
		# if current line specifies an address
		if line_char[0] == '@':
		    curr_addr = int('0x'+line_char[1:])
		# otherwise, if current line specifies a memory value
		else 
		    curr_data = int('0x'+line_char[:])
		    memvalid[curr_addr] = 1
			mem.insert(curr_addr,curr_data)
			# increment the current address
			curr_addr = curr_addr + 1
		
		# read next line
		line = srcfile.readline()
	
	# close the input file
	srcfile.close()
	
	# set PC to the starting address
	PC = START_ADDR
	# clear other registers
	AC = 0
	LR = 0
	IR = 0

		
# Function: read_mem
# Arguments: address, read_type
# Description: "Performs" a read operation on a location
#    in memory, writes to the trace file, and returns the 
#    value read from the given memory location.
def read_mem(address, read_type):
	# obtain address in hexadecimal for print
	addr_hex = hex(address)
	addr_hex = addr_hex[2:]	 # trim the leading '0x'
    # check if the value at the given memory address is valid
    if (memvalid[address] != 1)
	    print "[Warning: Invalid memory location accessed at",addr_hex
    
	# write to trace file
	tracefile.write(trace_type[read_type]+' '+addr_hex)
	# return the value from memory at given address
	return mem[address]	

# Function: write_mem
# Arguments: address, value
# Description: "Performs" a write operation on a location
#    in memory, writes to the trace file, and updates the 
#    value at the given memory location.
def write_mem(address, value):
    # obtain address in hexadecimal for print
	addr_hex = hex(address)
	addr_hex = addr_hex[2:]	 # trim the leading '0x'
	# write to trace file
	tracefile.write(trace_type['WRITE']+' '+addr_hex)
	# update value in the memory array & set valid bit
	mem[address] = value
	memvalid[address] = 1

# Function: calc_eaddr
# Description: Given the current instruction, if it is an 
#    instruction that involves memory reference, calculates
#    the effective address to be used.
def calc_eaddr():
    new_eaddr = 0
	return new_eaddr

# Function: exec_microinstr
# Description: Executes the current microinstruction.
def exec_microinstr():
    # do stuff here

# Function: execute
# Description: Executes the next instruction (found at the
#    address specified by the PC).
# Return Value: 0 -> execution completed successfully,
#                    and no HLT was encountered
#               1 -> HLT microinstruction was given.
def execute():
    # STEP 1: Fetch the current instruction
	IR = read_mem(PC,'FETCH')

	# STEP 2: Decode the current instruction
	# determine the opcode
	curr_opcode = IR >> (PDP8_WORD_SIZE - PDP8_OPCODE_SIZE)
	