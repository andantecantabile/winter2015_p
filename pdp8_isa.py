### Title: pdp8 module
###        for PDP-8 Instruction Set Simulator
### Date: March 24th, 2015
### Author: Elizabeth Reed
### Comments: This module contains the main functions and
###           data structures for the pdp-8 simulator

# import the logarithmic function
from math import log, bin, hex, oct

#----------------------------------------
# CONSTANTS
#------------
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

# Dictionaries for memory operations saved to trace files,
# for branch trace file operations, and opcode information.
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

# Opcode Names
opcode_name = {
    0: 'AND',
    1: 'TAD',
    2: 'ISZ',
    3: 'DCA',
    4: 'JMS',
    5: 'JMP',
    6: 'IO',
    7: 'UI'
}
# Opcode function calls
opcode_type = {
	0: op_and(),
	1: op_tad(),
	2: op_isz(),
	3: op_dca(),
	4: op_jms(),
	5: op_jmp(),
	6: op_io(),
	7: op_ui
}
# Number of cycles required for each opcode type
opcode_cycles = {
	0: 2	# AND = 2 cycles
	1: 2 	# TAD = 2 cycles 
	2: 2 	# ISZ = 2 cycles
	3: 2 	# DCA = 2 cycles 
	4: 2 	# JMS = 2 cycles 
	5: 1 	# JMP = 1 cycle
	6: 0 	# IO = 0 cycles 
	7: 1 	# UI = 1 cycle 
}

#--------------------------------------
# PDP8 CLASS
#--------------------------
class PDP8(object):
	def __init__(self,debug,debug_verbose):
		self.debug = debug		# debug display flag
		self.debug_v = debug_verbose # verbose debug display flag
		self.tracefile = ''		# trace file object
		self.branchfile = ''	# branch file object
		self.mem = list()		# the main memory array
		self.memvalid = list()	# corresponding valid bits
		self.curr_opcode_str = 'NOP'	# the string of the current opcode 
		self.opcode = 0			# integer value of current opcode
		# Dictionary to track current values of registers
		# and machine state, including effective address, 
		# memory at effective address, and the address of 
		# the currently executed instruction (prevPC)
		self.reg = {
			'IR': 0,	# Instruction (current/last executed)
			'PC': 0,	# Program Counter
			'AC': 0,	# Accumulator
			'LR': 0,	# Link Register
			'SR': 0,	# Switch Register
			'eaddr': 0,		# effective address
			'mem_eaddr': 0,	# value in memory @ eaddr
			'prevPC': 0	# PC of the current(last executed) instruction
		}

		# Statistic tracking dictionaries for instruction 
		# counts, total cycles used, and total numbers 
		# of branches taken/not taken.
		self.instr_count = {
			'all': 0,
			'AND': 0,
			'TAD': 0,
			'ISZ': 0,
			'DCA': 0,
			'JMP': 0,
			'JMS': 0,
			'IO': 0,
			'UI': 0
		}
		self.cycle_count = {
			'all': 0,
			'AND': 0,
			'TAD': 0,
			'ISZ': 0,
			'DCA': 0,
			'JMP': 0,
			'JMS': 0,
			'IO': 0,
			'UI': 0
		}
		# counts for taken unconditional branches
		self.branch_uncond_count = {
			'all': 0,
			'JMP': 0,
			'JMS': 0,
			'UI': 0
		}
		# counts for taken conditional branches
		self.branch_cond_t_count = {
			'all': 0,
			'ISZ': 0,
			'UI': 0
		}
		# counts for not taken conditional branches
		self.branch_cond_nt_count = {
			'all': 0,
			'ISZ': 0,
			'UI': 0 
		}

		#===============================================
		# CLASS FUNCTIONS
		#------------

		# Function: open_tracefiles
		# Description: Opens trace files for appending.
		def open_tracefiles(self):
			self.tracefile = open(TRACE_FILE_NAME,'a')
			self.branchfile = open(BRANCH_FILE_NAME,'a')

		# Function: close_tracefiles
		# Description: Closes trace files
		def close_tracefiles(self):
			self.tracefile.close()
			self.branchfile.close()

		#-----------------------------------
		# Function: load_memory
		# Description: Takes input filename as parameter, and 
		#   assigns values accordingly to the main memory array.
		def load_memory(self,filename):
			self.mem = list()	# initialize mem and memvalid to empty lists
			self.memvalid = list()
			# set PC to the starting address
			self.reg['PC'] = START_ADDR
			# clear other registers
			self.reg['AC'] = 0
			self.reg['LR'] = 0
			self.reg['IR'] = 0
			curr_addr = 0
			# Set all valid bits to 0
			for i in range (MEM_SIZE - 1)
				self.memvalid.append(0)
			# read from file
			srcfile = open(filename)
			line = srcfile.readline()
			# Set starting address to the first address given in the file
			if line_char[0] == '@':
				self.reg['PC'] = int('0x'+line_char[1:])
			
			# read lines until end of file is encountered
			while line != '':
				line_char = list(line)
				# if current line specifies an address
				if line_char[0] == '@':
					curr_addr = int('0x'+line_char[1:])
				# otherwise, if current line specifies a memory value
				else 
					curr_data = int('0x'+line_char[:])
					self.memvalid[curr_addr] = 1
					self.mem.insert(curr_addr,curr_data)
					# increment the current address
					curr_addr = curr_addr + 1
				
				# read next line
				line = srcfile.readline()
			
			# close the input file
			srcfile.close()

		#-------------------------------------
		# Function: read_mem
		# Arguments: address, read_type
		# Description: "Performs" a read operation on a location
		#    in memory, writes to the trace file, and returns the 
		#    value read from the given memory location.
		def read_mem(self, address, read_type):
			# obtain address in hexadecimal for print
			addr_hex = hex(address)
			addr_hex = addr_hex[2:]	 # trim the leading '0x'
			# check if the value at the given memory address is valid
			if (self.memvalid[address] != 1)
				print "[Warning: Invalid memory location accessed at",addr_hex
			# write to trace file
			self.tracefile.write(trace_type[read_type]+' '+addr_hex)
			# return the value from memory at given address
			return self.mem[address]	

		# Function: write_mem
		# Arguments: address, value
		# Description: "Performs" a write operation on a location
		#    in memory, writes to the trace file, and updates the 
		#    value at the given memory location.
		def write_mem(self, address, value):
			# obtain address in hexadecimal for print
			addr_hex = hex(address)
			addr_hex = addr_hex[2:]	 # trim the leading '0x'
			# write to trace file
			self.tracefile.write(trace_type['WRITE']+' '+addr_hex)
			# update value in the memory array & set valid bit
			self.mem[address] = value
			self.memvalid[address] = 1

		# Function: calc_eaddr
		# Description: Given the current instruction, if it is an 
		#    instruction that involves memory reference, calculates
		#    the effective address to be used.
		def calc_eaddr(self):
			new_eaddr = 0
			return new_eaddr

		# Function: exec_microinstr
		# Description: Executes the current microinstruction.
		def exec_microinstr(self):
			# do stuff here

		# Function: execute
		# Description: Executes the next instruction (found at the
		#    address specified by the PC).
		# Return Value: 0 -> execution completed successfully,
		#                    and no HLT was encountered
		#               1 -> HLT microinstruction was given.
		def execute(self):
			# STEP 1: Fetch the current instruction
			self.reg['IR'] = self.read_mem(self.reg['PC'],'FETCH')

			# STEP 2: Decode the current instruction
			# determine the opcode
			self.curr_opcode = self.reg['IR'] >> (PDP8_WORD_SIZE - PDP8_OPCODE_SIZE)
			