### Title: PDP-8 Instruction Set Simulator
### Last Update Date: March 29, 2015
### Start Date: March 24th, 2015
### Author: Elizabeth Reed
### Comments: ECE 586 Project: Version 3 in Python!
###   Takes three command line parameters:
###      1. input file (in output form for verilog's readmemh)
###      2. debug flag (1 = print debug statements; 0 = silent)
###      3. Switch Register value
### Edit 3/28/15: This GUI version has all three parameters optional,
###   since files may also be loaded via the "open file" button option.

from math import log   	# needed for calculation of number of page bits
import argparse			# needed parsing command line arguments
import tkinter as tk	# needed for GUI functions
import tkinter.ttk as ttk
from tkinter.filedialog import askopenfilename

#==============================================================================
# CONSTANTS
#------------
# Default Output Trace File Names
TRACE_FILE_NAME = 'trace.txt'
BRANCH_FILE_NAME = 'branch.txt'
# Default Starting Address
START_ADDR = 0o200  # 200 octal

# Architecture Constants
PDP8_ADDR_SIZE = int(12)  # in bits
PDP8_WORD_SIZE = int(12)
PDP8_WORDS_PER_PAGE = int(128)
PDP8_PAGE_NUM = int(32)
PDP8_OPCODE_SIZE = int(3)   # opcode size in bits
# Special Bit Positions for Memory Reference Addressing
ADDR_INDIRECT_ADDR_BIT = int(3)
ADDR_MEMORY_PAGE_BIT = int(4)
# Calculated Constants
MEM_SIZE = PDP8_WORDS_PER_PAGE * PDP8_PAGE_NUM
PAGE_BITS = int(log(PDP8_PAGE_NUM, 2))
PDP8_OCT_DIGITS = int(PDP8_WORD_SIZE / 3)
if (PDP8_WORD_SIZE % 3) != 0:
	PDP8_OCT_DIGITS = PDP8_OCT_DIGITS + 1
PDP8_HEX_DIGITS = int(PDP8_WORD_SIZE / 4)
if (PDP8_WORD_SIZE % 4) != 0:
	PDP8_HEX_DIGITS = PDP8_HEX_DIGITS + 1
NUM_OPCODES = 2**PDP8_OPCODE_SIZE
# Address Indices for page and offset
ADDR_PAGE_LOW = int(0)
ADDR_PAGE_HIGH = int(PAGE_BITS - 1)
ADDR_PAGE_SIZE = (ADDR_PAGE_HIGH - ADDR_PAGE_LOW + 1)
ADDR_OFFSET_LOW = PAGE_BITS
ADDR_OFFSET_HIGH = PDP8_ADDR_SIZE - 1
ADDR_OFFSET_SIZE = (ADDR_OFFSET_HIGH - ADDR_OFFSET_LOW + 1)

# Dictionaries for memory operations saved to trace files,
# for branch trace file operations, and opcode information.
TRACE_TYPE = {
	'READ': 0, 
	'WRITE': 1, 
	'FETCH': 2
}

BRANCH_TYPE = {
	'NO_BRANCH': 0, 
	'UNCONDITIONAL': 1, 
	'CONDITIONAL': 2
}

# Opcode Names
OPCODE_NAME = {
    0: 'AND',
    1: 'TAD',
    2: 'ISZ',
    3: 'DCA',
    4: 'JMS',
    5: 'JMP',
    6: 'IO',
    7: 'UI'
}
# Number of cycles required for each opcode type
OPCODE_CYCLES = {
	'AND': 2,	# AND = 2 cycles
	'TAD': 2, 	# TAD = 2 cycles 
	'ISZ': 2, 	# ISZ = 2 cycles
	'DCA': 2, 	# DCA = 2 cycles 
	'JMS': 2, 	# JMS = 2 cycles 
	'JMP': 1, 	# JMP = 1 cycle
	'IO': 0, 	# IO = 0 cycles 
	'UI': 1 	# UI = 1 cycle 
}
# Number of cycles added for effective address calculation
EADDR_CYCLES = {
	'AutoIndex': 2,	# Auto-Indexing: 2 additional cycles 
	'Indirect': 1 	# Indirect Addressing: 1 additional cycle  
}

# BIT POSITION LABELS FOR UI INSTRUCTIONS
BIT_POS_LBL = {
	'UI_GRP1': ['','','','','cla','cll','cma','cml','rar','ral','0/1','iac'],
	'UI_GRP2_OR': ['','','','','cla','sma','sza','snl','0/1','osr','hlt',''],
	'UI_GRP2_AND': ['','','','','cla','spa','sna','szl','0/1','osr','hlt',''],
	'DEFAULT': ['','','','','','','','','','','','']
}

# END LIST OF CONSTANTS
#==============================================================================


#==============================================================================
# PDP8_ISA CLASS DEFINITION
#----------------------------
class PDP8_ISA(object):
	def __init__(self,debug,debug_verbose,SR):
		self.debug = debug		# debug display flag
		self.debug_v = debug_verbose # verbose debug display flag
		self.tracefile = ''		# trace file object
		self.branchfile = ''	# branch file object
		self.opcode_str = 'NOP'	# the string of the current opcode 
		self.opcode = 0			# integer value of current opcode
		self.word_mask = (1 << PDP8_WORD_SIZE) - 1
		# Current values of all registers
		# and machine state, including effective address, 
		# memory at effective address, and the address of 
		# the currently executed instruction (prevPC)
		# List of full size registers and values
		self.reg_names = ['IR','PC','AC','SR','eaddr','mem_eaddr','prevPC']
		self.regs = {
			'IR': 0,		# Instruction (current/last executed)
			'PC': 0,		# Program Counter
			'AC': 0,		# Accumulator
			'LR': 0,		# Link Register
			'SR': SR,		# Switch Register
			'eaddr': 0,		# effective address
			'mem_eaddr': 0,	# value in memory @ eaddr
			'prevPC': 0		# PC of the current(last executed) instruction
		}
		self.flagHLT = False
		# Create Memory Arrays
		self.mem = list()	# initialize mem and memvalid lists
		self.memvalid = list() 	# each entry is true/false indicating if valid
		self.mem_valid_addrlist = list() # list of addresses that are currently valid
		self.mem_breakpoint = list()
		# flag used to indicate breakpoint after curr instruction
		self.flag_breakpoint = False
		# Note that breakpoints need to be tk.IntVals, for 
		# attaching to the tk.checkbuttons.
		# Set all valid bits to 0; initialize memory list to 0
		for i in range (MEM_SIZE):
			self.memvalid.append(0)
			self.mem.append(0)
			int_val = tk.IntVar()
			self.mem_breakpoint.append(int_val)
			self.mem_breakpoint[i].set(0)	# initialize as false
		# GUI String Values for register values
		self.GUI_reg_vals = {}
		# List of allowed string format types
		self.GUI_format_types = ['oct','hex','bin']
		# Create zero value default strings
		zero_str = {}
		zero_str['oct'] = self.format_str(0,'oct')
		zero_str['hex'] = self.format_str(0,'hex')
		zero_str['bin'] = self.format_str(0,'bin')
		# Create a tkStringVar for each valid format type
		for name in self.reg_names:
			self.GUI_reg_vals.update({name:{}})
			for type in self.GUI_format_types:
				str_var = tk.StringVar()
				self.GUI_reg_vals[name].update({type:str_var})
				self.GUI_reg_vals[name][type].set(zero_str[type])
		# GUI String Values for Memory Values
		self.GUI_mem_vals = {}
		# Create a tk.StringVar for each valid format type
		for i in range(MEM_SIZE):
			self.GUI_mem_vals.update({i:{}})
			#self.GUI_mem_vals[str(i)] = {}
			for type in self.GUI_format_types:
				str_var = tk.StringVar()
				self.GUI_mem_vals[i].update({type:str_var})
				#self.GUI_mem_vals[str(i)][type] = str_var
				self.GUI_mem_vals[i][type].set(zero_str[type])
		# Create tk.StringVar for special variables
		# LR is one bit only
		self.GUI_LR_val = tk.StringVar()
		self.GUI_LR_val.set('0')
		# Opcode is a string name
		self.GUI_opcode_str = tk.StringVar()
		self.GUI_opcode_str.set('NOP')
		# IR binary digits
		self.GUI_IR_bin_val = []
		for i in range(PDP8_WORD_SIZE):
			self.GUI_IR_bin_val.append(tk.StringVar())
			self.GUI_IR_bin_val[i].set('0')
		# corresponding bit position labels
		self.GUI_IR_bit_disp_type = 'DEFAULT'
		self.GUI_IR_bit_lbl = []
		for i in range(PDP8_WORD_SIZE):
			self.GUI_IR_bit_lbl.append(tk.StringVar())
			self.GUI_IR_bit_lbl[i].set('')
		
		# locations last accessed in memory; used in GUI
		self.GUI_mem_highlight_types = ['instr_fetch','eaddr_read','eaddr_write','mem_read','mem_write']
		self.GUI_mem_ref = {
			'instr_fetch': -1,
			'eaddr_read': -1,
			'eaddr_write': -1, 
			'mem_read': -1,
			'mem_write': -1
		}	

		# Opcode function calls
		self.opcode_exec = {
			0: self.op_and,
			1: self.op_tad,
			2: self.op_isz,
			3: self.op_dca,
			4: self.op_jms,
			5: self.op_jmp,
			6: self.op_io,
			7: self.op_ui
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
			'JMS': 0,
			'JMP': 0,
			'IO': 0,
			'UI': 0
		}
		self.cycle_count = {
			'all': 0,
			'AND': 0,
			'TAD': 0,
			'ISZ': 0,
			'DCA': 0,
			'JMS': 0,
			'JMP': 0,
			'IO': 0,
			'UI': 0
		}
		# counts for taken unconditional branches
		self.branch_uncond_count = {
			'all': 0,
			'JMS': 0,
			'JMP': 0,
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
		# the condition tests made on last branch (for UI)
		self.branch_tests = ''
		# the OR condition tests that succeeded on last branch (for UI)
		self.branch_OR_success = ''
		# the AND condition tests that failed on last branch (for UI)
		self.branch_AND_fail = ''

	#===============================================
	# CLASS FUNCTIONS
	#------------
	
	# Function: init_tracefiles
	# Description: Clears contents of output trace file,
	#    prints header for the branch trace file
	def init_tracefiles(self):
		self.tracefile = open(TRACE_FILE_NAME,'w')
		self.tracefile.close()
		self.branchfile = open(BRANCH_FILE_NAME,'w')
		self.branchfile.write('PC [octal]    BRANCH TYPE         TAKEN/NOT TAKEN    TARGET ADDRESS [octal]\n')
		self.branchfile.write('---------------------------------------------------------------------------\n')
		self.branchfile.close()

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
	# Function: format_str
	# Description: Takes two arguments, an integer
	#	value and a string indicating the desired 
	#	format of the string result. Returns a string
	#	of the desired number format, with leading zeroes.
	# Arguments:	1. integer value 
	#				2. format type ('oct','hex', or 'bin')
	def format_str(self,value,format_type):
		ret_str = ''	# initialize return value
		if format_type == 'oct':
			ret_str = oct(value)[2:]	# trim leading '0o'
			while len(ret_str) < PDP8_OCT_DIGITS:
				ret_str = '0' + ret_str		# add leading zero digits
		elif format_type == 'hex':
			ret_str = hex(value)[2:]	# trim leading '0x'
			while len(ret_str) < PDP8_HEX_DIGITS:
				ret_str = '0' + ret_str
		elif format_type == 'bin':
			ret_str = bin(value)[2:]	# trim leading '0b'
			while len(ret_str) < PDP8_WORD_SIZE:
				ret_str = '0' + ret_str
		# return string
		return ret_str

	
	#-----------------------------------
	# Function: clear_stats
	# Description: Clears all stat variables
	def clear_stats(self):
		# build a list of opcode categories
		list_ops = []
		for i in range(NUM_OPCODES):
			list_ops.append(OPCODE_NAME[i])
		list_ops.append('all')
		# build list of branch types 
		list_uncond_branch_types = ['all','JMS','JMP','UI']
		list_cond_branch_types = ['all','ISZ','UI']

		# clear instr_count and cycle_count
		for name in list_ops:
			self.instr_count[name] = 0 
			self.cycle_count[name] = 0 
		# clear branch counts
		for name in list_uncond_branch_types:
			self.branch_uncond_count[name] = 0
		for name in list_cond_branch_types:
			self.branch_cond_nt_count[name] = 0 
			self.branch_cond_t_count[name] = 0

	
	#-----------------------------------
	# Function: load_memory
	# Description: Takes input filename as parameter, and 
	#   assigns values accordingly to the main memory array.
	def load_memory(self,filename):
		# clear registers (Note: do NOT clear SR)
		for name in ['IR','PC','AC','eaddr','mem_eaddr','prevPC']:
			self.regs[name] = 0 
		self.opcode = 0
		self.opcode_str = 'NOP'
		# set PC to the starting address
		self.regs['PC'] = START_ADDR
		
		# Clear all locations referenced in memory by last instruction
		for type in self.GUI_mem_highlight_types:
			self.GUI_mem_ref[type] = -1
		# Set default string for GUI_IR_bit_disp_type
		self.GUI_IR_bit_disp_type='DEFAULT'
		self.flag_breakpoint = False
		
		# clear the list of addresses that are currently valid
		self.mem_valid_addrlist = list() 
		
		curr_addr = 0
		# Set all valid bits to 0; initialize memory list to 0
		for i in range (MEM_SIZE):
			self.memvalid[i]=0
			self.mem[i]=0
		# read from file
		srcfile = open(filename)
		line_str = srcfile.readline()
		# Set starting address to the first address given in the file
		if line_str[0] == '@':
			if line_str[1] !='0':
				self.regs['PC'] = int(line_str[1:-1],16)
				# Note: Trim off the '\n'
			elif line_str[2] != '0':
				self.regs['PC'] = int(line_str[2:-1],16)
			else:
				self.regs['PC'] = int(line_str[3],16)
		
		# read lines until end of file is encountered
		while (line_str != '') and (line_str != '\n'):
			# get value
			if (line_str[0] != '@') and (line_str[0] != '0'):
				curr_val = int(line_str[0:-1],16)
				# Note: Trim off the '\n'
			elif line_str[1] != '0':
				curr_val = int(line_str[1:-1],16)
			elif (line_str[0] != '@') or (line_str[2] != '0'):
				curr_val = int(line_str[2:-1],16)
			else:
				curr_val = int(line_str[3],16)
			
			# if current line specifies an address
			if line_str[0] == '@':
				curr_addr = int(curr_val)
			# otherwise, if current line specifies a memory value
			else: 
				curr_data = int(curr_val)
				self.memvalid[curr_addr] = 1
				self.mem[curr_addr] = curr_data
				# add the address to list of valid addresses 
				self.mem_valid_addrlist.append(curr_addr)
				# update StringVals for GUI 
				for type in self.GUI_format_types:
					self.GUI_mem_vals[curr_addr][type].set(self.format_str(curr_data,type))
				# increment the current address
				curr_addr = curr_addr + 1
			
			# read next line
			line_str = srcfile.readline()
		
		# sort the valid addrlist
		self.mem_valid_addrlist.sort()
		
		# update StringVals for GUI
		for reg in self.reg_names:
			for type in self.GUI_format_types:
				self.GUI_reg_vals[reg][type].set(self.format_str(self.regs[reg],type))
		# IR binary values:
		tmp_val = self.format_str(self.regs['IR'],'bin')
		for i in range(PDP8_WORD_SIZE):
			self.GUI_IR_bin_val[i].set(tmp_val[i])
		# LR:
		self.GUI_LR_val.set(int(self.regs['LR']))
		# Opcode:
		self.GUI_opcode_str.set(self.opcode_str)
		# Bit Position Labels:
		for i in range(PDP8_WORD_SIZE):
			self.GUI_IR_bit_lbl[i].set(BIT_POS_LBL[self.GUI_IR_bit_disp_type][i])
		
		# if debug is on, print out all valid memory values:
		if self.debug:
			print ("\n=====================================================")
			print (" STARTING MEMORY:")
			for i in range(MEM_SIZE):
				if self.memvalid[i] == 1:
					print ("Address: {0:04o}  Value: {1:04o}".format(i, self.mem[i]))
			print ("=====================================================\n")
		
		# close the input file
		srcfile.close()

	#-------------------------------------
	# Function: read_mem
	# Arguments: address, read_type
	# Description: "Performs" a read operation on a location
	#    in memory, writes to the trace file, and returns the 
	#    value read from the given memory location.
	def read_mem(self, address, read_type):
		# check if the value at the given memory address is valid
		if (self.memvalid[address] != 1):
			print ("[Warning: Invalid memory location accessed at {0:04o}".format(address))
		# write to trace file
		self.tracefile.write("{0} {1:03x}\n".format(str(TRACE_TYPE[read_type]),address))
		# return the value from memory at given address
		return (self.mem[address] & self.word_mask)

	#-------------------------------------
	# Function: write_mem
	# Arguments: address, value
	# Description: "Performs" a write operation on a location
	#    in memory, writes to the trace file, and updates the 
	#    value at the given memory location.
	def write_mem(self, address, value):
		# write to trace file
		self.tracefile.write("{0} {1:03x}\n".format(str(TRACE_TYPE['WRITE']),address))
		
		# update value in the memory array & set valid bit
		self.mem[address] = value
		# if valid bit is not set, add it to the list of valid addresses 
		# and set the valid bit 
		if not(self.memvalid[address]):
			self.memvalid[address] = 1
			self.mem_valid_addrlist.append(address)
			# sort the valid addrlist
			self.mem_valid_addrlist.sort()
			
		# update the StringVals used by the GUI
		for type in self.GUI_format_types:
			self.GUI_mem_vals[address][type].set(self.format_str(value,type))

	#-------------------------------------
	# Function: write_branch_trace
	# Arguments: current PC, opcode (string), target address,
	#    the type of branch, and a flag indicating taken/not taken.
	# Description: Writes a line to the branch trace file and 
	#    updates branch statistics.
	def write_branch_trace(self, curr_PC, op_str, target_addr, 
		branch_type, branch_taken):
		# unconditional branch type
		if branch_type == BRANCH_TYPE['UNCONDITIONAL']:
			self.branch_uncond_count['all'] = self.branch_uncond_count['all'] + 1
			self.branch_uncond_count[op_str] = self.branch_uncond_count[op_str] + 1
			# write to trace file
			self.branchfile.write("{0:04o}          UNCONDITIONAL [{1:3s}]  TAKEN              {2:04o} \n".format(curr_PC, op_str, target_addr))
			# Example formatted print, uses a tuple: print '%d, %0d, %5d, %05d' % (34, 34, 34, 34)
		# conditional branch type 
		elif branch_type == BRANCH_TYPE['CONDITIONAL']:
			if branch_taken == True:
				self.branch_cond_t_count['all'] = self.branch_cond_t_count['all'] + 1 
				self.branch_cond_t_count[op_str] = self.branch_cond_t_count[op_str] + 1 
				self.branchfile.write("{0:04o}          CONDITIONAL [{1:3s}]    TAKEN              {2:04o} \n".format(curr_PC, op_str, target_addr))
			else: 
				self.branch_cond_nt_count['all'] = self.branch_cond_nt_count['all'] + 1 
				self.branch_cond_nt_count[op_str] = self.branch_cond_nt_count[op_str] + 1
				self.branchfile.write("{0:04o}          CONDITIONAL [{1:3s}]    NOT TAKEN          {2:04o} \n".format(curr_PC, op_str, target_addr))
	
	#-------------------------------------
	# Function: calc_eaddr
	# Description: Given the current instruction, if it is an 
	#    instruction that involves memory reference, calculates
	#    the effective address to be used.
	#    Uses the current value of the prevPC, the IR, and
	#    may read/write to mem[].
	#    Note that this function does not verify that the 
	#    opcode is in range of memory instructions, assumes
	#    that the check is performed before calc_eaddr has 
	#    been called.
	def calc_eaddr(self):
		# Convert IR to a binary string to check if specific
		# flag bits are set.
		IR_bin_str = bin(self.regs['IR'])
		IR_bin_str = IR_bin_str[2:]	# trim off leading '0b'
		
		while len(IR_bin_str) < PDP8_WORD_SIZE:
			IR_bin_str = '0'+IR_bin_str
		
		offset_mask = (1 << ADDR_OFFSET_SIZE) - 1 
		page_mask = ((1 << ADDR_PAGE_SIZE) - 1) << ADDR_OFFSET_SIZE
		
		current_page = self.regs['prevPC'] & page_mask 
		current_offset = self.regs['IR'] & offset_mask
			
		eff_addr = -1	# initialize return val to -1
				
		# Check if the Indirect Addressing bit is not set
		if IR_bin_str[ADDR_INDIRECT_ADDR_BIT] == '0':
			# If Indirect Addressing bit = 0 (Direct addressing) 
			# Check if the Memory Page bit is set...
			if IR_bin_str[ADDR_MEMORY_PAGE_BIT] == '0':
				# ADDRESSING MODE 1: Zero Page Addressing
				#    Effective Address <- 00000 + Offset
				eff_addr = current_offset
			else:	# Memory Page bit = 1
				# ADDRESSING MODE 2: Current Page Addressing
				#    Effective Address <- Old_PC[0:4] + Offset
				eff_addr = current_page + current_offset
		else: # Indirect Addressing bit = 1 
			# Check if the AutoIndex registers are not selected.
			# (locations outside of 0010 through 0017 (octal) have been indicated)
			if ( (current_offset < 0o10) or (current_offset > 0o17) ):
				# ADDRESSING MODE 3: Indirect Addressing
				# Check if the memory bit is set 
				if IR_bin_str[ADDR_MEMORY_PAGE_BIT] == '0':
					# Zero Page Addressing, so: 
					#    Effective Address <- C(00000 + Offset)
					indirect_addr_loc = current_offset
					# Read memory at indirect_addr_loc
					eff_addr = self.read_mem(indirect_addr_loc,'READ')
					self.GUI_mem_ref['eaddr_read'] = indirect_addr_loc
				else:
					# Current Page Addressing, so:
					#    Effective Address <- C(Old_PC[0:4] + Offset)
					indirect_addr_loc = current_page + current_offset
					# Read memory at indirect_addr_loc
					eff_addr = self.read_mem(indirect_addr_loc,'READ')
					self.GUI_mem_ref['eaddr_read'] = indirect_addr_loc
				# Add cycles for use of Indirect Addressing
				self.cycle_count['all'] = self.cycle_count['all'] + EADDR_CYCLES['Indirect']
				self.cycle_count[self.opcode_str] = self.cycle_count[self.opcode_str]+EADDR_CYCLES['Indirect']
			else: # offset location in range of 0010 - 0017 (octal) was specified
				# ADDRESSING MODE 4: AutoIndex Addressing
				#      C(AutoIndex_Register) <- C(AutoIndex_Register) + 1
				#      EffectiveAddress <- C(AutoIndex_Register)
				indirect_addr_loc = current_offset
				# Read memory at indirect_addr_loc
				eff_addr = self.read_mem(indirect_addr_loc,'READ')
				self.GUI_mem_ref['eaddr_read'] = indirect_addr_loc
				# Increment the value 
				eff_addr = eff_addr + 1 
				# Store the incremented value in memory
				self.write_mem(indirect_addr_loc,eff_addr)
				self.GUI_mem_ref['eaddr_write'] = indirect_addr_loc
				# Add cycles for use of AutoIndex Addressing
				self.cycle_count['all'] = self.cycle_count['all'] + EADDR_CYCLES['AutoIndex']
				self.cycle_count[self.opcode_str] = self.cycle_count[self.opcode_str]+EADDR_CYCLES['AutoIndex']
		# Return the calculated effective address
		return int(eff_addr)

	#-------------------------------------	
	# Function: op_and
	# Description: Executes the AND operation.
	def op_and(self):
		# First read the value at eaddr
		self.regs['mem_eaddr'] = self.read_mem(self.regs['eaddr'],'READ')
		self.GUI_mem_ref['mem_read'] = self.regs['eaddr']
		# Calculate AC & mem_val
		self.regs['AC'] = self.regs['AC'] & self.regs['mem_eaddr']
		
	#-------------------------------------	
	# Function: op_tad
	# Description: Executes the TAD operation.
	def op_tad(self):
		# First read the value at eaddr
		self.regs['mem_eaddr'] = self.read_mem(self.regs['eaddr'],'READ')
		self.GUI_mem_ref['mem_read'] = self.regs['eaddr']
		# Add AC and mem_val
		sum = self.regs['AC'] + self.regs['mem_eaddr']
		# if there is overflow from the MSbit position,
		# invert the LR 
		if ( (sum >> PDP8_WORD_SIZE) != 0 ):
			self.regs['LR'] = not(self.regs['LR'])  
			# Note: Using logical NOT here, since LR is one bit only
		# save the AC using mask
		self.regs['AC'] = sum & self.word_mask 
	
	#-------------------------------------	
	# Function: op_isz
	# Description: Executes the ISZ operation.
	def op_isz(self):
		# First read the value at eaddr
		self.regs['mem_eaddr'] = self.read_mem(self.regs['eaddr'],'READ')
		self.GUI_mem_ref['mem_read'] = self.regs['eaddr']
		# Increment value by 1
		self.regs['mem_eaddr'] = (self.regs['mem_eaddr'] + 1) & self.word_mask
		# Write updated value to memory
		self.write_mem(self.regs['eaddr'],self.regs['mem_eaddr'])
		self.GUI_mem_ref['mem_write'] = self.regs['eaddr']
		# Check if the updated value is 0: if so, skip next instr
		if self.regs['mem_eaddr'] == 0:
			self.regs['PC'] = self.regs['PC'] + 1
			# Write to branch trace file, providing current PC, opcode string,
			# target address, branch type, and flag indicating branch taken/not taken
			self.write_branch_trace(self.regs['prevPC'], self.opcode_str, 
				self.regs['PC'], BRANCH_TYPE['CONDITIONAL'], True)
		else:
			self.write_branch_trace(self.regs['prevPC'], self.opcode_str, 
				self.regs['PC'], BRANCH_TYPE['CONDITIONAL'], False)
	
	#-------------------------------------	
	# Function: op_dca
	# Description: Executes the DCA operation.
	def op_dca(self):
		# Write AC to memory
		self.write_mem(self.regs['eaddr'],self.regs['AC'])
		self.GUI_mem_ref['mem_write'] = self.regs['eaddr']
		# indicate the new value of mem[eaddr] (for GUI display)
		self.regs['mem_eaddr'] = self.regs['AC']
		# Clear the AC
		self.regs['AC'] = 0 
	
	#-------------------------------------	
	# Function: op_jms
	# Description: Executes the JMS operation.
	def op_jms(self):
		# Save the PC to the effective address location
		# (Recall that PC was already incremented in step 1, 
		#  so it is already pointing to the next instruction)
		self.write_mem(self.regs['eaddr'],self.regs['PC'])
		self.GUI_mem_ref['mem_write'] = self.regs['eaddr']
		# indicate the new value of mem[eaddr] for GUI display
		self.regs['mem_eaddr'] = self.regs['PC']
		# Set the PC to (EffAddr + 1)
		self.regs['PC'] = (self.regs['eaddr'] + 1) & self.word_mask 
		# Write to the branch trace file, providing current PC, opcode string,
		# target address, branch type, and flag indicating branch taken/not taken
		self.write_branch_trace(self.regs['prevPC'], self.opcode_str, 
				self.regs['PC'], BRANCH_TYPE['UNCONDITIONAL'], True)
	
	#-------------------------------------	
	# Function: op_jmp
	# Description: Executes the JMP operation.
	def op_jmp(self):
		# Set PC to the effective address
		self.regs['PC'] = self.regs['eaddr']
		# indicate memory at the effective address, even though it was not used 
		self.regs['mem_eaddr'] = self.mem[self.regs['eaddr']]
		# Write to the branch trace file, providing current PC, opcode string,
		# target address, branch type, and flag indicating branch taken/not taken
		self.write_branch_trace(self.regs['prevPC'], self.opcode_str, 
				self.regs['PC'], BRANCH_TYPE['UNCONDITIONAL'], True)
	
	#-------------------------------------	
	# Function: op_io
	# Description: Executes the IO operation.
	def op_io(self):
		# Not implemented, print warning
		print ("WARNING: IO instruction encountered at PC: [%04o]\n", self.prevPC)

	#-------------------------------------
	# Function: op_ui
	# Description: Executes the current microinstruction.
	def op_ui(self):
		# Convert IR to a binary string to test for setting of specific bit positions
		IR_str = bin(self.regs['IR'])
		IR_str = IR_str[2:]	# trim off leading '0b'
		
		while len(IR_str) < PDP8_WORD_SIZE:
			IR_str = '0'+IR_str
		
		# Initialize this instr as NOT a branch
		curr_branch_type = BRANCH_TYPE['NO_BRANCH']
		curr_branch_taken = False
		str_OR_success = '' # OR conditions which were met
		str_AND_fail = '' # AND conditions that failed
		str_skip_check = ''
		
		# Verbose Debug Print for UI Instructions
		if self.debug_v:
			print (" ")
			print ("***************** UI MODULE DEBUG ******************")
			print ("   Current Instr: {0:04o}".format(self.regs['IR']))
			print (" ")
			print ("   0   1   2   3   4   5   6   7   8   9  10  11")
			print (" +---+---+---+---+---+---+---+---+---+---+---+---+")
			print (" | {0} | {1} | {2} | {3} | {4} | {5} | {6} | {7} | {8} | {9} | {10} | {11} |".format(
				IR_str[0],IR_str[1],IR_str[2],IR_str[3],IR_str[4],IR_str[5],
				IR_str[6],IR_str[7],IR_str[8],IR_str[9],IR_str[10],IR_str[11]))
			print (" +---+---+---+---+---+---+---+---+---+---+---+---+")
		
		# Group 1 Microinstructions: Check if bit 3 is a 0
		if IR_str[3] == '0':
			self.GUI_IR_bit_disp_type = 'UI_GRP1'
			if self.debug_v:
				print ("                  cla cll cma cml rar ral 0/1 iac")
				print (" ")
				print ("Group 1 Microinstructions:")
			
			# if bits IR[4:11] == 0, then the instruction is a NOP
			if (((self.regs['IR'] << 4) & self.word_mask) == 0):
				# NOP
				print (" -- NOP")
			else:
				# Sequence 1: CLA/CLL
				# Check if bits 4 and 5 were set
				if IR_str[4] == '1':
					self.regs['AC'] = 0
					if self.debug_v:
						print (" -- Clear Accumulator")
						print ("                NEW AC: {0:04o}".format(self.regs['AC']))
				
				if IR_str[5] == '1':
					self.regs['LR'] = 0
					if self.debug_v:
						print (" -- Clear Link Register")
						print ("                NEW LR: {0:1o}".format(self.regs['LR']))
				
				# Sequence 2: CMA/CML
				# Check if bits 6 and 7 were set
				if IR_str[6] == '1':
					self.regs['AC'] = (~self.regs['AC']) & self.word_mask
					if self.debug_v:
						print (" -- Complement Accumulator")
						print ("                NEW AC: {0:04o}".format(self.regs['AC']))
				
				if IR_str[7] == '1':
					self.regs['LR'] = not(self.regs['LR'])	# use logical not here since LR is one bit only
					if self.debug_v:
						print (" -- Complement Link Register")
						print ("                NEW LR: {0:1o}".format(self.regs['LR']))
				
				# Sequence 3: IAC
				# Check if bit 11 is set
				if IR_str[11] == '1':
					self.regs['AC'] = self.regs['AC'] + 1
					if (self.regs['AC'] >> PDP8_WORD_SIZE) != 0: # Check for overflow
						self.regs['LR'] = not(self.regs['LR'])	# invert LR bit
					self.regs['AC'] = self.regs['AC'] & self.word_mask 	# mask upper bits of AC to word size
					
					if self.debug_v:
						print (" -- Complement Accumulator")
						print ("                NEW AC: {0:04o}".format(self.regs['AC']))
						print ("                NEW LR: {0:1o}".format(self.regs['LR']))
				
				# Sequence 4: RAR/RAL
				# Check if bits 8 and 9 have been set simultaneously: if so, this
				# is an invalid instruction, since a rotate right and rotate left has
				# been simultaneously indicated. Print a warning, but allow instruction 
				# to "execute" since performing the right and left rotate will cancel 
				# each other out and leave the AC unchanged.
				if (IR_str[8] == '1') and (IR_str[9] == '1'):
					print ("WARNING: Micro Op instruction conflict at PC = [{0:04o}]. Rotate Left and Rotate Right enabled simultaneously.\n".format(self.prevPC))
				
				# Rotate right:
				# Check bit 8, which indicates a rotate right operation
				if IR_str[8] == '1':
					# Let tmp_val be set to the concatenation of LR and AC, 
					# {LR,AC}
					tmp_val = (self.regs['LR'] << PDP8_WORD_SIZE) + self.regs['AC']
					
					# Check if bit 10 is 0: If so, only need to rotate one bit position
					if IR_str[10] == '1':
						# First make the most significant bit of tmp_rotate
						# equal to the least significant bit of tmp_val
						tmp_rotate = (tmp_val & 1) << PDP8_WORD_SIZE
						
						# Then OR the remaining more significant bits of tmp_val
						# with tmp_rotate
						tmp_rotate = tmp_rotate | (tmp_val >> 1)
						
						if self.debug_v:
							print (" -- Rotate Accumulator and Link Right")
					
					# Otherwise bit 10 (the 0/1 bit) is 1 --> rotate 2 positions right
					else:
						# First set the two most significant bits of tmp_rotate
						# equal to the two least significant bits of tmp_val
						tmp_rotate = (tmp_val & 3) << (PDP8_WORD_SIZE - 1)
						# Then OR the remaining more significant bits of tmp_val
						# with tmp_rotate
						tmp_rotate = tmp_rotate | (tmp_val >> 2)
						
						if self.debug_v:
							print (" -- Rotate Accumulator and Link Right Twice")
					
					# The new value of LR should be the most significant
					# bit of tmp_rotate, and the AC should be set to all the 
					# less significant bits of tmp_rotate.
					# {LR, AC} = tmp_rotate
					self.regs['LR'] = tmp_rotate >> PDP8_WORD_SIZE
					self.regs['AC'] = tmp_rotate & word_mask
					
					# Debug Print
					if self.debug_v:
						print ("                NEW LR: {0:1o}".format(self.regs['LR']))
						print ("                NEW AC: {0:04o}".format(self.regs['AC']))
				
				# Rotate left
				# Check if bit 9 is 1: RAL
				if IR_str[9] == '1':
					# Let tmp_val be set to the concatenation of LR and AC, 
					# {LR,AC}
					tmp_val = (self.regs['LR'] << PDP8_WORD_SIZE) + self.regs['AC']
					
					# Check if bit 10 is 0: If so, only need to rotate one bit position
					if IR_str[10] == '1':
						# First set the least significant bit of tmp_rotate to be
						# the most significant of tmp_val.
						tmp_rotate = tmp_val >> PDP8_WORD_SIZE
						# Then OR tmp_rotate with all the remaining bits of tmp_val
						# after shifting them left one position.
						tmp_rotate = tmp_rotate | ((tmp_val & self.word_mask) << 1)
						if self.debug_v:
							print (" -- Rotate Accumulator and Link Left")
					
					# Otherwise bit 10(the 0/1 bit) is 1 --> rotate 2 positions left
					else:
						# First set the two least significant bits of tmp_rotate to be
						# the least significant two of tmp_val
						tmp_rotate = tmp_val >> (PDP8_WORD_SIZE - 1)
						# Then OR tmp_rotate with all remaining bits of tmp_val
						# after shifting them left two positions. Actually, what 
						# is done here: shift tmp_val to the left 1 bit and AND 
						# result with word_mask to set the most significant two 
						# bits to 0, then shift left one more bit position, so that
						# the next most significant bit will have been shifted two
						# bits left.
						tmp_rotate = tmp_rotate | (((tmp_val << 1) & self.word_mask) << 1)
						if self.debug_v:
							print (" -- Rotate Accumulator and Link Left Twice")
											
					# Next, the new value of LR should be the most significant
					# bit of tmp_rotate, and the AC should be set to all the 
					# less significant bits of tmp_rotate.
					self.regs['LR'] = tmp_rotate >> PDP8_WORD_SIZE
					self.regs['AC'] = tmp_rotate & word_mask
					
					# Debug Print
					if self.debug_v:
						print ("                NEW LR: {0:1o}".format(self.regs['LR']))
						print ("                NEW AC: {0:04o}".format(self.regs['AC']))

		# Else, Bit 3 is 1, indicating either Group 2 or 3 Microinstructions
		else:
			# Check if bit 11 is 0: Group 2 Microinstructions
			if IR_str[11] == '0':
				# OR subgroup: Check if bit 8 is set to 0 
				if IR_str[8] == '0':
					self.GUI_IR_bit_disp_type = 'UI_GRP2_OR'
					if self.debug_v:
						print ("                  cla sma sza snl 0/1 osr hlt")
						print (" ")
						print (" Group 2 Microinstructions:")
					
					# check if any of bits 5 through 7 were set, indicating
					# that an OR skip condition was to be checked (this instruction
					# should be flagged as a conditional branch instruction)
					if ((self.regs['IR'] >> (PDP8_WORD_SIZE - 7-1)) & 7) != 0:
						curr_branch_type = BRANCH_TYPE['CONDITIONAL']
					
					# SMA - Skip on Minus Accumulator: check bit 5
					if IR_str[5] == '1':
						# if most significant bit of AC is 1, then skip
						if (self.regs['AC'] >> (PDP8_WORD_SIZE - 1)) == 1:
							curr_branch_taken = True
							str_OR_success = str_OR_success + 'SMA '
						str_skip_check = str_skip_check + 'SMA '
					
					# SZA - Skip on Zero Accumulator: check bit 6
					if IR_str[6] == '1':
						# if AC is 0, then skip
						if self.regs['AC'] == 0:
							curr_branch_taken = True
							str_OR_success = str_OR_success + 'SZA '
						str_skip_check = str_skip_check + 'SZA '
					
					# SNL - Skip on Nonzero Link: check bit 7
					if IR_str[7] == '1':
						# if LR is not 0, then skip
						if self.regs['LR'] != 0:
							curr_branch_taken = True
							str_OR_success = str_OR_success + 'SNL '
						str_skip_check = str_skip_check + 'SNL '
					
					# Debug Print: Indicating if any of the OR skip conditions were met
					if self.debug_v and curr_branch_type == BRANCH_TYPE['CONDITIONAL']:
						if curr_branch_taken:
							print (" -- OR group condition(s) met: {0}".format(str_OR_success))
						else:
							print (" -- OR group condition(s) not met.")
						print ("    Checked for: {0}".format(str_skip_check))

				# Else, AND subgroup (bit 8 = 1)
				else:
					self.GUI_IR_bit_disp_type = 'UI_GRP2_AND'
					# debug print header
					if self.debug_v:
						print ("                  cla spa sna szl 0/1 osr hlt")
						print (" ")
						print (" Group 2 Microinstructions:")
					
					# check if bits [5:7] were all zero: Skip Always should be 
					# flagged as an unconditional branch.
					if ((self.regs['IR'] >> (PDP8_WORD_SIZE - 7-1)) & 7) == 0:
						curr_branch_type = BRANCH_TYPE['UNCONDITIONAL']
						str_skip_check = 'None. (Unconditional branch)'
					else:
						curr_branch_type = BRANCH_TYPE['CONDITIONAL']
					
					# set skip flag to true initially
					curr_branch_taken = True
					
					# Note that for the AND section, str_AND_fail is used 
					# to indicate the conditions that failed.
					
					# SPA - Skip on Positive Accumulator: check bit 5
					if IR_str[5] == '1':
						# if most significant bit of AC is not 0, then 
						# then AC is negative, and condition is not met
						if (self.regs['AC'] >> (PDP8_WORD_SIZE - 1)) == 1:
							curr_branch_taken = False
							str_AND_fail = str_AND_fail + 'SPA '
						str_skip_check = str_skip_check + 'SPA '
					
					# SNA - Skip on Nonzero Accumulator: check bit 6
					if IR_str[6] == '1':
						# if AC is 0, then condition was not met, so do not skip
						if self.regs['AC'] == 0:
							curr_branch_taken = False
							str_AND_fail = str_AND_fail + 'SNA '
						str_skip_check = str_skip_check + 'SNA '
					
					# SZL - Skip on Zero Link: check bit 7
					if IR_str[7] == '1':
						# if LR is non-zero, then condition not satisfied,
						# so do not skip
						if self.regs['LR'] != 0:
							curr_branch_taken = False
							str_AND_fail = str_AND_fail + 'SZL '
						str_skip_check = str_skip_check + 'SZL '
					
					# Debug print
					if self.debug_v and (curr_branch_type != BRANCH_TYPE['NO_BRANCH']):
						if curr_branch_taken:
							print (" -- AND group condition(s) met.")
						else:
							print (" -- AND group condition(s) not met: {0}".format(str_AND_fail))
						print ("    Checked for: {0}".format(str_skip_check))
						
				# CLA - Clear Accumulator: check if bit 4 is set
				if IR_str[4] == '1':
					self.regs['AC'] = 0
					if self.debug_v:
						print (" -- CLA - Clear Accumulator")
						print ("                NEW AC: {0:04o}".format(self.regs['AC']))
				
				# OSR - Or Switch Register with Accumulator: check if bit 9 is set
				if IR_str[9] == '1':
					if self.debug_v:
						print (" -- OSR - Or Switch Register with Accumulator")
						print ("           Previous AC: {0:04o}".format(self.regs['AC']))
						print ("           Previous SR: {0:04o}".format(self.regs['SR']))
					
					self.regs['AC'] = self.regs['AC'] | self.regs['SR']
					
					if self.debug_v:
						print ("                NEW AC: {0:04o}".format(self.regs['AC']))
				
				# HLT - HaLT: check if bit 10 is set
				if IR_str[10] == '1':
					self.flagHLT = True
					if self.debug_v:
						print (" -- HLT - Halt")
				
				# If a Group 2 branch instruction was given:
				if curr_branch_type != BRANCH_TYPE['NO_BRANCH']:
					# Determine if a Group 2 branch was taken, 
					# and if so, increment the PC
					if curr_branch_taken:
						self.regs['PC'] = self.regs['PC'] + 1
					
					# Update Branch Statistics as needed
					# Write to branch trace file, providing current PC, opcode string,
					# target address, branch type, and flag indicating branch taken/not taken
					self.write_branch_trace(self.regs['prevPC'], self.opcode_str, 
						self.regs['PC'], curr_branch_type, curr_branch_taken)
			
			# Else, bit 11 is set to 1: Group 3 Microinstructions
			else:
				# These are not implemented, so should be noted as 
				# illegal/unrecognized instructions
				print ("WARNING: Group 3 MicroOp called at PC = [{0:04o}]. Group 3 MicroOps not enabled in simulation.".format(self.regs['PC']))
		
		# Set the flags for which branch condition tests were made
		self.branch_tests = str_skip_check
		self.branch_OR_success = str_OR_success
		self.branch_AND_fail = str_AND_fail
				
	#-------------------------------------
	# Function: op_default
	# Description: "Executes" a NOP.
	def op_default(self):
		# do nothing, print warning that illegal opcode was given
		print ("WARNING: Invalid opcode encountered at PC: [{0:04o}]".format(self.regs['prevPC']))

	#-------------------------------------
	# Function: execute
	# Description: Executes the next instruction (found at the
	#    address specified by the PC).
	# Return Value: 0 -> execution completed successfully,
	#                    and no HLT was encountered
	#               1 -> HLT microinstruction was given.
	def execute(self):
		# STEP 0: Clear all locations referenced in memory by last instruction
		for type in self.GUI_mem_highlight_types:
			self.GUI_mem_ref[type] = -1
		# Set default string for GUI_IR_bit_disp_type
		self.GUI_IR_bit_disp_type='DEFAULT'
		# Initialize breakpoint flag as false 
		self.flag_breakpoint = False
		self.flagHLT = False
		
		# STEP 1: Fetch the current instruction, increment PC
		self.regs['IR'] = self.read_mem(self.regs['PC'],'FETCH')
		self.GUI_mem_ref['instr_fetch'] = self.regs['PC']	# save location of fetched instr
		self.regs['prevPC'] = self.regs['PC'] 
		self.regs['PC'] = self.regs['PC'] + 1

		# STEP 2: Decode the current instruction
		# determine the opcode
		self.opcode = self.regs['IR'] >> (PDP8_WORD_SIZE - PDP8_OPCODE_SIZE)
		self.opcode_str = OPCODE_NAME[self.opcode]
		op_str = self.opcode_str 	# shorter name for easier use, read-only
		
		# Update Overall Instruction Count
		self.instr_count['all'] = self.instr_count['all'] + 1
		self.instr_count[op_str] = self.instr_count[op_str]+1
		
		if self.debug:	# Print basic debug for instruction number, PC, IR
			print (" ")
			print ("================== INSTRUCTION #{0:-1d} : {1} ==================".format(self.instr_count['all'], self.opcode_str))
			print ("             PC / IR: {0:04o} / {1:04o}".format(self.regs['prevPC'], self.regs['IR']))
		
		# STEP 2b: Determine the Effective Address
		if (self.opcode >= 0 and self.opcode < 6):
			self.regs['eaddr'] = self.calc_eaddr()
		else:
			self.regs['eaddr'] = 0
		
		# STEP 3: Execute Current Instruction
		self.opcode_exec.get(self.opcode,self.op_default)()
		# This will call the corresponding function based on the current opcode.
		
		# STEP 4: Update Cycle Stats for Opcodes
		self.cycle_count['all'] = self.cycle_count['all'] + OPCODE_CYCLES[op_str]
		self.cycle_count[op_str] = self.cycle_count[op_str]+OPCODE_CYCLES[op_str]
		
		# Print the basic debug values for register/memory values after instruction executes
		if self.debug:
			print ("             LR / AC: {0:1o} / {1:04o}".format(self.regs['LR'], self.regs['AC']))
			print ("   EFFECTIVE ADDRESS: {0:04o}".format(self.regs['eaddr']))
			print ("   VALUE @ EFF. ADDR: {0:04o}".format(self.mem[self.regs['eaddr']]))
		
		# Update all string values for GUI display
		# IR,PC,AC,SR,eaddr,mem_eaddr,prevPC:
		for reg in self.reg_names:
			for type in self.GUI_format_types:
				self.GUI_reg_vals[reg][type].set(self.format_str(self.regs[reg],type))
		# IR binary values:
		tmp_val = self.format_str(self.regs['IR'],'bin')
		for i in range(PDP8_WORD_SIZE):
			self.GUI_IR_bin_val[i].set(tmp_val[i])
		# LR:
		self.GUI_LR_val.set(int(self.regs['LR']))
		# Opcode:
		self.GUI_opcode_str.set(self.opcode_str)
		# Bit Position Labels:
		for i in range(PDP8_WORD_SIZE):
			self.GUI_IR_bit_lbl[i].set(BIT_POS_LBL[self.GUI_IR_bit_disp_type][i])

		# check if there was a breakpoint set on this instruction
		# (if so, stop execution AFTER this instruction completes)
		if self.mem_breakpoint[self.regs['PC']].get():
			self.flag_breakpoint = True
			if self.debug:
				print ("-Breakpoint: Next PC flagged with breakpoint at {0:04o}".format(self.regs['PC'])) 
		# check for any other breakpoints that might have been 
		# touched on memory read/write accesses
		else:
			# exclude the 'instr_fetch' type
			other_types = ['eaddr_read','eaddr_write','mem_read','mem_write']
			for type in other_types:
				if self.GUI_mem_ref[type] != -1:
					# check if accessed memory has a breakpoint set 
					if self.mem_breakpoint[self.GUI_mem_ref[type]].get():
						self.flag_breakpoint = True
						if self.debug:
							print ("--Breakpoint type: {0} at address: {1:04o}".format(type,self.GUI_mem_ref[type]))
		
		# return the HALT flag
		return self.flagHLT
	
	#-------------------------------------
	# Function: print_statistics
	# Description: Prints out summary statistics for: 
	#     1. number of instructions executed (total and per opcode)
	#     2. number of clock cycles used (total and per opcode)
	#     3. number of branches taken, not taken (total and per opcode)
	def print_statistics(self):
		# PRINT OUT STATISTICS AND MEMORY IMAGE
		# Print words in memory at all valid memory locations.
		if self.debug:
			print ("\n=====================================================")
			print (" RESULTING MEMORY:")
			for i in range(0, MEM_SIZE - 1):
				if self.memvalid[i] == 1:
					print ("Address: {0:04o}  Value: {1:04o}".format(i, self.mem[i]))
			
		
		print ("\n=====================================================")
		print ("STATISTICS\n");
		print ("CPU Clocks Used: {0:-1d}".format(self.cycle_count['all']))
		print ("Total Instructions: {0:-1d}".format(self.instr_count['all']))
		print (" ")
		print ("   Type    # of Instrs   # of Cycles")
		print ("   ----    -----------   -----------")
		print ("    AND    {0:10d}  {1:12d}".format(self.instr_count['AND'],self.cycle_count['AND']))
		print ("    TAD    {0:10d}  {1:12d}".format(self.instr_count['TAD'],self.cycle_count['TAD']))
		print ("    ISZ    {0:10d}  {1:12d}".format(self.instr_count['ISZ'],self.cycle_count['ISZ']))
		print ("    DCA    {0:10d}  {1:12d}".format(self.instr_count['DCA'],self.cycle_count['DCA']))
		print ("    JMS    {0:10d}  {1:12d}".format(self.instr_count['JMS'],self.cycle_count['JMS']))
		print ("    JMP    {0:10d}  {1:12d}".format(self.instr_count['JMP'],self.cycle_count['JMP']))
		print ("     IO    {0:10d}  {1:12d}".format(self.instr_count['IO'],self.cycle_count['IO']))
		print ("     UI    {0:10d}  {1:12d}".format(self.instr_count['UI'],self.cycle_count['UI']))
		print ("   ----    -----------   -----------")
		print ("  TOTAL    {0:10d}  {1:12d}".format(self.instr_count['all'],self.cycle_count['all']))
		print (" ")
		print ("=====================================================")
		print ("BRANCH STATISTICS\n")
		print ("Total Number of Branches: {0} Taken / {1} Not Taken".format(
			self.branch_uncond_count['all']+self.branch_cond_t_count['all'],
			self.branch_cond_nt_count['all']))
		print ("\nUnconditional Branches:\n")
		print ("     Opcode     Taken ")
		print ("     ------    ------- ")
		print ("       JMS     {0:6d}".format(self.branch_uncond_count['JMS']))
		print ("       JMP     {0:6d}".format(self.branch_uncond_count['JMP']))
		print ("       UI      {0:6d}".format(self.branch_uncond_count['UI']))
		print ("     ------    ------- ")
		print ("      TOTAL    {0:6d}".format(self.branch_uncond_count['all']))
		print ("\nConditional Branches:\n")
		print ("     Opcode     Taken    Not Taken   Total #")
		print ("     ------    -------   ---------   -------")
		print ("       ISZ     {0:6d}    {1:8d}    {2:6d}".format(
			self.branch_cond_t_count['ISZ'],
			self.branch_cond_nt_count['ISZ'],
			(self.branch_cond_t_count['ISZ']+self.branch_cond_nt_count['ISZ'])))
		print ("       UI      {0:6d}    {1:8d}    {2:6d}".format(
			self.branch_cond_t_count['UI'],
			self.branch_cond_nt_count['UI'],
			(self.branch_cond_t_count['UI']+self.branch_cond_nt_count['UI'])))
		print ("     ------    -------   ---------   -------")
		print ("      TOTAL    {0:6d}    {1:8d}    {2:6d}".format(
			self.branch_cond_t_count['all'],
			self.branch_cond_nt_count['all'],
			(self.branch_cond_t_count['all']+self.branch_cond_nt_count['all'])))
		print (" ")
		print ("=====================================================\n")

# END CLASS DEFINITION FOR PDP8_ISA
#==============================================================================

#==============================================================================
# GUI APP CLASS DEFINITIONS
#----------------------------
class App:
	def __init__(self,root,input_filename,debug,debug_v,SR_val):
		self.root = root
		self.root.title("PDP-8 ISA Simulator")
		self.input_filename = ''
		
		self.PDP8 = PDP8_ISA(debug,debug_v,SR_val) # instantiate a PDP8 object
			
		self.view_format_type = 'oct'	# by default, display in octal
		
		# background colors for highlighting memory
		self.mem_color_types = {
			'instr_fetch': "#ffb700",
			'eaddr_read': "#54b69a",
			'eaddr_write': "#8171cc",
			'mem_read': "#007785",
			'mem_write': "#cc71a9",
			'default': "#d9d7e0"
		}
		# build styles
		self.mem_color_styles = {}
		for type in self.PDP8.GUI_mem_highlight_types:
			s = ttk.Style()
			s.configure(type+'.TLabel', background=self.mem_color_types[type])
			self.mem_color_styles[type] = s
		s = ttk.Style()
		s.configure('default.TLabel', background=self.mem_color_types['default'])
		self.mem_color_styles['default'] = s
		
		#------------------------
		# BUILD LAYOUT FOR GUI:
		# Main frame
		self.mainframe = ttk.Frame(self.root, padding=(5, 5, 10, 10))
		self.mainframe.grid(sticky='nwse')
		#for column in range(6):
		#	self.mainframe.columnconfigure(column, weight=1)
		self.mainframe.rowconfigure(1, weight=1)
		
		# Frame for menu buttons
		self.menubar = ttk.Frame(self.mainframe, padding = (2,2,2,2))
		self.menubar.grid(sticky='ew')
		
		# Menu bar buttons:
		s = ttk.Style()
		# Open File button
		s.configure('Open.TButton', foreground='midnight blue')
		self.btn_open = ttk.Button(self.menubar,
							text='OPEN FILE', style='Open.TButton',
							command=self.open_file)
		self.btn_open.grid(in_=self.menubar,row=0,column=0)
		# Start button
		s.configure('Start.TButton', foreground='purple4')
		self.btn_start = ttk.Button(self.menubar,
							text="START/CONTINUE", style='Start.TButton',
							command=self.execute)
		self.btn_start.grid(in_=self.menubar,row=0,column=1)
		self.btn_start['state']='disabled'
		# Step button
		s.configure('Step.TButton', foreground='DarkOrchid4')
		self.btn_step = ttk.Button(self.menubar,
							text="STEP/NEXT", style='Step.TButton',
							command=self.execute_next)
		self.btn_step.grid(in_=self.menubar,row=0,column=2)
		self.btn_step['state']='disabled'
		# Restart button
		s.configure('Restart.TButton', foreground='dark goldenrod')
		self.btn_restart = ttk.Button(self.menubar,
							text="RESTART", style='Restart.TButton',
							command=self.restart)
		self.btn_restart.grid(in_=self.menubar,row=0,column=3)
		self.btn_restart['state']='disabled'
		# Clear Breakpoints button
		s.configure('ClearBreakpoints.TButton', foreground='OrangeRed3')
		self.btn_clearbreakpoints = ttk.Button(self.menubar,
							text="CLEAR BREAKPOINTS", style='ClearBreakpoints.TButton',
							command=self.clear_breakpoints)
		self.btn_clearbreakpoints.grid(in_=self.menubar,row=0,column=4)
		#self.btn_clearbreakpoints['state']='disabled'
		# View Stats button
		s.configure('Stats.TButton', foreground='indian red')
		self.btn_stats = ttk.Button(self.menubar,
							text="VIEW STATS", style='Stats.TButton',
							command=self.view_stats)
		self.btn_stats.grid(in_=self.menubar,row=0,column=5)
		# Exit button
		s.configure('Exit.TButton', foreground='firebrick4')
		self.btn_exit = ttk.Button(self.menubar,
							text="EXIT", style='Exit.TButton',
							command=self.root.quit)
		self.btn_exit.grid(in_=self.menubar,row=0,column=6)
		
		# Separator between menubar and main part of window
		self.separator = ttk.Frame(self.mainframe, borderwidth=2, relief='sunken')
		self.separator.grid(in_=self.mainframe, column=0, row=1, columnspan=6, sticky='ew')
		
		# Frame for main part of window below menu buttons
		self.sub_frame = ttk.LabelFrame(self.mainframe,padding=(2, 2, 2, 2),text="Simulation")
		self.sub_frame.grid(column=0, row=2, columnspan=6, sticky='nsew')
		
		# sub frame components
		# column 0:
		self.frame_SR = ttk.LabelFrame(self.sub_frame, text="Switch Register", padding=(5, 5, 5, 5))
		self.frame_SR.grid(column=0,row=0,sticky='ew')
		self.sep3a = ttk.Frame(self.sub_frame, padding=(0,0,0,0))
		self.sep3a.grid(column=0,row=1,sticky='ns')
		ttk.Label(self.sep3a, text='').grid(in_=self.sep3a,row=0,column=0)
		self.frame_last_instr = ttk.LabelFrame(self.sub_frame, text="Last Executed Instruction", padding=(5, 5, 5, 5))
		self.frame_last_instr.grid(column=0,row=2, sticky='ew')
		self.sep3b = ttk.Frame(self.sub_frame, padding=(0,0,0,0))
		self.sep3b.grid(column=0,row=3,sticky='ns')
		ttk.Label(self.sep3b, text='').grid(in_=self.sep3b,row=0,column=0)
		self.frame_regs = ttk.LabelFrame(self.sub_frame, text="Current Register Values", padding=(10, 10, 10, 10))
		self.frame_regs.grid(column=0,row=4,sticky='ew')
		
		# column 1: Current Memory Image frame
		self.memframe_main = ttk.LabelFrame(self.sub_frame, text="Current Memory Image", padding=(5,5,5,5))
		self.memframe_main.grid(column=1,row=0,rowspan=5,sticky='nsew')
		# memframe1 contains the column header frame
		self.memframe1 = ttk.Frame(self.memframe_main)
		self.memframe1.grid(column=0,row=0,sticky='nw')
		# create the column headers
		self.mem_header = ttk.Frame(self.memframe1)
		self.mem_header.pack() #expand=True
		self.mem_header_col0 = ttk.Label(self.mem_header, text='Breakpoint', width=10, 
			borderwidth="0").grid(row=0, column=0,sticky='w')
		self.mem_header_col2 = ttk.Label(self.mem_header, text="Address", width=19,
			borderwidth="0").grid(row=0, column=1,sticky='w')
		self.mem_header_col3 = ttk.Label(self.mem_header, text="Value", width=15).grid(row=0, column=2,sticky='w')
		# memframe2 contains the scrollable canvas
		self.memframe2 = ttk.Frame(self.memframe_main)
		self.memframe2.grid(column=0,row=1,sticky='nw')
		self.canvas = tk.Canvas(self.memframe2, borderwidth=0) # background="#ffffff"
		self.memtable = ttk.Frame(self.canvas)
		self.vsb = tk.Scrollbar(self.memframe2, orient="vertical", command=self.canvas.yview)
		self.canvas.configure(yscrollcommand=self.vsb.set)
		
		self.canvas.pack(side="left", fill='y') #fill="both", expand=True
		self.vsb.pack(side="right", fill='y')
		self.canvas.create_window((0,0), window=self.memtable, anchor="nw")
		# resize scrollbar
		self.memtable.bind("<Configure>", self.OnFrameConfigure)
		# build memory table
		self.populateMemTable()
		
		# separator between scrollable canvas and color key table
		self.memframe_sep = ttk.Frame(self.memframe_main) # borderwidth=2, relief='flat'
		self.memframe_sep.grid(in_=self.memframe_main, column=1, row=0, sticky='ns',rowspan=2)
		self.memframe_sep_lbl = ttk.Label(self.memframe_sep,text="").grid(in_=self.memframe_sep,column=0,row=0,sticky='nsew')
		
		# memframe3 contains the color key for the memory image 
		self.memframe3 = ttk.Frame(self.memframe_main)
		self.memframe3.grid(column=2,row=0,rowspan=2,sticky='nw')
		# row 0: radio button options for view format type 
		self.mem_disp_type_frame = ttk.LabelFrame(self.memframe3, text="Value Display Format", padding=(5,5,5,5))
		self.mem_disp_type_frame.grid(column=0,row=0,sticky='nw')
		self.strVar_DispType = tk.StringVar()
		self.strVar_DispType.set('oct')	# default format is octal
		types = [
			('Octal', 'oct'),
			('Hexadecimal', 'hex'),
			('Binary', 'bin')
		]
		for text, mode in types:
			radio_btn = tk.Radiobutton(self.mem_disp_type_frame, text=text,
				variable=self.strVar_DispType, value = mode,
				command=self.changed_disp_val_format)
			radio_btn.pack(anchor='w')
		# row 1: space
		self.mem_sep1 = ttk.Frame(self.memframe3) # borderwidth=2, relief='flat'
		self.mem_sep1.grid(in_=self.memframe3, column=0, row=1, sticky='ew')
		self.mem_sep1_lbl = ttk.Label(self.mem_sep1,text="").grid(in_=self.mem_sep1,column=0,row=0,sticky='nsew')
		# row 2: color key
		self.mem_colorkey_frame = ttk.LabelFrame(self.memframe3, text="Memory Color Key", padding=(5,5,5,5))
		self.mem_colorkey_frame.grid(column=0,row=2,sticky='nw')
		# build color table
		self.mem_color_table_row1 = ttk.Label(self.mem_colorkey_frame, text="Instruction Fetch", padding = (10,5,10,5), 
			style='instr_fetch.TLabel', anchor='center').grid(in_=self.mem_colorkey_frame,column=0,row=0,sticky='nsew')
		self.mem_color_table_sep1 = ttk.Frame(self.mem_colorkey_frame,borderwidth=2, relief='flat')
		self.mem_color_table_sep1.grid(in_=self.mem_colorkey_frame, column=0, row=1, sticky='ns')
		self.mem_color_table_row2 = ttk.Label(self.mem_colorkey_frame, text="Addressing Mode Read", padding = (10,5,10,5), 
			style='eaddr_read.TLabel', anchor='center').grid(in_=self.mem_colorkey_frame,column=0,row=2,sticky='nsew')
		self.mem_color_table_sep2 = ttk.Frame(self.mem_colorkey_frame,borderwidth=2, relief='flat')
		self.mem_color_table_sep2.grid(in_=self.mem_colorkey_frame, column=0, row=3, sticky='ns')
		self.mem_color_table_row3 = ttk.Label(self.mem_colorkey_frame, text="Addressing Mode Write", padding = (10,5,10,5), 
			style='eaddr_write.TLabel', anchor='center').grid(in_=self.mem_colorkey_frame,column=0,row=4,sticky='nsew')
		self.mem_color_table_sep3 = ttk.Frame(self.mem_colorkey_frame,borderwidth=2, relief='flat')
		self.mem_color_table_sep3.grid(in_=self.mem_colorkey_frame, column=0, row=5, sticky='ns')
		self.mem_color_table_row4 = ttk.Label(self.mem_colorkey_frame, text="Memory Read", padding = (10,5,10,5), 
			style='mem_read.TLabel', anchor='center').grid(in_=self.mem_colorkey_frame,column=0,row=6,sticky='nsew')
		self.mem_color_table_sep4 = ttk.Frame(self.mem_colorkey_frame,borderwidth=2, relief='flat')
		self.mem_color_table_sep4.grid(in_=self.mem_colorkey_frame, column=0, row=7, sticky='ns')
		self.mem_color_table_row5 = ttk.Label(self.mem_colorkey_frame, text="Memory Write", padding = (10,5,10,5), 
			style='mem_write.TLabel', anchor='center').grid(in_=self.mem_colorkey_frame,column=0,row=8,sticky='nsew')
		self.mem_color_table_sep5 = ttk.Frame(self.mem_colorkey_frame,borderwidth=2, relief='flat')
		self.mem_color_table_sep5.grid(in_=self.mem_colorkey_frame, column=0, row=9, sticky='ns')
		
		# SR frame
		self.lbl_SR_name = ttk.Label(self.frame_SR, text="SR:", padding=(2,2,2,5)).grid(in_=self.frame_SR,row=0,column=0,sticky='E', rowspan=2)
		self.lbl_SR_val = ttk.Label(self.frame_SR, textvariable=self.PDP8.GUI_reg_vals['SR'][self.view_format_type], padding=(2,2,2,2), relief='solid').grid(in_=self.frame_SR,row=0,column=1, rowspan=2)
		self.SR_chk_box = []
		self.SR_bin_val = []
		SR_bin_start = bin(self.PDP8.regs['SR'])
		SR_bin_start = SR_bin_start[2:]	# trim leading '0b'
		while len(SR_bin_start) < PDP8_WORD_SIZE:
			SR_bin_start = '0'+SR_bin_start
		ttk.Label(self.frame_SR, padding=(25,2,5,2), text="Bit #:").grid(in_=self.frame_SR,row=0,column=2)
		for i in range(PDP8_WORD_SIZE):
			int_var = tk.IntVar()
			#self.SR_bin_val[i] = int(SR_bin_start[i])
			ttk.Label(self.frame_SR, text=u"%s" % str(i), padding = (0,3,0,3), anchor='center').grid(in_=self.frame_SR,row=0,column=(i+3),sticky='ns')
			self.SR_chk_box.append(ttk.Checkbutton(self.frame_SR,
				command=self.changed_SR_val, variable=int_var,
				onvalue=1, offvalue=0, padding=5))
			self.SR_chk_box[i].grid(in_=self.frame_SR,row=1,column=(i+3),sticky='ew')
			self.SR_chk_box[i].state = int(SR_bin_start[i])
			self.SR_bin_val.append(int_var)
		
		# Last Executed Instruction Labels
		self.lbl_prevPC_name = ttk.Label(self.frame_last_instr, text="Previous PC:", padding=(2,4,10,4)).grid(in_=self.frame_last_instr,row=0,column=0, sticky='E')
		self.lbl_prevPC_val = ttk.Label(self.frame_last_instr, textvariable=self.PDP8.GUI_reg_vals['prevPC'][self.view_format_type], padding=(2,2,2,2), relief='solid').grid(in_=self.frame_last_instr,row=0,column=1,sticky='W')
		self.lbl_IR_name = ttk.Label(self.frame_last_instr, text="IR:", padding=(2,4,10,4)).grid(in_=self.frame_last_instr,row=1, column=0, sticky='E')
		self.lbl_IR_val = ttk.Label(self.frame_last_instr, textvariable=self.PDP8.GUI_reg_vals['IR'][self.view_format_type], padding=(2,2,2,2), relief='solid').grid(in_=self.frame_last_instr,row=1,column=1,sticky='W')
		self.lbl_opcode_name = ttk.Label(self.frame_last_instr, text="OPCODE:", 
			padding=(25,2,10,2)).grid(in_=self.frame_last_instr,row=1, column=2, sticky='E')
		self.lbl_opcode_val = ttk.Label(self.frame_last_instr, textvariable=self.PDP8.GUI_opcode_str, 
			width = 5, padding=(2,2,2,2), relief='solid').grid(in_=self.frame_last_instr,row=1,column=3,sticky='W')
		# Display table of binary bits for IR value
		self.frame_bin_IR = ttk.LabelFrame(self.frame_last_instr,text="IR Value Displayed in Binary Bits", padding=(5, 5, 5, 5))
		self.frame_bin_IR.grid(row=2,column=0,columnspan=4,padx=3,pady=10)
		self.IR_bin_lbl = []
		self.IR_bin_bit_lbl = []
		s = ttk.Style()
		s.configure('BitNum.TLabel', background='LightSteelBlue3')
		s.configure('BitVal.TLabel', background='azure3')
		s.configure('BitName.TLabel', background='LightSteelBlue3')
		for i in range(PDP8_WORD_SIZE):
			ttk.Label(self.frame_bin_IR, text=u"%s" % str(i),
				padding = (10,5,10,5), style='BitNum.TLabel', 
				anchor='center').grid(in_=self.frame_bin_IR,row=0,column=2*i,sticky='nsew')
			# vertical separator
			self.separator1a = ttk.Frame(self.frame_bin_IR,borderwidth=2, relief='flat')
			self.separator1a.grid(in_=self.frame_bin_IR, column=2*i+1, row=0, sticky='ns')
			#ttk.Label(self.frame_bin_IR, text='', padding = (1,0,0,0)).grid(in_=self.frame_bin_IR,row=0,column=2*i+1,sticky='nsew')
			self.IR_bin_lbl.append(ttk.Label(self.frame_bin_IR,
				textvariable=self.PDP8.GUI_IR_bin_val[i], padding = (10,5,10,5), style='BitVal.TLabel', 
				anchor='center').grid(in_=self.frame_bin_IR,row=2,column=2*i,sticky='nsew'))
			# vertical separator
			self.separator1b = ttk.Frame(self.frame_bin_IR,borderwidth=2, relief='flat')
			self.separator1b.grid(in_=self.frame_bin_IR, column=2*i+1, row=1, sticky='ns')
			#ttk.Label(self.frame_bin_IR, text='', padding = (1,0,0,0)).grid(in_=self.frame_bin_IR,row=2,column=2*i+1,sticky='nsew')
			self.IR_bin_lbl.append(ttk.Label(self.frame_bin_IR, width = 4,	# FIXED WIDTH SET HERE
				textvariable=self.PDP8.GUI_IR_bit_lbl[i], padding = (10,5,10,5), style='BitName.TLabel',
				anchor='center').grid(in_=self.frame_bin_IR,row=4,column=2*i,sticky='nsew'))
			# vertical separator
			self.separator1c = ttk.Frame(self.frame_bin_IR,borderwidth=2, relief='flat')
			self.separator1c.grid(in_=self.frame_bin_IR, column=2*i+1, row=2, sticky='ns')
			#ttk.Label(self.frame_bin_IR, text='', padding = (1,0,0,0)).grid(in_=self.frame_bin_IR,row=4,column=2*i+1,sticky='nsew')
		# horizontal separators
		self.separator2a = ttk.Frame(self.frame_bin_IR,borderwidth=2, relief='flat')
		self.separator2a.grid(in_=self.frame_bin_IR, column=0, row=1, columnspan=2*PDP8_WORD_SIZE, sticky='ew')
		self.separator2b = ttk.Frame(self.frame_bin_IR, borderwidth=2, relief='flat')
		self.separator2b.grid(in_=self.frame_bin_IR, column=0, row=3, columnspan=2*PDP8_WORD_SIZE, sticky='ew')
		#ttk.Label(self.frame_bin_IR, padding = (0,1,0,0)).grid(in_=self.frame_bin_IR,row=1,column=0,columnspan=2*PDP8_WORD_SIZE,sticky='nsew')
		#ttk.Label(self.frame_bin_IR, padding = (0,1,0,0)).grid(in_=self.frame_bin_IR,row=3,column=0,columnspan=2*PDP8_WORD_SIZE,sticky='nsew')
		
		# Register Value Labels
		# Last Executed Instruction Labels
		# row 0
		self.lbl_PC_name = ttk.Label(self.frame_regs, text="PC:", padding=(2,4,10,4)).grid(in_=self.frame_regs,row=0,column=0, sticky='E')
		self.lbl_PC_val = ttk.Label(self.frame_regs, textvariable=self.PDP8.GUI_reg_vals['PC'][self.view_format_type], padding=(2,2,2,2), relief='solid').grid(in_=self.frame_regs,row=0,column=1,sticky='W')
		# row 1
		self.lbl_LR_name = ttk.Label(self.frame_regs, text="LR:", padding=(2,4,10,4)).grid(in_=self.frame_regs,row=1, column=0, sticky='E')
		self.lbl_LR_val = ttk.Label(self.frame_regs, textvariable=self.PDP8.GUI_LR_val, padding=(2,2,2,2), relief='solid').grid(in_=self.frame_regs,row=1,column=1,sticky='W')
		self.lbl_AC_name = ttk.Label(self.frame_regs, text="AC:", padding=(25,4,10,4)).grid(in_=self.frame_regs,row=1, column=2, sticky='E')
		self.lbl_AC_val = ttk.Label(self.frame_regs, textvariable=self.PDP8.GUI_reg_vals['AC'][self.view_format_type], padding=(2,2,2,2), relief='solid').grid(in_=self.frame_regs,row=1,column=3,sticky='W')
		# row 2
		self.lbl_eaddr_name = ttk.Label(self.frame_regs, text="Effective Addr:", padding=(2,4,10,4)).grid(in_=self.frame_regs,row=2, column=0, sticky='E')
		self.lbl_eaddr_val = ttk.Label(self.frame_regs, textvariable=self.PDP8.GUI_reg_vals['eaddr'][self.view_format_type], padding=(2,2,2,2), relief='solid').grid(in_=self.frame_regs,row=2,column=1,sticky='W')
		self.lbl_mem_eaddr_name = ttk.Label(self.frame_regs, text="Mem[EAddr]:", padding=(25,4,10,4)).grid(in_=self.frame_regs,row=2, column=2, sticky='E')
		self.lbl_mem_eaddr_val = ttk.Label(self.frame_regs, textvariable=self.PDP8.GUI_reg_vals['mem_eaddr'][self.view_format_type], padding=(2,2,2,2), relief='solid').grid(in_=self.frame_regs,row=2,column=3,sticky='W')
		
		# END LAYOUT FOR GUI
		#---------------------
		
		# Check if a filename was given from command line, 
		# if so, load memory image.
		if input_filename != '':
			# set filename and restart()
			self.input_filename = input_filename
			self.restart()

	# End __init__()
	#-------------------------------------

	
	#-------------------------------------
	# Function: populateMemTable
	# Description: This function redraws the memory table
	def populateMemTable(self):
		# first, delete any existing widgets in memtable
		for child in self.memtable.winfo_children():
			child.destroy()
		
		# each entry in this list is a list of widgets on 
		# the current row in the memory table.
		self.mem_row_items = []
		curr_row = 0	# index for current row in GUI table
		
		# loop through all memory values, and display and 
		# link breakpoint button and label values for all
		# valid entries
		#for i in range(MEM_SIZE):
		#	if self.PDP8.memvalid[i]:
		
		# only need to loop through list of valid addresses
		for i in self.PDP8.mem_valid_addrlist:
			self.mem_row_items.append([])
			
			# check if current address = PC, if so, 
			# display the arrow in first column 
			if i == self.PDP8.regs['PC']:				
				# Arrow item for indicating current PC
				self.mem_row_items[curr_row].append(tk.Canvas(self.memtable,width=26,height=25))
				self.mem_row_items[curr_row][0].grid(row=curr_row,column=0, sticky='ns')
				self.mem_row_items[curr_row][0].create_polygon(0,11, 15,11, 
					15,5, 25,14, 15,23, 15,18, 0,18,
					fill='forest green')
			else:	# otherwise, use empty label in first column
				self.mem_row_items[curr_row].append(ttk.Label(self.memtable, text='', width=2, 
					borderwidth="0").grid(row=curr_row, column=0))
			# second column = checkbutton for breakpoint
			# Note: no command specified, since only need the value updated
			self.mem_row_items[curr_row].append(ttk.Checkbutton(self.memtable,
				variable=self.PDP8.mem_breakpoint[i], onvalue=1, offvalue=0, padding=5))
			self.mem_row_items[curr_row][1].grid(in_=self.memtable,row=curr_row,column=1,sticky='ew')
			
			# determine background color for the last two columns
			style_name = 'default.TLabel'
			#bgcolor = self.mem_color_types['default']
			for type in self.PDP8.GUI_mem_highlight_types:
				if i == self.PDP8.GUI_mem_ref[type]:
					style_name=type+'.TLabel'
					#bgcolor = self.mem_color_types['type']
			
			# third column = address label
			addr_str = self.PDP8.format_str(i,self.view_format_type)
			self.mem_row_items[curr_row].append(ttk.Label(self.memtable, 
				text=u'%s' % addr_str, padding = (10,5,10,5), width=15,
				style=style_name #, borderwidth="1", relief="solid"
				).grid(row=curr_row, column=2,sticky='w'))
			# fourth column = vertical separator
			self.mem_row_items[curr_row].append(ttk.Frame(self.memtable,borderwidth=2, relief='flat'))
			self.mem_row_items[curr_row][3].grid(in_=self.memtable, column=3, row=curr_row, sticky='ns')
			# fourth column = value label
			self.mem_row_items[curr_row].append(ttk.Label(self.memtable, width=15, 
				padding = (10,5,10,5), style=style_name, 
				textvariable=self.PDP8.GUI_mem_vals[i][self.view_format_type]).grid(row=curr_row, column=4,sticky='w'))
			
			curr_row = curr_row + 1 	# increment GUI table row number

			# add separator line
			self.mem_row_items.append([])
			self.mem_row_items[curr_row].append(ttk.Frame(self.memtable,borderwidth=2, relief='flat'))
			self.mem_row_items[curr_row][0].grid(in_=self.memtable, column=0, row=curr_row, columnspan=5, sticky='ew')
			curr_row = curr_row + 1
				
	#-------------------------------------
	# Function: open_file
	# Description: Opens the dialog window for file selection,
	#	allows user to select file. 
	#	If file_name is not empty, then save file name,
	#	clear all breakpoints and then attempt restart()
	def open_file(self):
		file_name = askopenfilename()
		if file_name != '':
			self.input_filename = file_name
			self.clear_breakpoints()
			# restart
			self.restart()
	
	#-------------------------------------
	# Function: clear_breakpoints
	# Description: Clears all active breakpoints
	def clear_breakpoints(self):
		# clear all breakpoints 
		for i in range(MEM_SIZE):
			self.PDP8.mem_breakpoint[i].set(0)
	
	#-------------------------------------
	# Function: execute
	# Description: Execute instructions, until 
	#	a breakpoint or a HALT instruction is encountered
	def execute(self):
		# enable restart button 
		self.btn_restart['state']='normal'
		# disable the SR register checkbuttons 
		for i in range(PDP8_WORD_SIZE):
			self.SR_chk_box[i].configure(state='disabled')
			
		self.PDP8.open_tracefiles()	# open trace files for append
		flag_break = False
		while not(flag_break):
			flag_halt = self.PDP8.execute()
			if self.PDP8.flag_breakpoint or flag_halt:
				flag_break = True
			#print ("halt: ",flag_halt," break: ",flag_break)
		self.PDP8.close_tracefiles()	# close trace files
		
		# redraw memory table
		self.populateMemTable()
		
		# if halt instruction was given, 
		# disable continue and step buttons, 
		# and print statistics
		if flag_halt:
			self.btn_start['state']='disabled'
			self.btn_step['state']='disabled'
			self.PDP8.print_statistics()	# print statistics
	
	
	#-------------------------------------
	# Function: execute_next
	# Description: Executes the next instruction, 
	#	then stops
	def execute_next(self):
		# enable restart button 
		self.btn_restart['state']='normal'
		# disable the SR register checkbuttons 
		for i in range(PDP8_WORD_SIZE):
			self.SR_chk_box[i].configure(state='disabled')
			
		self.PDP8.open_tracefiles()	# open trace files for append
		flag_halt = self.PDP8.execute()
		self.PDP8.close_tracefiles()	# close trace files
		
		# redraw memory table
		self.populateMemTable()
		
		# if halt instruction was given, 
		# disable continue and step buttons, 
		# and print statistics
		if flag_halt:
			self.btn_start['state']='disabled'
			self.btn_step['state']='disabled'
			self.PDP8.print_statistics()	# print statistics
	
	#-------------------------------------
	# Function: restart
	# Description: Reloads memory image from 
	#	currently selected file, and enables/disables
	#	necessary buttons. 
	#	Note: Do NOT clear breakpoints on restart().
	def restart(self):
		# clear trace files and stats, and load the memory image
		self.PDP8.init_tracefiles()
		self.PDP8.clear_stats()
		self.PDP8.load_memory(self.input_filename)
		
		# redraw memory table
		self.populateMemTable()
		
		# enable start and step buttons 
		self.btn_start['state']='normal'
		self.btn_step['state']='normal'
		# disable restart button 
		self.btn_restart['state']='disabled'
		# enable the SR register checkbuttons 
		for i in range(PDP8_WORD_SIZE):
			self.SR_chk_box[i].configure(state='normal')
	
	#-------------------------------------
	# Function: view_stats
	# Description: Open dialog window to show current stats.
	def view_stats(self):
		print ("View Statistics")
		
	#-------------------------------------
	# Function: changed_disp_val_format
	# Description: Change the display type of all 
	#	full size registers and memory values
	def changed_disp_val_format(self):
		self.lbl_SR_val
		self.lbl_IR_val
		self.lbl_prevPC_val
		self.lbl_PC_val
		self.lbl_AC_val
		self.lbl_eaddr_val
		self.lbl_mem_eaddr_val
	
	#-------------------------------------
	# Function: changed_SR_val
	# Description: Updates the SR val when an SR checkbutton has been clicked.
	def changed_SR_val(self):
		# recalculate the current SR_val
		curr_SR = ''
		for i in range(PDP8_WORD_SIZE):
			if self.SR_bin_val[i].get() == 0:
				curr_SR = curr_SR + '0'
			else:
				curr_SR = curr_SR + '1'
		curr_SR_val = int(curr_SR,2)
		# save it to PDP8 class
		self.PDP8.regs['SR'] = curr_SR_val
		# update GUI string vals
		for type in self.PDP8.GUI_format_types:
			self.PDP8.GUI_reg_vals['SR'][type].set(self.PDP8.format_str(curr_SR_val,type))
		# update label display
		#self.lbl_SR_val.configure(text=u"%04o" % self.PDP8.SR)
	
	#-------------------------------------
	# Function: print_statistics
	# Description: Used to reset the scroll area to match size of the inner frame
	def OnFrameConfigure(self, event):
		self.canvas.configure(scrollregion=self.canvas.bbox("all"))

# END CLASS DEFINITION FOR GUI APP
#==============================================================================


#==============================================================================
# START OF PROGRAM 
#------------------
# parse the command line arguments
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
	
# GUI Testing
root = tk.Tk()
app = App(root,args.input_filename,args.debug,args.debug_verbose,SR)
root.mainloop()


# END OF PROGRAM
#==============================================================================