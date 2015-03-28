### Title: pdp8 module
###        for PDP-8 Instruction Set Simulator
### Date: March 24th, 2015
### Author: Elizabeth Reed
### Comments: This module contains the main functions and
###           data structures for the pdp-8 simulator
### Additional features that would be good to implement later:
###		1. Modify load_memory() so that it can parse EITHER 
###		   input file type, not just the verilog version.

# import the logarithmic function
from math import log

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
	0: 2,	# AND = 2 cycles
	1: 2, 	# TAD = 2 cycles 
	2: 2, 	# ISZ = 2 cycles
	3: 2, 	# DCA = 2 cycles 
	4: 2, 	# JMS = 2 cycles 
	5: 1, 	# JMP = 1 cycle
	6: 0, 	# IO = 0 cycles 
	7: 1 	# UI = 1 cycle 
}
# Number of cycles added for effective address calculation
EADDR_CYCLES = {
	'AutoIndex': 2,	# Auto-Indexing: 2 additional cycles 
	'Indirect': 1 	# Indirect Addressing: 1 additional cycle  
}

#--------------------------------------
# PDP8 CLASS
#--------------------------
class PDP8(object):
	def __init__(self,debug,debug_verbose,SR):
		self.debug = debug		# debug display flag
		self.debug_v = debug_verbose # verbose debug display flag
		self.tracefile = ''		# trace file object
		self.branchfile = ''	# branch file object
		self.mem = list()		# the main memory array
		self.memvalid = list()	# corresponding valid bits
		self.opcode_str = 'NOP'	# the string of the current opcode 
		self.opcode = 0			# integer value of current opcode
		self.word_mask = (1 << PDP8_WORD_SIZE) - 1
		# Current values of all registers
		# and machine state, including effective address, 
		# memory at effective address, and the address of 
		# the currently executed instruction (prevPC)
		self.IR = 0		# Instruction (current/last executed)
		self.PC = 0		# Program Counter
		self.AC = 0		# Accumulator
		self.LR = 0		# Link Register
		self.SR = SR	# Switch Register
		self.eaddr = 0		# effective address
		self.mem_eaddr = 0	# value in memory @ eaddr
		self.prevPC = 0		# PC of the current(last executed) instruction
		self.flagHLT = False
		
		# locations last accessed in memory; used in GUI
		self.mem_ref = {
			'eaddr_read': -1,
			'eaddr_write': -1, 
			'mem_read': -1,
			'mem_write': -1,
			'instr_fetch': -1
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
	# Function: load_memory
	# Description: Takes input filename as parameter, and 
	#   assigns values accordingly to the main memory array.
	def load_memory(self,filename):
		self.mem = list()	# initialize mem and memvalid to empty lists
		self.memvalid = list()
		# set PC to the starting address
		self.PC = START_ADDR
		# clear other registers
		self.AC = 0
		self.LR = 0
		self.IR = 0
		curr_addr = 0
		# Set all valid bits to 0
		for i in range (MEM_SIZE - 1):
			self.memvalid.append(0)
		# read from file
		srcfile = open(filename)
		line = srcfile.readline()
		# Set starting address to the first address given in the file
		if line_char[0] == '@':
			self.PC = int('0x'+line_char[1:])
		
		# read lines until end of file is encountered
		while line != '':
			line_char = list(line)
			# if current line specifies an address
			if line_char[0] == '@':
				curr_addr = int('0x'+line_char[1:])
			# otherwise, if current line specifies a memory value
			else: 
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
		if (self.memvalid[address] != 1):
			print ("[Warning: Invalid memory location accessed at %04o \n", address)
		# write to trace file
		self.tracefile.write(TRACE_TYPE[read_type]+' '+addr_hex+'\n')
		# return the value from memory at given address
		return (self.mem[address] & self.word_mask)

	#-------------------------------------
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
		self.tracefile.write(TRACE_TYPE['WRITE']+' '+addr_hex+'\n')
		# update value in the memory array & set valid bit
		self.mem[address] = value
		self.memvalid[address] = 1

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
			self.branchfile.write("%04o          UNCONDITIONAL [%3s] TAKEN              %04o \n", curr_PC, op_str, target_addr)
			# Example formatted print, uses a tuple: print '%d, %0d, %5d, %05d' % (34, 34, 34, 34)
		# conditional branch type 
		elif branch_type == BRANCH_TYPE['CONDITIONAL']:
			if branch_taken == True:
				self.branch_cond_t_count['all'] = self.branch_cond_t_count['all'] + 1 
				self.branch_cond_t_count[op_str] = self.branch_cond_t_count[op_str] + 1 
				self.branchfile.write("%04o          CONDITIONAL [%3s]    TAKEN              %04o \n", curr_PC, op_str, target_addr)
			else: 
				self.branch_cond_nt_count['all'] = self.branch_cond_nt_count['all'] + 1 
				self.branch_cond_nt_count[op_str] = self.branch_cond_nt_count[op_str] + 1
				self.branchfile.write("%04o          CONDITIONAL [%3s]    NOT TAKEN          %04o \n", curr_PC, op_str, target_addr)
	
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
		IR_bin_str = bin(self.IR)
		
		offset_mask = (1 << (ADDR_OFFSET_SIZE)) - 1 
		page_mask = (1 << (ADDR_PAGE_SIZE)) - 1
		
		current_page = self.prevPC & page_mask 
		current_offset = self.IR & offset_mask
		
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
					eff_addr = self.read_mem(self,indirect_addr_loc,'READ')
					self.mem_ref['eaddr_read'] = indirect_addr_loc
				else:
					# Current Page Addressing, so:
					#    Effective Address <- C(Old_PC[0:4] + Offset)
					indirect_addr_loc = current_page + current_offset
					# Read memory at indirect_addr_loc
					eff_addr = self.read_mem(self,indirect_addr_loc,'READ')
					self.mem_ref['eaddr_read'] = indirect_addr_loc
				# Add cycles for use of Indirect Addressing
				self.cycle_count['all'] = self.cycle_count['all'] + EADDR_CYCLES['Indirect']
				self.cycle_count[self.opcode_str] = self.cycle_count[self.opcode_str]+EADDR_CYCLES['Indirect']
			else: # offset location in range of 0010 - 0017 (octal) was specified
				# ADDRESSING MODE 4: AutoIndex Addressing
				#      C(AutoIndex_Register) <- C(AutoIndex_Register) + 1
				#      EffectiveAddress <- C(AutoIndex_Register)
				indirect_addr_loc = current_offset
				# Read memory at indirect_addr_loc
				eff_addr = self.read_mem(self,indirect_addr_loc,'READ')
				self.mem_ref['eaddr_read'] = indirect_addr_loc
				# Increment the value 
				eff_addr = eff_addr + 1 
				# Store the incremented value in memory
				self.write_mem(self,indirect_addr_loc,eff_addr)
				self.mem_ref['eaddr_write'] = indirect_addr_loc
				# Add cycles for use of AutoIndex Addressing
				self.cycle_count['all'] = self.cycle_count['all'] + EADDR_CYCLES['AutoIndex']
				self.cycle_count[self.opcode_str] = self.cycle_count[self.opcode_str]+EADDR_CYCLES['AutoIndex']
		# Return the calculated effective address
		return eff_addr

	#-------------------------------------	
	# Function: op_and
	# Description: Executes the AND operation.
	def op_and(self):
		# First read the value at eaddr
		self.mem_eaddr = read_mem(self,self.eaddr,'READ')
		self.mem_ref['mem_read'] = self.eaddr
		# Calculate AC & mem_val
		self.AC = self.AC & self.mem_eaddr
		
	#-------------------------------------	
	# Function: op_tad
	# Description: Executes the TAD operation.
	def op_tad(self):
		# First read the value at eaddr
		self.mem_eaddr = read_mem(self,self.eaddr,'READ')
		self.mem_ref['mem_read'] = self.eaddr
		# Add AC and mem_val
		sum = self.AC + self.mem_eaddr
		# if there is overflow from the MSbit position,
		# invert the LR 
		if ( (sum >> PDP8_WORD_SIZE) != 0 ):
			self.LR = not(self.LR)  
			# Note: Using logical NOT here, since LR is one bit only
		# save the AC using mask
		self.AC = sum & self.word_mask 
	
	#-------------------------------------	
	# Function: op_isz
	# Description: Executes the ISZ operation.
	def op_isz(self):
		# First read the value at eaddr
		self.mem_eaddr = read_mem(self,self.eaddr,'READ')
		self.mem_ref['mem_read'] = self.eaddr
		# Increment value by 1
		self.mem_eaddr = (self.mem_eaddr + 1) & self.word_mask
		# Write updated value to memory
		self.write_mem(self,self.eaddr,self.mem_eaddr)
		self.mem_ref['mem_write'] = self.eaddr
		# Check if the updated value is 0: if so, skip next instr
		if self.mem_eaddr == 0:
			self.PC = self.PC + 1
			# Write to branch trace file, providing current PC, opcode string,
			# target address, branch type, and flag indicating branch taken/not taken
			self.write_branch_trace(self, self.prevPC, self.opcode_str, 
				self.PC, BRANCH_TYPE['CONDITIONAL'], True)
		else:
			self.write_branch_trace(self, self.prevPC, self.opcode_str, 
				self.PC, BRANCH_TYPE['CONDITIONAL'], False)
	
	#-------------------------------------	
	# Function: op_dca
	# Description: Executes the DCA operation.
	def op_dca(self):
		# Write AC to memory
		self.write_mem(self,self.eaddr,self.AC)
		self.mem_ref['mem_write'] = self.eaddr
		# Clear the AC
		self.AC = 0 
	
	#-------------------------------------	
	# Function: op_jms
	# Description: Executes the JMS operation.
	def op_jms(self):
		# Save the PC to the effective address location
		# (Recall that PC was already incremented in step 1, 
		#  so it is already pointing to the next instruction)
		self.write_mem(self,self.eaddr,self.PC)
		self.mem_ref['mem_write'] = self.eaddr
		# Set the PC to (EffAddr + 1)
		self.PC = (self.eaddr + 1) & self.word_mask 
		# Write to the branch trace file, providing current PC, opcode string,
		# target address, branch type, and flag indicating branch taken/not taken
		self.write_branch_trace(self, self.prevPC, self.opcode_str, 
				self.PC, BRANCH_TYPE['UNCONDITIONAL'], True)
	
	#-------------------------------------	
	# Function: op_jmp
	# Description: Executes the JMP operation.
	def op_jmp(self):
		# Set PC to the effective address
		self.PC = self.eaddr
		# Write to the branch trace file, providing current PC, opcode string,
		# target address, branch type, and flag indicating branch taken/not taken
		self.write_branch_trace(self, self.prevPC, self.opcode_str, 
				self.PC, BRANCH_TYPE['UNCONDITIONAL'], True)
	
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
		IR_str = bin(self.IR)
		# Initialize this instr as NOT a branch
		curr_branch_type = BRANCH_TYPE['NO_BRANCH']
		curr_branch_taken = False
		str_OR_success = '' # OR conditions which were met
		str_AND_fail = '' # AND conditions that failed
		str_skip_check = ''
		
		# Verbose Debug Print for UI Instructions
		if self.debug_v:
			print ("\n")
			print ("***************** UI MODULE DEBUG ******************\n")
			print ("   Current Instr: %04o\n", self.IR)
			print (" \n")
			print ("   0   1   2   3   4   5   6   7   8   9  10  11\n")
			print (" +---+---+---+---+---+---+---+---+---+---+---+---+\n")
			print (" | %c | %c | %c | %c | %c | %c | %c | %c | %c | %c | %c | %c |\n",
				IR_str[0],IR_str[1],IR_str[2],IR_str[3],IR_str[4],IR_str[5],
				IR_str[6],IR_str[7],IR_str[8],IR_str[9],IR_str[10],IR_str[11])
			print (" +---+---+---+---+---+---+---+---+---+---+---+---+\n")
		
		# Group 1 Microinstructions: Check if bit 3 is a 0
		if IR_str[3] == '0':
			if self.debug_v:
				print ("                  cla cll cma cml rar ral 0/1 iac\n")
				print (" \n")
				print ("Group 1 Microinstructions:\n")
			
			# if bits IR[4:11] == 0, then the instruction is a NOP
			if (((self.IR << 4) & word_mask) == 0):
				# NOP
				print (" -- NOP\n")
			else:
				# Sequence 1: CLA/CLL
				# Check if bits 4 and 5 were set
				if IR_str[4] == '1':
					self.AC = 0
					if self.debug_v:
						print (" -- Clear Accumulator\n")
						print ("                NEW AC: %04o\n", self.AC)
				
				if IR_str[5] == '1':
					self.LR = 0
					if self.debug_v:
						print (" -- Clear Link Register\n")
						print ("                NEW LR: %1o\n", self.LR)
				
				# Sequence 2: CMA/CML
				# Check if bits 6 and 7 were set
				if IR_str[6] == '1':
					self.AC = (~self.AC) & self.word_mask
					if self.debug_v:
						print (" -- Complement Accumulator\n")
						print ("                NEW AC: %04o\n", self.AC)
				
				if IR_str[7] == '1':
					self.LR = not(self.LR)	# use logical not here since LR is one bit only
					if self.debug_v:
						print (" -- Complement Link Register\n")
						print ("                NEW LR: %1o\n", self.LR)
				
				# Sequence 3: IAC
				# Check if bit 11 is set
				if IR_str[11] == '1':
					self.AC = self.AC + 1
					if (self.AC >> PDP8_WORD_SIZE) != 0: # Check for overflow
						self.LR = not(self.LR)	# invert LR bit
					self.AC = self.AC & self.word_mask 	# mask upper bits of AC to word size
					
					if self.debug_v:
						print (" -- Complement Accumulator\n")
						print ("                NEW AC: %04o\n", self.AC)
						print ("                NEW LR: %1o", self.LR)
				
				# Sequence 4: RAR/RAL
				# Check if bits 8 and 9 have been set simultaneously: if so, this
				# is an invalid instruction, since a rotate right and rotate left has
				# been simultaneously indicated. Print a warning, but allow instruction 
				# to "execute" since performing the right and left rotate will cancel 
				# each other out and leave the AC unchanged.
				if (IR_str[8] == '1') and (IR_str[9] == '1'):
					print ("WARNING: Micro Op instruction conflict at PC = [%04o]. Rotate Left and Rotate Right enabled simultaneously.\n", self.prevPC)
				
				# Rotate right:
				# Check bit 8, which indicates a rotate right operation
				if IR_str[8] == '1':
					# Let tmp_val be set to the concatenation of LR and AC, 
					# {LR,AC}
					tmp_val = (self.LR << PDP8_WORD_SIZE) + self.AC
					
					# Check if bit 10 is 0: If so, only need to rotate one bit position
					if IR_str[10] == '1':
						# First make the most significant bit of tmp_rotate
						# equal to the least significant bit of tmp_val
						tmp_rotate = (tmp_val & 1) << PDP8_WORD_SIZE
						
						# Then OR the remaining more significant bits of tmp_val
						# with tmp_rotate
						tmp_rotate = tmp_rotate | (tmp_val >> 1)
						
						if self.debug_v:
							print (" -- Rotate Accumulator and Link Right\n")
					
					# Otherwise bit 10 (the 0/1 bit) is 1 --> rotate 2 positions right
					else:
						# First set the two most significant bits of tmp_rotate
						# equal to the two least significant bits of tmp_val
						tmp_rotate = (tmp_val & 3) << (PDP8_WORD_SIZE - 1)
						# Then OR the remaining more significant bits of tmp_val
						# with tmp_rotate
						tmp_rotate = tmp_rotate | (tmp_val >> 2)
						
						if self.debug_v:
							print (" -- Rotate Accumulator and Link Right Twice\n")
					
					# The new value of LR should be the most significant
					# bit of tmp_rotate, and the AC should be set to all the 
					# less significant bits of tmp_rotate.
					# {LR, AC} = tmp_rotate
					self.LR = tmp_rotate >> PDP8_WORD_SIZE
					self.AC = tmp_rotate & word_mask
					
					# Debug Print
					if self.debug_v:
						print ("                NEW LR: %1o\n", self.LR)
						print ("                NEW AC: %04o\n", self.AC)
				
				# Rotate left
				# Check if bit 9 is 1: RAL
				if IR_str[9] == '1':
					# Let tmp_val be set to the concatenation of LR and AC, 
					# {LR,AC}
					tmp_val = (self.LR << PDP8_WORD_SIZE) + self.AC
					
					# Check if bit 10 is 0: If so, only need to rotate one bit position
					if IR_str[10] == '1':
						# First set the least significant bit of tmp_rotate to be
						# the most significant of tmp_val.
						tmp_rotate = tmp_val >> PDP8_WORD_SIZE
						# Then OR tmp_rotate with all the remaining bits of tmp_val
						# after shifting them left one position.
						tmp_rotate = tmp_rotate | ((tmp_val & self.word_mask) << 1)
						if self.debug_v:
							print (" -- Rotate Accumulator and Link Left\n")
					
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
							print (" -- Rotate Accumulator and Link Left Twice\n")
											
					# Next, the new value of LR should be the most significant
					# bit of tmp_rotate, and the AC should be set to all the 
					# less significant bits of tmp_rotate.
					self.LR = tmp_rotate >> PDP8_WORD_SIZE
					self.AC = tmp_rotate & word_mask
					
					# Debug Print
					if self.debug_v:
						print ("                NEW LR: %1o\n", self.LR)
						print ("                NEW AC: %04o\n", self.AC)

		# Else, Bit 3 is 1, indicating either Group 2 or 3 Microinstructions
		else:
			# Check if bit 11 is 0: Group 2 Microinstructions
			if IR_str[11] == '0':
				# OR subgroup: Check if bit 8 is set to 0 
				if IR_str[8] == '0':
					if self.debug_v:
						print ("                  cla sma sza snl 0/1 osr hlt\n")
						print (" \n")
						print (" Group 2 Microinstructions:\n")
					
					# check if any of bits 5 through 7 were set, indicating
					# that an OR skip condition was to be checked (this instruction
					# should be flagged as a conditional branch instruction)
					if ((self.IR >> (PDP8_WORD_SIZE - 7-1)) & 7) != 0:
						curr_branch_type = BRANCH_TYPE['CONDITIONAL']
					
					# SMA - Skip on Minus Accumulator: check bit 5
					if IR_str[5] == '1':
						# if most significant bit of AC is 1, then skip
						if (self.AC >> (PDP8_WORD_SIZE - 1)) == 1:
							curr_branch_taken = True
							str_OR_success = str_OR_success + 'SMA '
						str_skip_check = str_skip_check + 'SMA '
					
					# SZA - Skip on Zero Accumulator: check bit 6
					if IR_str[6] == '1':
						# if AC is 0, then skip
						if self.AC == 0:
							curr_branch_taken = True
							str_OR_success = str_OR_success + 'SZA '
						str_skip_check = str_skip_check + 'SZA '
					
					# SNL - Skip on Nonzero Link: check bit 7
					if IR_str[7] == '1':
						# if LR is not 0, then skip
						if self.LR != 0:
							curr_branch_taken = True
							str_OR_success = str_OR_success + 'SNL '
						str_skip_check = str_skip_check + 'SNL '
					
					# Debug Print: Indicating if any of the OR skip conditions were met
					if self.debug_v and curr_branch_type == BRANCH_TYPE['CONDITIONAL']:
						if curr_branch_taken:
							print (" -- OR group condition(s) met: %s\n", str_OR_success)
						else:
							print (" -- OR group condition(s) not met.\n")
						print ("    Checked for: %s\n", str_skip_check)

				# Else, AND subgroup (bit 8 = 1)
				else:
					# debug print header
					if self.debug_v:
						print ("                  cla spa sna szl 0/1 osr hlt\n")
						print (" \n")
						print (" Group 2 Microinstructions:\n")
					
					# check if bits [5:7] were all zero: Skip Always should be 
					# flagged as an unconditional branch.
					if ((self.IR >> (PDP8_WORD_SIZE - 7-1)) & 7) == 0:
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
						if (self.AC >> (PDP8_WORD_SIZE - 1)) == 1:
							curr_branch_taken = False
							str_AND_fail = str_AND_fail + 'SPA '
						str_skip_check = str_skip_check + 'SPA '
					
					# SNA - Skip on Nonzero Accumulator: check bit 6
					if IR_str[6] == '1':
						# if AC is 0, then condition was not met, so do not skip
						if self.AC == 0:
							curr_branch_taken = False
							str_AND_fail = str_AND_fail + 'SNA '
						str_skip_check = str_skip_check + 'SNA '
					
					# SZL - Skip on Zero Link: check bit 7
					if IR_str[7] == '1':
						# if LR is non-zero, then condition not satisfied,
						# so do not skip
						if self.LR != 0:
							curr_branch_taken = False
							str_AND_fail = str_AND_fail + 'SZL '
						str_skip_check = str_skip_check + 'SZL '
					
					# Debug print
					if self.debug_v and (curr_branch_type != BRANCH_TYPE['NO_BRANCH']):
						if curr_branch_taken:
							print (" -- AND group condition(s) met.\n")
						else:
							print (" -- AND group condition(s) not met: %s\n", str_AND_fail)
						print ("    Checked for: %s\n", str_skip_check)
						
				# CLA - Clear Accumulator: check if bit 4 is set
				if IR_str[4] == '1':
					self.AC = 0
					if self.debug_v:
						print (" -- CLA - Clear Accumulator\n")
						print ("                NEW AC: %04o\n", self.AC)
				
				# OSR - Or Switch Register with Accumulator: check if bit 9 is set
				if IR_str[9] == '1':
					if self.debug_v:
						print (" -- OSR - Or Switch Register with Accumulator\n")
						print ("           Previous AC: %04o\n", self.AC)
						print ("           Previous SR: %04o\n", self.SR)
					
					self.AC = self.AC | self.SR
					
					if self.debug_v:
						print ("                NEW AC: %04o\n", self.AC)
				
				# HLT - HaLT: check if bit 10 is set
				if IR_str[10] == '1':
					self.flagHLT = True
					if self.debug_v:
						print (" -- HLT - Halt\n")
				
				# If a Group 2 branch instruction was given:
				if curr_branch_type != BRANCH_TYPE['NO_BRANCH']:
					# Determine if a Group 2 branch was taken, 
					# and if so, increment the PC
					if curr_branch_taken:
						self.PC = self.PC + 1
					
					# Update Branch Statistics as needed
					# Write to branch trace file, providing current PC, opcode string,
					# target address, branch type, and flag indicating branch taken/not taken
					self.write_branch_trace(self, self.prevPC, self.opcode_str, 
						self.PC, curr_branch_type, curr_branch_taken)
			
			# Else, bit 11 is set to 1: Group 3 Microinstructions
			else:
				# These are not implemented, so should be noted as 
				# illegal/unrecognized instructions
				print ("WARNING: Group 3 MicroOp called at PC = [%04o]. Group 3 MicroOps not enabled in simulation.\n", self.PC)
		
		# Set the flags for which branch condition tests were made
		self.branch_tests = str_skip_check
		self.branch_OR_success = str_OR_success
		self.branch_AND_fail = str_AND_fail
				
	#-------------------------------------
	# Function: op_default
	# Description: "Executes" a NOP.
	def op_default(self):
		# do nothing, print warning that illegal opcode was given
		print ("WARNING: Invalid opcode encountered at PC: [%04o]\n", self.prevPC)

	#-------------------------------------
	# Function: execute
	# Description: Executes the next instruction (found at the
	#    address specified by the PC).
	# Return Value: 0 -> execution completed successfully,
	#                    and no HLT was encountered
	#               1 -> HLT microinstruction was given.
	def execute(self):
		# STEP 0: Clear all locations referenced in memory by last instruction
		self.mem_ref['eaddr_read'] = -1
		self.mem_ref['eaddr_write'] = -1
		self.mem_ref['mem_read'] = -1
		self.mem_ref['mem_write'] = -1
		
		# STEP 1: Fetch the current instruction, increment PC
		self.IR = self.read_mem(self,self.PC,'FETCH')
		self.mem_ref['instr_fetch'] = self.PC	# save location of fetched instr
		self.prevPC = self.PC 
		self.PC = self.PC + 1

		# STEP 2: Decode the current instruction
		# determine the opcode
		self.opcode = self.IR >> (PDP8_WORD_SIZE - PDP8_OPCODE_SIZE)
		self.opcode_str = OPCODE_NAME[self.opcode]
		op_str = self.opcode_str 	# shorter name for easier use, read-only
		
		# STEP 2b: Determine the Effective Address
		if (self.opcode >= 0 and self.opcode < 6):
			self.eaddr = self.calc_eaddr()
		
		# STEP 3: Execute Current Instruction
		self.opcode_exec.get(self.opcode,self.op_default)(self)
		# This will call the corresponding function based on the current opcode.
		
		# STEP 4: Update Stats for Opcodes
		self.instr_count['all'] = self.instr_count['all'] + 1
		self.instr_count[op_str] = self.instr_count[op_str]+1
		self.cycle_count['all'] = self.cycle_count['all'] + OPCODE_CYCLES[op_str]
		self.cycle_count[op_str] = self.cycle_count[op_str]+OPCODE_CYCLES[op_str]
		
		# Print the basic debug values
		if self.debug:
			print ("\n")
			print ("================== INSTRUCTION #%-1d : %s ==================\n", self.instr_count['all'], self.opcode_str)
			print ("             PC / IR: %04o / %04o\n", self.prevPC, self.IR)
			print ("             LR / AC: %1o / %04o \n", self.LR, self.AC)
			print ("   EFFECTIVE ADDRESS: %04o\n", self.eaddr)
			print ("   VALUE @ EFF. ADDR: %04o\n", self.mem[self.eaddr])
		
		# return the HALT flag
		return self.flagHLT
