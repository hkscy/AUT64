# Reference AUT64 implementation in python
# C Hicks, hkscy.org, 03-01-19
from __future__ import print_function
import math
import random
import os
import copy
from copy import deepcopy
import itertools

verbose = False

# For prettying up the terminal output
class bcolours:
    OKBLUE = '\033[94m'
    BOLD = '\033[1m'
    ENDC = '\033[0m'

# Logarithm base 2
def log2(n):
    return int(math.log(n)/math.log(2))

# Create generator of consecutive 32-bit keys with no zeroes
# Returns: generator which yields a list of integer nibbles [1-15]    
def key_reg_gen():
    n_hexdig = int(2+(32/4)) 
    for n in map(list, itertools.product(['{:01x}'.format(bits) for bits in range(0x1,0xF+1)], repeat=8)):
        yield [int(nibble, 16) for nibble in n]

# Generate a random permutation of length n_inputs
# Returns: a list of integer nibbles [0-n_inputs]
def random_pbox(n_inputs=8):
    nibbles = []
    for nibble in range(0, n_inputs):
        foundNibble = False
        # Find a nibble which isn't already in the list
        while not foundNibble:
            randNib = random.getrandbits(log2(n_inputs))
            if not randNib in nibbles:
                nibbles += [randNib]
                foundNibble = True
    return nibbles        

# Generate A `random' bijective sbox of size n*n
# Returns: list of integer nibbles [0-2^n]
def random_sbox(n=4):
    return random_pbox(pow(2,n))

table_ln = [0x4, 0x5, 0x6, 0x7, 0x0, 0x1, 0x2, 0x3, # Round 0
            0x5, 0x4, 0x7, 0x6, 0x1, 0x0, 0x3, 0x2, # Round 1
            0x6, 0x7, 0x4, 0x5, 0x2, 0x3, 0x0, 0x1, # ...
            0x7, 0x6, 0x5, 0x4, 0x3, 0x2, 0x1, 0x0, 
            0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7,
            0x1, 0x0, 0x3, 0x2, 0x5, 0x4, 0x7, 0x6,
            0x2, 0x3, 0x0, 0x1, 0x6, 0x7, 0x4, 0x5,
            0x3, 0x2, 0x1, 0x0, 0x7, 0x6, 0x5, 0x4,
            0x5, 0x4, 0x7, 0x6, 0x1, 0x0, 0x3, 0x2,
            0x4, 0x5, 0x6, 0x7, 0x0, 0x1, 0x2, 0x3,
            0x7, 0x6, 0x5, 0x4, 0x3, 0x2, 0x1, 0x0, # ...
            0x6, 0x7, 0x4, 0x5, 0x2, 0x3, 0x0, 0x1] # Round 11
            
table_un = [0x1, 0x0, 0x3, 0x2, 0x5, 0x4, 0x7, 0x6, # Round 0
            0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, # Round 1
            0x3, 0x2, 0x1, 0x0, 0x7, 0x6, 0x5, 0x4, # ...
            0x2, 0x3, 0x0, 0x1, 0x6, 0x7, 0x4, 0x5, 
            0x5, 0x4, 0x7, 0x6, 0x1, 0x0, 0x3, 0x2, 
            0x4, 0x5, 0x6, 0x7, 0x0, 0x1, 0x2, 0x3, 
            0x7, 0x6, 0x5, 0x4, 0x3, 0x2, 0x1, 0x0, 
            0x6, 0x7, 0x4, 0x5, 0x2, 0x3, 0x0, 0x1, 
            0x3, 0x2, 0x1, 0x0, 0x7, 0x6, 0x5, 0x4,
            0x2, 0x3, 0x0, 0x1, 0x6, 0x7, 0x4, 0x5, 
            0x1, 0x0, 0x3, 0x2, 0x5, 0x4, 0x7, 0x6, # ...
            0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7] # Round 11

# AUT64 Compression function substituiton table T_offset         
# Input Nibbble:   0    1    2    3    4    5    6    7    8    9    A    B    C    D    E    F  | Key Nibble               
table_offset = [ 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, # 0
                 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF, # 1
                 0x0, 0x2, 0x4, 0x6, 0x8, 0xA, 0xC, 0xE, 0x3, 0x1, 0x7, 0x5, 0xB, 0x9, 0xF, 0xD, # 2
                 0x0, 0x3, 0x6, 0x5, 0xC, 0xF, 0xA, 0x9, 0xB, 0x8, 0xD, 0xE, 0x7, 0x4, 0x1, 0x2, # 3
                 0x0, 0x4, 0x8, 0xC, 0x3, 0x7, 0xB, 0xF, 0x6, 0x2, 0xE, 0xA, 0x5, 0x1, 0xD, 0x9, # 4
                 0x0, 0x5, 0xA, 0xF, 0x7, 0x2, 0xD, 0x8, 0xE, 0xB, 0x4, 0x1, 0x9, 0xC, 0x3, 0x6, # 5
                 0x0, 0x6, 0xC, 0xA, 0xB, 0xD, 0x7, 0x1, 0x5, 0x3, 0x9, 0xF, 0xE, 0x8, 0x2, 0x4, # 6
                 0x0, 0x7, 0xE, 0x9, 0xF, 0x8, 0x1, 0x6, 0xD, 0xA, 0x3, 0x4, 0x2, 0x5, 0xC, 0xB, # 7
                 0x0, 0x8, 0x3, 0xB, 0x6, 0xE, 0x5, 0xD, 0xC, 0x4, 0xF, 0x7, 0xA, 0x2, 0x9, 0x1, # 8
                 0x0, 0x9, 0x1, 0x8, 0x2, 0xB, 0x3, 0xA, 0x4, 0xD, 0x5, 0xC, 0x6, 0xF, 0x7, 0xE, # 9
                 0x0, 0xA, 0x7, 0xD, 0xE, 0x4, 0x9, 0x3, 0xF, 0x5, 0x8, 0x2, 0x1, 0xB, 0x6, 0xC, # A
                 0x0, 0xB, 0x5, 0xE, 0xA, 0x1, 0xF, 0x4, 0x7, 0xC, 0x2, 0x9, 0xD, 0x6, 0x8, 0x3, # B
                 0x0, 0xC, 0xB, 0x7, 0x5, 0x9, 0xE, 0x2, 0xA, 0x6, 0x1, 0xD, 0xF, 0x3, 0x4, 0x8, # C
                 0x0, 0xD, 0x9, 0x4, 0x1, 0xC, 0x8, 0x5, 0x2, 0xF, 0xB, 0x6, 0x3, 0xE, 0xA, 0x7, # D
                 0x0, 0xE, 0xF, 0x1, 0xD, 0x3, 0x2, 0xC, 0x9, 0x7, 0x6, 0x8, 0x4, 0xA, 0xB, 0x5, # E
                 0x0, 0xF, 0xD, 0x2, 0x9, 0x6, 0x4, 0xB, 0x1, 0xE, 0xC, 0x3, 0x8, 0x7, 0x5, 0xA ]# F

# AUT64 Substitution table (used for decryption)                                     
table_sub = [0x0, 0x1, 0x9, 0xE, 0xD, 0xB, 0x7, 0x6, 0xF, 0x2, 0xC, 0x5, 0xA, 0x4, 0x3, 0x8] 

# Print input n as 8 bit binary string
def print8bitBin(n):
    return format(n, '#010b')

# Print input n as 8 bit binary string with prefix prefix
def print8bitBinPrefixed(prefix, n):    
    return str(prefix) + ' ' + print8bitBin(n)

# AUT64 Compression function G
# Inputs: state   - 64-bit bitstring round state
#         key_reg - 32-bit bitstring compression function key k_G
#         roundN  - AUT64 round number [0-11]
#         verbose - Provide detailed operations
# Returns: 8-bit integer x'_7
def compress(state, key_reg, roundN, verbose):
    if verbose:
        print ('round: ' + str(roundN))
        print ('\tround input: ', end='')
        print ([print8bitBin(i) for i in state[:4]])
        print ('\t        ...: ', end='')
        print ([print8bitBin(i) for i in state[4:]])

    r5 = 0
    r6 = 0
    for byte in range(0, 7): # Compute over first 7 bytes
        ## lower nibble in byte ##  
        ln = state[byte] & 0xf # get lower byte nibble
        lk = key_reg[table_ln[8*roundN + byte]] # get key nibble
        p0 = ln | ((lk << 4) & 0xf0) # combine state and key nibble    
        r6 ^= table_offset[p0]
        
        ## upper nibble in byte ##
        un = (state[byte] >> 4) & 0xf # get upper byte nibble
        uk = key_reg[table_un[8*roundN + byte]] # get key nibble  
        p1 = un | ((uk << 4) & 0xf0) # combine state and key nibble uk,un
        r5 ^= table_offset[p1]
        
        if verbose:
            print ('\tbyte #: ' + str(byte), end='')
            print (print8bitBinPrefixed(' :', state[byte]))
            print (print8bitBinPrefixed('\tln:', ln),end='')
            print (print8bitBinPrefixed(' lk:', lk),end='')
            print ('(' + str(table_ln[8*roundN + byte]) + ')',end='')
            print (print8bitBinPrefixed(' p0:', p0),end='')
            print (print8bitBinPrefixed(' to:', table_offset[p0]),end='')
            print (print8bitBinPrefixed(' r6:', r6))
            print (print8bitBinPrefixed('\tun:', un),end='')
            print (print8bitBinPrefixed(' uk:', uk),end='')
            print ('(' + str(table_un[8*roundN + byte]) + ')',end='')
            print (print8bitBinPrefixed(' p1:', p1),end='')
            print (print8bitBinPrefixed(' to:', table_offset[p1]),end='')
            print (print8bitBinPrefixed(' r5:', r5))
        
    ## Compute final byte (7)
    
    ## lower nibble in byte ##
    ln = state[7] & 0xf # get lower byte nibble
    lk = key_reg[table_ln[8*roundN + 7]] # get lower key nibble   
    ls = (table_sub[lk] << 4) & 0xf0    # Substitute and move lower into upper nibble

    # Find index of ln in table_offset at ls+(0,1,2,...,15)
    for i_ln in range(0,16):
        if table_offset[ls + i_ln] == ln:
            break
    r6 ^= i_ln
    
    if verbose:
        print ('\tbyte #: 7 :',end='')
        print (print8bitBinPrefixed(' :', state[7]))
        print (print8bitBinPrefixed('\tln:', ln),end='')
        print (print8bitBinPrefixed(' lk:', lk),end='')
        print ('(' + str(table_ln[8*roundN + byte]) + ')',end='')
        print (print8bitBinPrefixed('ls(lk):', ls),end='')
        print ('(' + str(lk) + ')')        
        print ('\ti_ln: ' + str(i_ln) + ' ls+i_ln: ' + str(ls+i_ln),end='')
        print ('table_offset[ls+i_ln]: ' + str(table_offset[ls+i_ln]) + ' = ln',end='')
        print (print8bitBinPrefixed('r6:', r6))
    
    ## upper nibble in byte ##
    un = (state[7] >> 4) & 0xf # get upper byte nibble
    uk = key_reg[table_un[8*roundN + 7]] # get upper key nibble   
    us = (table_sub[uk] << 4) & 0xf0    # Substitute and move lower into upper nibble

    #Find index of ln in table_offset at ls+(0,1,2,...,15)
    for i_un in range(0,16):
        if table_offset[us + i_un] == un:
            break
    r5 ^= i_un
    
    result = ((r5 << 4) & 0xf0) | (r6 & 0x0f) #r5,r6
    
    if verbose:
        print (print8bitBinPrefixed('\tun:', un),end='')
        print (print8bitBinPrefixed(' uk:', uk),end='')
        print ('(' + str(table_ln[8*roundN + byte]) + ')',end='')
        print (print8bitBinPrefixed('us(uk):', ls),end='')
        print ('(' + str(uk) + ')')
        print ('\ti_un: ' + str(i_ln) + ' us+i_un: ' + str(us+i_un),end='')
        print ('table_offset[us+i_lu]: ' + str(table_offset[us+i_un]) + ' = un',end='')     
        print (print8bitBinPrefixed('r5:', r5))
        print (print8bitBinPrefixed('\t**round output: ', result) + '**')
            
    return result

# Apply 4x4 sbox nibble wise to byte
# Returns: 8-bit integer result
def apply_sbox(byte, sbox):
    result = 0
    
    # Lower nibble
    result = sbox[byte & 0xf]
    # Upper nibble
    result = result|sbox[(byte >> 4) & 0x0f] << 4
    
    return result

# Apply pbox to input_data(list of input bytes) n times
# Returns: 8-bit integer result 
def apply_pbox(input_data, pbox, n):
    input_data_copy = copy.copy(input_data)

    for rnd in range(0,n):
        output_data = [0]*8
        for bIdx,byte in enumerate(input_data_copy):
            output_data[pbox[bIdx]] = input_data_copy[bIdx]        
        input_data_copy = copy.copy(output_data)
        
    return output_data 


# Apply pbox to 8-bit input_data bitwise
# Returns: 8-bit bitwise permuted input_data as integer
def apply_pbox_bitwise(input_data, pbox):
    result = 0

    for bit in range(8):
        if (input_data & (1 << bit)):
            result |= (1 << pbox[bit])

    return result

# AUT64 encryption function
# Inputs: state   - 64-bit bitstring message m
#         key_reg - 32-bit bitstring compression function key k_G
#         pbox    - 8-element AUT64 permutation key part k_perm
#         sbox    - 4x4 AUT64 sbox key part k_sub
#         nRounds - nRounds of AUT64 round function to apply
#         verbose - Provide detailed operations
# Returns: 64-bit AUT64 encryption as list of hex strings
def encrypt(state, key_reg, pbox, sbox, nRounds, verbose):

    stateInternal = copy.deepcopy(state)

    for roundN in range(0,nRounds):
        stateInternal = apply_pbox(stateInternal,pbox,1) 
        step1 = compress(stateInternal, key_reg, roundN, verbose)          #g({0,1}^64}) -> {0,1}^8
        step2 = list( bin( apply_sbox(step1, sbox) )[2:].zfill(8) ) 
        step2 = int(''.join(step2), 2)
        step3 = apply_pbox_bitwise(step2, pbox)
        step4 = int( apply_sbox(step3, sbox) )
        stateInternal[7] = step4

        if False:
            print(hex(step1))
            print(hex(step2))
            print(hex(step3))
            print(hex(step4))
            print(stateInternal) 

    return stateInternal                   

if __name__ == '__main__':

    # Some example key values
    pbox = [2, 0, 6, 5, 7, 4, 3, 1]
    key_reg = [10, 8, 4, 14, 5, 4, 8, 11]
    sbox = [5, 11, 7, 12, 4, 8, 0, 3, 13, 9, 6, 1, 2, 14, 10, 15]
    message = [0x1,0x2,0x3,0x4,0x5,0x6,0x7,0x8]
    nRounds = 8

    # AUT64 encrypt
    e = encrypt(message, key_reg, pbox, sbox, nRounds, verbose)
    print('Message: ', end='')
    print(['0x{:02x}'.format(m_) for m_ in message])
    print('Ciphert: ', end='')
    print(['0x{:02x}'.format(e_) for e_ in e])

    # Generate and print some random encryptions
    # Note: Unless you sanitise (cyclic only) the pbox values these will not look very random!
    nRandEncryptions = 5
    kRGen = key_reg_gen()
    for _ in range(nRandEncryptions):
        key_reg = next(key_reg_gen())
        pbox = random_pbox()
        sbox = random_sbox()
        message = [random.randint(0,255) for _ in range(8)]
        e = encrypt(message, key_reg, pbox, sbox, nRounds, verbose) 
        print('Message: ', end='')
        print(['0x{:02x}'.format(m_) for m_ in message])
        print('Ciphert: ', end='')
        print(['0x{:02x}'.format(e_) for e_ in e])