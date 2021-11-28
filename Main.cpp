//
//  main.c
//  aes-64-ctr
//  uses GF(2^4) field and a polynomial of x^4 + x^1 + 1 (0x13)
//  state length is 4 bits long
//  round number remains 10
//
//  Created by Peter Čuřík Jr. on 13/11/2021. Modified by Stanislav Marochok on 28/11/2021.
//

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <cstdint>
#include <ctime>

const int rounds = 4; // old 10
const int numexperiments = 100;

//key stuff
const uint16_t rcon[10] = { 0x0100, 0x0200, 0x0400, 0x0800, 0x0300, 0x0600, 0x0C00, 0x0B00, 0x0500, 0x0A00 };
const uint64_t master_key = 0x2b7e151628aed2a6;
uint64_t round_keys[rounds];

//sbox stuff
const uint8_t sbox[16] = { 0x8, 0xC, 0xB, 0x3, 0x7, 0x9, 0x1, 0x4, 0xE, 0x6, 0x0, 0xD, 0x2, 0xF, 0x5, 0xA };
const uint8_t inverse_sbox[16] = { 0xA, 0x6, 0xC, 0x3, 0x7, 0xE, 0x9, 0x4, 0x0, 0x5, 0xF, 0x2, 0x1, 0xB, 0x8, 0xD };

//substitution stuff
const uint8_t shift_rows_mapping[16] = { 0x0, 0xD, 0xA, 0x7, 0x4, 0x1, 0xE, 0xB, 0x8, 0x5, 0x2, 0xF, 0xC, 0x9, 0x6, 0x3 };
const uint8_t shift_rows_inverse_mapping[16] = { 0x0, 0x5, 0xA, 0xF, 0x4, 0x9, 0xE, 0x3, 0x8, 0xD, 0x2, 0x7, 0xC, 0x1, 0x6, 0xB };

//multiplication tables
const uint8_t mul1[16] = { 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF };
const uint8_t mul2[16] = { 0x0, 0x2, 0x4, 0x6, 0x8, 0xA, 0xC, 0xE, 0x3, 0x1, 0x7, 0x5, 0xB, 0x9, 0xF, 0xD };
const uint8_t mul3[16] = { 0x0, 0x3, 0x6, 0x5, 0xC, 0xF, 0xA, 0x9, 0xB, 0x8, 0xD, 0xE, 0x7, 0x4, 0x1, 0x2 };
const uint8_t mul9[16] = { 0x0, 0x9, 0x1, 0x8, 0x2, 0xB, 0x3, 0xA, 0x4, 0xD, 0x5, 0xC, 0x6, 0xF, 0x7, 0xE };
const uint8_t mul11[16] = { 0x0, 0xB, 0x5, 0xE, 0xA, 0x1, 0xF, 0x4, 0x7, 0xC, 0x2, 0x9, 0xD, 0x6, 0x8, 0x3 };
const uint8_t mul13[16] = { 0x0, 0xD, 0x9, 0x4, 0x1, 0xC, 0x8, 0x5, 0x2, 0xF, 0xB, 0x6, 0x3, 0xE, 0xA, 0x7 };
const uint8_t mul14[16] = { 0x0, 0xE, 0xF, 0x1, 0xD, 0x3, 0x2, 0xC, 0x9, 0x7, 0x6, 0x8, 0x4, 0xA, 0xB, 0x5 };

uint64_t addRoundKey(uint64_t key, uint64_t block) {
    return key ^ block;
}

uint64_t subBytes(uint64_t block, int mode) {
    uint8_t box[16];
    // use sbox in case of encrypting. use inverse sbox otherwise
    memcpy(box, mode == 1 ? sbox : inverse_sbox, sizeof(sbox));

    uint16_t col1 = (block >> 48) & 0xffff;
    uint16_t col2 = (block >> 32) & 0xffff;
    uint16_t col3 = (block >> 16) & 0xffff;
    uint16_t col4 = (block >> 0) & 0xffff;

    col1 = (box[(col1 >> 0) & 0xf] << 0)
        ^ (box[(col1 >> 4) & 0xf] << 4)
        ^ (box[(col1 >> 8) & 0xf] << 8)
        ^ (box[(col1 >> 12) & 0xf] << 12);

    col2 = (box[(col2 >> 0) & 0xf] << 0)
        ^ (box[(col2 >> 4) & 0xf] << 4)
        ^ (box[(col2 >> 8) & 0xf] << 8)
        ^ (box[(col2 >> 12) & 0xf] << 12);

    col3 = (box[(col3 >> 0) & 0xf] << 0)
        ^ (box[(col3 >> 4) & 0xf] << 4)
        ^ (box[(col3 >> 8) & 0xf] << 8)
        ^ (box[(col3 >> 12) & 0xf] << 12);

    col4 = (box[(col4 >> 0) & 0xf] << 0)
        ^ (box[(col4 >> 4) & 0xf] << 4)
        ^ (box[(col4 >> 8) & 0xf] << 8)
        ^ (box[(col4 >> 12) & 0xf] << 12);

    return ((uint64_t)col1) << 48
        ^ ((uint64_t)col2) << 32
        ^ ((uint64_t)col3) << 16
        ^ ((uint64_t)col4) << 0;
}

uint64_t shiftRows(uint64_t block, int mode) {
    uint8_t arrShiftRows[16];
    // use shift rows table in case of encrypting. use shift rows inverse table otherwise
    memcpy(arrShiftRows, mode == 1 ? shift_rows_mapping : shift_rows_inverse_mapping, sizeof(shift_rows_mapping));

    uint64_t shiftedBlock = 0;
    uint64_t mask = 0xf;
    int maskShift, blockShift;
    for (int i = sizeof(arrShiftRows) - 1; i >= 0; i--) {
        maskShift = 4 * ((sizeof(arrShiftRows) - 1) - arrShiftRows[i]);
        blockShift = maskShift - 4 * (sizeof(arrShiftRows) - 1 - i);

        if (blockShift < 0) {
            shiftedBlock |= (block >> abs(blockShift)) & (mask << maskShift);
        }
        else {
            shiftedBlock |= (block << blockShift) & (mask << maskShift);
        }
    }
    return shiftedBlock;
}

uint64_t mixColumns(uint64_t block, int mode) {
    uint8_t arr1[16], arr2[16], arr3[16], arr4[16];
    // choose multiplication tables according to encryption/decryption mode
    memcpy(arr1, mode == 1 ? mul2 : mul14, sizeof(mul1));
    memcpy(arr2, mode == 1 ? mul3 : mul11, sizeof(mul1));
    memcpy(arr3, mode == 1 ? mul1 : mul13, sizeof(mul1));
    memcpy(arr4, mode == 1 ? mul1 : mul9, sizeof(mul1));

    uint64_t mixedBlock = 0;

    // Rijndael's matrix and data block multiplication
    for (int i = 15; i >= 3; i -= 4) {
        mixedBlock |= (uint64_t)(arr1[(block >> 4 * i) & 0xf]
            ^ arr2[(block >> 4 * (i - 1)) & 0xf]
            ^ arr3[(block >> 4 * (i - 2)) & 0xf]
            ^ arr4[(block >> 4 * (i - 3)) & 0xf]) << 4 * i;

        mixedBlock |= (uint64_t)(arr4[(block >> 4 * i) & 0xf]
            ^ arr1[(block >> 4 * (i - 1)) & 0xf]
            ^ arr2[(block >> 4 * (i - 2)) & 0xf]
            ^ arr3[(block >> 4 * (i - 3)) & 0xf]) << 4 * (i - 1);

        mixedBlock |= (uint64_t)(arr3[(block >> 4 * i) & 0xf]
            ^ arr4[(block >> 4 * (i - 1)) & 0xf]
            ^ arr1[(block >> 4 * (i - 2)) & 0xf]
            ^ arr2[(block >> 4 * (i - 3)) & 0xf]) << 4 * (i - 2);

        mixedBlock |= (uint64_t)(arr2[(block >> 4 * i) & 0xf]
            ^ arr3[(block >> 4 * (i - 1)) & 0xf]
            ^ arr4[(block >> 4 * (i - 2)) & 0xf]
            ^ arr1[(block >> 4 * (i - 3)) & 0xf]) << 4 * (i - 3);
    }

    return mixedBlock;
}

uint64_t AESencrypt(uint64_t block, int _rounds) {
    block = addRoundKey(master_key, block);

    for (int round = 0; round < _rounds; round++) {
        block = subBytes(block, 1);
        block = shiftRows(block, 1);
        if (round < _rounds - 1)
            block = mixColumns(block, 1);
        
        block = addRoundKey(round_keys[round], block);
    }
    return block;
}

uint64_t AESdecrypt(uint64_t block, int _rounds) {
    for (int round = 0; round < _rounds; round++) {
        block = addRoundKey(round_keys[_rounds - 1 - round], block);
        if (round != 0)
            block = mixColumns(block, 0);
        
        block = shiftRows(block, 0);
        block = subBytes(block, 0);
    }

    block = addRoundKey(master_key, block);
    return block;
}

uint64_t *setup(uint64_t *plain_texts) {
    uint64_t *cipher_texts = new uint64_t[16];

    for (int i = 0; i < 16; i++) {
        uint64_t encrypted = AESencrypt(plain_texts[i], rounds);
        cipher_texts[i] = encrypted;
    }

    return cipher_texts;
}

// nibble_position: 0 for first nibble (the most left)
uint8_t check_xor_of_nth_nibbles_in_set(uint64_t *delta_set, int nibble_position) {
    uint8_t result = (delta_set[0] >> (64 - (nibble_position * 4))) & 0xf;
    for (int i = 1; i < 16; i++) {
        uint8_t x = (delta_set[i] >> (64 - (nibble_position * 4))) & 0xf;
        result ^= x;
    }

    return result;
}

// key_guess -> guess for 4 bits of key (value in range 0 - 15)
// key_guess_position -> position of the key
uint8_t * reverseState(uint8_t key_guess, int key_guess_position, uint64_t *cipher_texts) {
    uint8_t *result = new uint8_t[16];
    for (int i = 0; i < 16; i++) {
        uint8_t byteOnPosition = ((cipher_texts[i] >> (64 - (key_guess_position * 4))) & 0xf);
        uint8_t before_add_round_key = byteOnPosition ^ key_guess;
        uint8_t before_sub_byte = inverse_sbox[before_add_round_key];
        result[i] = before_sub_byte;
    }

    return result;
}

bool checkKeyGuess(uint8_t keyGuess, uint8_t *reversedStates) {
    uint8_t result = 0;
    for (int i = 0; i < 16; i++)
        result ^= reversedStates[i];
    return result == 0;
}

uint64_t guessKey() {
    uint64_t* plainTexts = new uint64_t[16]{
        0b0000000000000000000000000000000000000000000000000000000000000000,
        0b0001000000000000000000000000000000000000000000000000000000000000,
        0b0010000000000000000000000000000000000000000000000000000000000000,
        0b0011000000000000000000000000000000000000000000000000000000000000,
        0b0100000000000000000000000000000000000000000000000000000000000000,
        0b0101000000000000000000000000000000000000000000000000000000000000,
        0b0110000000000000000000000000000000000000000000000000000000000000,
        0b0111000000000000000000000000000000000000000000000000000000000000,
        0b1000000000000000000000000000000000000000000000000000000000000000,
        0b1001000000000000000000000000000000000000000000000000000000000000,
        0b1010000000000000000000000000000000000000000000000000000000000000,
        0b1011000000000000000000000000000000000000000000000000000000000000,
        0b1100000000000000000000000000000000000000000000000000000000000000,
        0b1101000000000000000000000000000000000000000000000000000000000000,
        0b1110000000000000000000000000000000000000000000000000000000000000,
        0b1111000000000000000000000000000000000000000000000000000000000000,
    };

    uint64_t *cipherTexts = setup(plainTexts);
    uint64_t lastRoundKey = 0;

    for (int keyGuessPosition = 1; keyGuessPosition <= 16; keyGuessPosition++) {
        for (int i = 0; ; i++) {
            uint8_t* guesses = new uint8_t[16];
            int correct_guesses = 0;
            for (uint8_t keyGuess = 0x0; keyGuess <= 0xf; keyGuess++) {
                uint8_t* reversedStates = reverseState(keyGuess, keyGuessPosition, cipherTexts);
                if (checkKeyGuess(keyGuess, reversedStates)) {
                    guesses[correct_guesses++] = keyGuess;
                }
            }
            if (correct_guesses == 1) {
                //printf("Possible key: Index: %d, Value: %01x\n", keyGuessPosition, guesses[0]);
                lastRoundKey |= (uint64_t)guesses[0] << (64 - keyGuessPosition * 4);
                break;
            }
            else {
                // update delta set
                for (int j = 0; j < 16; j++) plainTexts[j]++;
                // get new data to crack
                cipherTexts = setup(plainTexts);
            }
        }
    }

    return lastRoundKey;
}

void deriveKeys() {
    uint64_t currentKey = master_key;

    for (int i = 0; i < rounds; i++) {
        //RotWord
        uint16_t tmp = currentKey & 0xffff;
        tmp = ((tmp >> 12) & 0xf) ^ (tmp << 4);

        //SubBytes
        tmp = (sbox[(tmp >> 0) & 0xf] << 0)
            ^ (sbox[(tmp >> 4) & 0xf] << 4)
            ^ (sbox[(tmp >> 8) & 0xf] << 8)
            ^ (sbox[(tmp >> 12) & 0xf] << 12);

        //Calculate each word column
        uint16_t roundKey1 = (tmp ^ (currentKey >> 48) ^ rcon[i]);
        uint16_t roundKey2 = (roundKey1 ^ (currentKey >> 32));
        uint16_t roundKey3 = (roundKey2 ^ (currentKey >> 16));
        uint16_t roundKey4 = (roundKey3 ^ (currentKey >> 0));

        //XOR together and save as a 64bit round key
        round_keys[i] = ((uint64_t)roundKey1) << 48
            ^ ((uint64_t)roundKey2) << 32
            ^ ((uint64_t)roundKey3) << 16
            ^ ((uint64_t)roundKey4) << 0;

        currentKey = round_keys[i];
    }
}

uint64_t inverseKeyExpansion(uint64_t key, int round) {
    uint16_t roundKey4 = (key >>  0) & 0xffff;
    uint16_t roundKey3 = (key >> 16) & 0xffff;
    uint16_t roundKey2 = (key >> 32) & 0xffff;
    uint16_t roundKey1 = (key >> 48) & 0xffff;

    uint16_t currentKey4 = roundKey4 ^ roundKey3;
    uint16_t currentKey3 = roundKey3 ^ roundKey2;
    uint16_t currentKey2 = roundKey2 ^ roundKey1;

    uint16_t tmp = currentKey4;
    tmp = ((tmp >> 12) & 0xf) ^ (tmp << 4);

    //SubBytes
    tmp = (sbox[(tmp >> 0) & 0xf] << 0)
        ^ (sbox[(tmp >> 4) & 0xf] << 4)
        ^ (sbox[(tmp >> 8) & 0xf] << 8)
        ^ (sbox[(tmp >> 12) & 0xf] << 12);

    uint16_t currentKey1 = roundKey1 ^ tmp ^ rcon[round];

    return ((uint64_t)currentKey1) << 48
        ^ ((uint64_t)currentKey2) << 32
        ^ ((uint64_t)currentKey3) << 16
        ^ ((uint64_t)currentKey4) << 0;
}

int main(int argc, const char* argv[]) {
    deriveKeys();

    // master  key: 0x2b7e151628aed2a6
    // round 1 key: 0x9a618f77a7d9757f
    // round 2 key: 0x0cc583b2246b5114
    // round 3 key: 0xc4bc470e63653271
    // round 4 key: 0x787f3f715c146e65

    clock_t beginTime = clock();

    uint64_t round4Key = guessKey();
    uint64_t round3Key = inverseKeyExpansion(round4Key, 3);
    uint64_t round2Key = inverseKeyExpansion(round3Key, 2);
    uint64_t round1Key = inverseKeyExpansion(round2Key, 1);
    uint64_t crackedMasterKey = inverseKeyExpansion(round1Key, 0);

    printf("Cracked key: 0x%16llx\n", crackedMasterKey);

    double time = (clock() - beginTime) / (double)CLOCKS_PER_SEC;
    printf("Time taken: %f\n", time);

    return 0;
}