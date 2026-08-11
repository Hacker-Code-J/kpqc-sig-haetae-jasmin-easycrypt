from Jasmin require import JByte_array.

require import BArray128 BArray768.

clone SubByteArray as SBArray768_128  with theory Asmall <= BArray128,
                                           theory Abig <= BArray768.
