from Jasmin require import JByte_array.

require import BArray32 BArray4032.

clone SubByteArray as SBArray4032_32  with theory Asmall <= BArray32,
                                           theory Abig <= BArray4032.
