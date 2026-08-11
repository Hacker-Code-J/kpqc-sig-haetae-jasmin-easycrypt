from Jasmin require import JByte_array.

require import BArray64 BArray4032.

clone SubByteArray as SBArray4032_64  with theory Asmall <= BArray64,
                                           theory Abig <= BArray4032.
