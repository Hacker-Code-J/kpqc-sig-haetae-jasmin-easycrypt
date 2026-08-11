from Jasmin require import JByte_array.

require import BArray32 BArray200.

clone SubByteArray as SBArray200_32  with theory Asmall <= BArray32,
                                          theory Abig <= BArray200.
