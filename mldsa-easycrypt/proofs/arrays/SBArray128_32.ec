from Jasmin require import JByte_array.

require import BArray32 BArray128.

clone SubByteArray as SBArray128_32  with theory Asmall <= BArray32,
                                          theory Abig <= BArray128.
