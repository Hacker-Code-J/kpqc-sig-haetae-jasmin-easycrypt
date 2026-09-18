require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import
Array1 Array2 Array4 Array5 Array24 Array25 Array26 Array32 Array64 Array76
Array132 Array136 Array166 Array256 Array257 Array512 Array1024 Array1152
Array2048 Array2752 Array2948 Array4096 Array8192 WArray192 WArray304
WArray528 WArray1024 WArray1328 WArray2048 BArray1 BArray8 BArray16 BArray26
BArray32 BArray40 BArray64 BArray136 BArray192 BArray200 BArray257 BArray304
BArray512 BArray528 BArray1024 BArray1152 BArray1328 BArray2048 BArray2752
BArray2948 BArray8192 BArray32768.

abbrev jmode5_hb_z1_dsyms_words =
(BArray528.of_list32
[(W32.of_int 65536); (W32.of_int 65537); (W32.of_int 65538);
(W32.of_int 65539); (W32.of_int 131076); (W32.of_int 851974);
(W32.of_int 3145747); (W32.of_int 7733315); (W32.of_int 13369529);
(W32.of_int 16056709); (W32.of_int 13369978); (W32.of_int 7734086);
(W32.of_int 3146684); (W32.of_int 918508); (W32.of_int 132090);
(W32.of_int 66556); (W32.of_int 66557); (W32.of_int 66558);
(W32.of_int 66559); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0)]).

abbrev jmode5_hb_z1_symbol_words =
(BArray2048.of_list32
[(W32.of_int 65536); (W32.of_int 196610); (W32.of_int 262148);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 393221); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 458758); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 524295);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 589832);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 851981); (W32.of_int 851981);
(W32.of_int 851981); (W32.of_int 851981); (W32.of_int 851981);
(W32.of_int 851981); (W32.of_int 851981); (W32.of_int 917518);
(W32.of_int 1048591); (W32.of_int 1179665)]).

abbrev jmode5_h_dsyms_words =
(BArray528.of_list32
[(W32.of_int 7995392); (W32.of_int 7667834); (W32.of_int 6684911);
(W32.of_int 5308757); (W32.of_int 3867046); (W32.of_int 2556385);
(W32.of_int 1507848); (W32.of_int 852511); (W32.of_int 393772);
(W32.of_int 197170); (W32.of_int 66101); (W32.of_int 66102);
(W32.of_int 66103); (W32.of_int 66104); (W32.of_int 66105);
(W32.of_int 66106); (W32.of_int 66107); (W32.of_int 66108);
(W32.of_int 66109); (W32.of_int 66110); (W32.of_int 66111);
(W32.of_int 66112); (W32.of_int 66113); (W32.of_int 66114);
(W32.of_int 197187); (W32.of_int 393798); (W32.of_int 852556);
(W32.of_int 1573465); (W32.of_int 2556529); (W32.of_int 3867288);
(W32.of_int 5309139); (W32.of_int 6685476); (W32.of_int 7734154);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0)]).

abbrev jmode5_h_symbol_words =
(BArray2048.of_list32
[(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 131073); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 196610); (W32.of_int 196611);
(W32.of_int 196611); (W32.of_int 196611); (W32.of_int 196611);
(W32.of_int 196611); (W32.of_int 196611); (W32.of_int 196611);
(W32.of_int 196611); (W32.of_int 196611); (W32.of_int 196611);
(W32.of_int 196611); (W32.of_int 196611); (W32.of_int 196611);
(W32.of_int 196611); (W32.of_int 196611); (W32.of_int 196611);
(W32.of_int 196611); (W32.of_int 196611); (W32.of_int 196611);
(W32.of_int 196611); (W32.of_int 196611); (W32.of_int 196611);
(W32.of_int 196611); (W32.of_int 196611); (W32.of_int 196611);
(W32.of_int 196611); (W32.of_int 196611); (W32.of_int 196611);
(W32.of_int 196611); (W32.of_int 196611); (W32.of_int 196611);
(W32.of_int 196611); (W32.of_int 196611); (W32.of_int 196611);
(W32.of_int 196611); (W32.of_int 196611); (W32.of_int 196611);
(W32.of_int 196611); (W32.of_int 196611); (W32.of_int 196611);
(W32.of_int 262148); (W32.of_int 262148); (W32.of_int 262148);
(W32.of_int 262148); (W32.of_int 262148); (W32.of_int 262148);
(W32.of_int 262148); (W32.of_int 262148); (W32.of_int 262148);
(W32.of_int 262148); (W32.of_int 262148); (W32.of_int 262148);
(W32.of_int 262148); (W32.of_int 262148); (W32.of_int 262148);
(W32.of_int 262148); (W32.of_int 262148); (W32.of_int 262148);
(W32.of_int 262148); (W32.of_int 262148); (W32.of_int 262148);
(W32.of_int 262148); (W32.of_int 262148); (W32.of_int 262148);
(W32.of_int 262148); (W32.of_int 262148); (W32.of_int 262148);
(W32.of_int 262148); (W32.of_int 262148); (W32.of_int 327684);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 458758); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 589833); (W32.of_int 655369);
(W32.of_int 786443); (W32.of_int 917517); (W32.of_int 1048591);
(W32.of_int 1179665); (W32.of_int 1310739); (W32.of_int 1441813);
(W32.of_int 1572887); (W32.of_int 1572888); (W32.of_int 1638425);
(W32.of_int 1638425); (W32.of_int 1638425); (W32.of_int 1703962);
(W32.of_int 1703962); (W32.of_int 1703962); (W32.of_int 1703962);
(W32.of_int 1703962); (W32.of_int 1703962); (W32.of_int 1769498);
(W32.of_int 1769499); (W32.of_int 1769499); (W32.of_int 1769499);
(W32.of_int 1769499); (W32.of_int 1769499); (W32.of_int 1769499);
(W32.of_int 1769499); (W32.of_int 1769499); (W32.of_int 1769499);
(W32.of_int 1769499); (W32.of_int 1769499); (W32.of_int 1835035);
(W32.of_int 1835036); (W32.of_int 1835036); (W32.of_int 1835036);
(W32.of_int 1835036); (W32.of_int 1835036); (W32.of_int 1835036);
(W32.of_int 1835036); (W32.of_int 1835036); (W32.of_int 1835036);
(W32.of_int 1835036); (W32.of_int 1835036); (W32.of_int 1835036);
(W32.of_int 1835036); (W32.of_int 1835036); (W32.of_int 1835036);
(W32.of_int 1835036); (W32.of_int 1835036); (W32.of_int 1835036);
(W32.of_int 1835036); (W32.of_int 1900573); (W32.of_int 1900573);
(W32.of_int 1900573); (W32.of_int 1900573); (W32.of_int 1900573);
(W32.of_int 1900573); (W32.of_int 1900573); (W32.of_int 1900573);
(W32.of_int 1900573); (W32.of_int 1900573); (W32.of_int 1900573);
(W32.of_int 1900573); (W32.of_int 1900573); (W32.of_int 1900573);
(W32.of_int 1900573); (W32.of_int 1900573); (W32.of_int 1900573);
(W32.of_int 1900573); (W32.of_int 1900573); (W32.of_int 1900573);
(W32.of_int 1900573); (W32.of_int 1900573); (W32.of_int 1900573);
(W32.of_int 1900573); (W32.of_int 1900573); (W32.of_int 1900573);
(W32.of_int 1900573); (W32.of_int 1900573); (W32.of_int 1900573);
(W32.of_int 1966109); (W32.of_int 1966110); (W32.of_int 1966110);
(W32.of_int 1966110); (W32.of_int 1966110); (W32.of_int 1966110);
(W32.of_int 1966110); (W32.of_int 1966110); (W32.of_int 1966110);
(W32.of_int 1966110); (W32.of_int 1966110); (W32.of_int 1966110);
(W32.of_int 1966110); (W32.of_int 1966110); (W32.of_int 1966110);
(W32.of_int 1966110); (W32.of_int 1966110); (W32.of_int 1966110);
(W32.of_int 1966110); (W32.of_int 1966110); (W32.of_int 1966110);
(W32.of_int 1966110); (W32.of_int 1966110); (W32.of_int 1966110);
(W32.of_int 1966110); (W32.of_int 1966110); (W32.of_int 1966110);
(W32.of_int 1966110); (W32.of_int 1966110); (W32.of_int 1966110);
(W32.of_int 1966110); (W32.of_int 1966110); (W32.of_int 1966110);
(W32.of_int 1966110); (W32.of_int 1966110); (W32.of_int 1966110);
(W32.of_int 1966110); (W32.of_int 1966110); (W32.of_int 1966110);
(W32.of_int 1966110); (W32.of_int 1966110); (W32.of_int 2031647);
(W32.of_int 2031647); (W32.of_int 2031647); (W32.of_int 2031647);
(W32.of_int 2031647); (W32.of_int 2031647); (W32.of_int 2031647);
(W32.of_int 2031647); (W32.of_int 2031647); (W32.of_int 2031647);
(W32.of_int 2031647); (W32.of_int 2031647); (W32.of_int 2031647);
(W32.of_int 2031647); (W32.of_int 2031647); (W32.of_int 2031647);
(W32.of_int 2031647); (W32.of_int 2031647); (W32.of_int 2031647);
(W32.of_int 2031647); (W32.of_int 2031647); (W32.of_int 2031647);
(W32.of_int 2031647); (W32.of_int 2031647); (W32.of_int 2031647);
(W32.of_int 2031647); (W32.of_int 2031647); (W32.of_int 2031647);
(W32.of_int 2031647); (W32.of_int 2031647); (W32.of_int 2031647);
(W32.of_int 2031647); (W32.of_int 2031647); (W32.of_int 2031647);
(W32.of_int 2031647); (W32.of_int 2031647); (W32.of_int 2031647);
(W32.of_int 2031647); (W32.of_int 2031647); (W32.of_int 2031647);
(W32.of_int 2031647); (W32.of_int 2031647); (W32.of_int 2031647);
(W32.of_int 2031647); (W32.of_int 2031647); (W32.of_int 2031647);
(W32.of_int 2031647); (W32.of_int 2031647); (W32.of_int 2031647);
(W32.of_int 2031647); (W32.of_int 2031647); (W32.of_int 2097184);
(W32.of_int 2097184); (W32.of_int 2097184); (W32.of_int 2097184);
(W32.of_int 2097184); (W32.of_int 2097184); (W32.of_int 2097184);
(W32.of_int 2097184); (W32.of_int 2097184); (W32.of_int 2097184);
(W32.of_int 2097184); (W32.of_int 2097184); (W32.of_int 2097184);
(W32.of_int 2097184); (W32.of_int 2097184); (W32.of_int 2097184);
(W32.of_int 2097184); (W32.of_int 2097184); (W32.of_int 2097184);
(W32.of_int 2097184); (W32.of_int 2097184); (W32.of_int 2097184);
(W32.of_int 2097184); (W32.of_int 2097184); (W32.of_int 2097184);
(W32.of_int 2097184); (W32.of_int 2097184); (W32.of_int 2097184);
(W32.of_int 2097184); (W32.of_int 2097184); (W32.of_int 2097184);
(W32.of_int 2097184); (W32.of_int 2097184); (W32.of_int 2097184);
(W32.of_int 2097184); (W32.of_int 2097184); (W32.of_int 2097184);
(W32.of_int 2097184); (W32.of_int 2097184); (W32.of_int 2097184);
(W32.of_int 2097184); (W32.of_int 2097184); (W32.of_int 2097184);
(W32.of_int 2097184); (W32.of_int 2097184); (W32.of_int 2097184);
(W32.of_int 2097184); (W32.of_int 2097184); (W32.of_int 2097184);
(W32.of_int 2097184); (W32.of_int 2097184); (W32.of_int 2097184);
(W32.of_int 2097184); (W32.of_int 2097184); (W32.of_int 2097184);
(W32.of_int 2097184); (W32.of_int 2097184); (W32.of_int 2097184);
(W32.of_int 2097184)]).

abbrev jmode3_hb_z1_dsyms_words =
(BArray528.of_list32
[(W32.of_int 65536); (W32.of_int 65537); (W32.of_int 65538);
(W32.of_int 65539); (W32.of_int 524292); (W32.of_int 2424844);
(W32.of_int 7340081); (W32.of_int 14155937); (W32.of_int 17629561);
(W32.of_int 14156422); (W32.of_int 7340894); (W32.of_int 2491342);
(W32.of_int 525300); (W32.of_int 66556); (W32.of_int 66557);
(W32.of_int 66558); (W32.of_int 66559); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0)]).

abbrev jmode3_hb_z1_symbol_words =
(BArray2048.of_list32
[(W32.of_int 65536); (W32.of_int 196610); (W32.of_int 262148);
(W32.of_int 262148); (W32.of_int 262148); (W32.of_int 262148);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 393221); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 458758);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 524295);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 589833); (W32.of_int 589833); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 917517); (W32.of_int 1048591)]).

abbrev jmode3_h_dsyms_words =
(BArray528.of_list32
[(W32.of_int 17432576); (W32.of_int 13959434); (W32.of_int 7406047);
(W32.of_int 2622032); (W32.of_int 590456); (W32.of_int 66177);
(W32.of_int 66178); (W32.of_int 66179); (W32.of_int 66180);
(W32.of_int 66181); (W32.of_int 66182); (W32.of_int 66183);
(W32.of_int 66184); (W32.of_int 590473); (W32.of_int 2622098);
(W32.of_int 7406266); (W32.of_int 13959979); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0)]).

abbrev jmode3_h_symbol_words =
(BArray2048.of_list32
[(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 131073); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 196611); (W32.of_int 196611);
(W32.of_int 196611); (W32.of_int 196611); (W32.of_int 196611);
(W32.of_int 196611); (W32.of_int 196611); (W32.of_int 196611);
(W32.of_int 196611); (W32.of_int 196611); (W32.of_int 196611);
(W32.of_int 196611); (W32.of_int 196611); (W32.of_int 196611);
(W32.of_int 196611); (W32.of_int 196611); (W32.of_int 196611);
(W32.of_int 196611); (W32.of_int 196611); (W32.of_int 196611);
(W32.of_int 262148); (W32.of_int 262148); (W32.of_int 262148);
(W32.of_int 262148); (W32.of_int 327684); (W32.of_int 458758);
(W32.of_int 589832); (W32.of_int 720906); (W32.of_int 851980);
(W32.of_int 851981); (W32.of_int 851981); (W32.of_int 851981);
(W32.of_int 851981); (W32.of_int 917518); (W32.of_int 917518);
(W32.of_int 917518); (W32.of_int 917518); (W32.of_int 917518);
(W32.of_int 917518); (W32.of_int 917518); (W32.of_int 917518);
(W32.of_int 917518); (W32.of_int 917518); (W32.of_int 917518);
(W32.of_int 917518); (W32.of_int 917518); (W32.of_int 917518);
(W32.of_int 917518); (W32.of_int 917518); (W32.of_int 917518);
(W32.of_int 917518); (W32.of_int 917518); (W32.of_int 917518);
(W32.of_int 983055); (W32.of_int 983055); (W32.of_int 983055);
(W32.of_int 983055); (W32.of_int 983055); (W32.of_int 983055);
(W32.of_int 983055); (W32.of_int 983055); (W32.of_int 983055);
(W32.of_int 983055); (W32.of_int 983055); (W32.of_int 983055);
(W32.of_int 983055); (W32.of_int 983055); (W32.of_int 983055);
(W32.of_int 983055); (W32.of_int 983055); (W32.of_int 983055);
(W32.of_int 983055); (W32.of_int 983055); (W32.of_int 983055);
(W32.of_int 983055); (W32.of_int 983055); (W32.of_int 983055);
(W32.of_int 983055); (W32.of_int 983055); (W32.of_int 983055);
(W32.of_int 983055); (W32.of_int 983055); (W32.of_int 983055);
(W32.of_int 983055); (W32.of_int 983055); (W32.of_int 983055);
(W32.of_int 983055); (W32.of_int 983055); (W32.of_int 983055);
(W32.of_int 983055); (W32.of_int 983055); (W32.of_int 983055);
(W32.of_int 983055); (W32.of_int 983055); (W32.of_int 983055);
(W32.of_int 983055); (W32.of_int 983055); (W32.of_int 983055);
(W32.of_int 983055); (W32.of_int 983055); (W32.of_int 983055);
(W32.of_int 983055); (W32.of_int 983055); (W32.of_int 983055);
(W32.of_int 983055); (W32.of_int 983055); (W32.of_int 983055);
(W32.of_int 983055); (W32.of_int 983055); (W32.of_int 1048591);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592); (W32.of_int 1048592); (W32.of_int 1048592);
(W32.of_int 1048592)]).

abbrev jmode2_hb_z1_dsyms_words =
(BArray528.of_list32
[(W32.of_int 65536); (W32.of_int 65537); (W32.of_int 65538);
(W32.of_int 327683); (W32.of_int 3801096); (W32.of_int 16121922);
(W32.of_int 26083640); (W32.of_int 16188102); (W32.of_int 3867581);
(W32.of_int 328696); (W32.of_int 66557); (W32.of_int 66558);
(W32.of_int 66559); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0)]).

abbrev jmode2_hb_z1_symbol_words =
(BArray2048.of_list32
[(W32.of_int 65536); (W32.of_int 196610); (W32.of_int 196611);
(W32.of_int 196611); (W32.of_int 262148); (W32.of_int 262148);
(W32.of_int 262148); (W32.of_int 262148); (W32.of_int 262148);
(W32.of_int 262148); (W32.of_int 262148); (W32.of_int 262148);
(W32.of_int 262148); (W32.of_int 262148); (W32.of_int 262148);
(W32.of_int 262148); (W32.of_int 262148); (W32.of_int 262148);
(W32.of_int 262148); (W32.of_int 262148); (W32.of_int 262148);
(W32.of_int 262148); (W32.of_int 262148); (W32.of_int 262148);
(W32.of_int 262148); (W32.of_int 262148); (W32.of_int 262148);
(W32.of_int 262148); (W32.of_int 262148); (W32.of_int 262148);
(W32.of_int 262148); (W32.of_int 262148); (W32.of_int 262148);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 327685); (W32.of_int 327685); (W32.of_int 327685);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 393222); (W32.of_int 393222);
(W32.of_int 393222); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 458759); (W32.of_int 458759);
(W32.of_int 458759); (W32.of_int 524295); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 524296); (W32.of_int 524296);
(W32.of_int 524296); (W32.of_int 589833); (W32.of_int 589833);
(W32.of_int 655369); (W32.of_int 786443)]).

abbrev jmode2_h_dsyms_words =
(BArray528.of_list32
[(W32.of_int 25034752); (W32.of_int 16122238); (W32.of_int 4260468);
(W32.of_int 459445); (W32.of_int 66236); (W32.of_int 66237);
(W32.of_int 66238); (W32.of_int 66239); (W32.of_int 66240);
(W32.of_int 66241); (W32.of_int 459458); (W32.of_int 4260553);
(W32.of_int 16122634); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0)]).

abbrev jmode2_h_symbol_words =
(BArray2048.of_list32
[(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 65537);
(W32.of_int 65537); (W32.of_int 65537); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 131074); (W32.of_int 131074);
(W32.of_int 131074); (W32.of_int 196610); (W32.of_int 196611);
(W32.of_int 196611); (W32.of_int 196611); (W32.of_int 327684);
(W32.of_int 458758); (W32.of_int 589832); (W32.of_int 655370);
(W32.of_int 655370); (W32.of_int 655370); (W32.of_int 720906);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 720907);
(W32.of_int 720907); (W32.of_int 720907); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444); (W32.of_int 786444);
(W32.of_int 786444); (W32.of_int 786444)]).

abbrev jmode5_hb_z1_esyms =
(BArray528.of_list32
[(W32.of_int 2097152); (W32.of_int (-1)); (W32.of_int 1023);
(W32.of_int 1023); (W32.of_int 2097152); (W32.of_int (-1));
(W32.of_int 1024); (W32.of_int 1023); (W32.of_int 2097152);
(W32.of_int (-1)); (W32.of_int 1025); (W32.of_int 1023);
(W32.of_int 2097152); (W32.of_int (-1)); (W32.of_int 1026);
(W32.of_int 1023); (W32.of_int 4194304); (W32.of_int (-2147483648));
(W32.of_int 4); (W32.of_int 1022); (W32.of_int 27262976);
(W32.of_int (-1651910498)); (W32.of_int 6); (W32.of_int 197619);
(W32.of_int 100663296); (W32.of_int (-1431655765)); (W32.of_int 19);
(W32.of_int 328656); (W32.of_int 247463936); (W32.of_int (-1965493508));
(W32.of_int 67); (W32.of_int 394122); (W32.of_int 427819008);
(W32.of_int (-1600085855)); (W32.of_int 185); (W32.of_int 459572);
(W32.of_int 513802240); (W32.of_int (-2051066014)); (W32.of_int 389);
(W32.of_int 459531); (W32.of_int 427819008); (W32.of_int (-1600085855));
(W32.of_int 634); (W32.of_int 459572); (W32.of_int 247463936);
(W32.of_int (-1965493508)); (W32.of_int 838); (W32.of_int 394122);
(W32.of_int 100663296); (W32.of_int (-1431655765)); (W32.of_int 956);
(W32.of_int 328656); (W32.of_int 29360128); (W32.of_int (-1840700269));
(W32.of_int 1004); (W32.of_int 197618); (W32.of_int 4194304);
(W32.of_int (-2147483648)); (W32.of_int 1018); (W32.of_int 1022);
(W32.of_int 2097152); (W32.of_int (-1)); (W32.of_int 2043);
(W32.of_int 1023); (W32.of_int 2097152); (W32.of_int (-1));
(W32.of_int 2044); (W32.of_int 1023); (W32.of_int 2097152);
(W32.of_int (-1)); (W32.of_int 2045); (W32.of_int 1023);
(W32.of_int 2097152); (W32.of_int (-1)); (W32.of_int 2046);
(W32.of_int 1023); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0)]).

abbrev jmode5_h_esyms =
(BArray528.of_list32
[(W32.of_int 255852544); (W32.of_int (-2041869698)); (W32.of_int 0);
(W32.of_int 394118); (W32.of_int 245366784); (W32.of_int (-1945583475));
(W32.of_int 122); (W32.of_int 394123); (W32.of_int 213909504);
(W32.of_int (-1600085855)); (W32.of_int 239); (W32.of_int 394138);
(W32.of_int 169869312); (W32.of_int (-901412889)); (W32.of_int 341);
(W32.of_int 394159); (W32.of_int 123731968); (W32.of_int (-1965493508));
(W32.of_int 422); (W32.of_int 328645); (W32.of_int 81788928);
(W32.of_int (-770891565)); (W32.of_int 481); (W32.of_int 328665);
(W32.of_int 48234496); (W32.of_int (-1307163959)); (W32.of_int 520);
(W32.of_int 263145); (W32.of_int 27262976); (W32.of_int (-1651910498));
(W32.of_int 543); (W32.of_int 197619); (W32.of_int 12582912);
(W32.of_int (-1431655765)); (W32.of_int 556); (W32.of_int 132090);
(W32.of_int 6291456); (W32.of_int (-1431655765)); (W32.of_int 562);
(W32.of_int 66557); (W32.of_int 2097152); (W32.of_int (-1));
(W32.of_int 1588); (W32.of_int 1023); (W32.of_int 2097152);
(W32.of_int (-1)); (W32.of_int 1589); (W32.of_int 1023);
(W32.of_int 2097152); (W32.of_int (-1)); (W32.of_int 1590);
(W32.of_int 1023); (W32.of_int 2097152); (W32.of_int (-1));
(W32.of_int 1591); (W32.of_int 1023); (W32.of_int 2097152);
(W32.of_int (-1)); (W32.of_int 1592); (W32.of_int 1023);
(W32.of_int 2097152); (W32.of_int (-1)); (W32.of_int 1593);
(W32.of_int 1023); (W32.of_int 2097152); (W32.of_int (-1));
(W32.of_int 1594); (W32.of_int 1023); (W32.of_int 2097152);
(W32.of_int (-1)); (W32.of_int 1595); (W32.of_int 1023);
(W32.of_int 2097152); (W32.of_int (-1)); (W32.of_int 1596);
(W32.of_int 1023); (W32.of_int 2097152); (W32.of_int (-1));
(W32.of_int 1597); (W32.of_int 1023); (W32.of_int 2097152);
(W32.of_int (-1)); (W32.of_int 1598); (W32.of_int 1023);
(W32.of_int 2097152); (W32.of_int (-1)); (W32.of_int 1599);
(W32.of_int 1023); (W32.of_int 2097152); (W32.of_int (-1));
(W32.of_int 1600); (W32.of_int 1023); (W32.of_int 2097152);
(W32.of_int (-1)); (W32.of_int 1601); (W32.of_int 1023);
(W32.of_int 6291456); (W32.of_int (-1431655765)); (W32.of_int 579);
(W32.of_int 66557); (W32.of_int 12582912); (W32.of_int (-1431655765));
(W32.of_int 582); (W32.of_int 132090); (W32.of_int 27262976);
(W32.of_int (-1651910498)); (W32.of_int 588); (W32.of_int 197619);
(W32.of_int 50331648); (W32.of_int (-1431655765)); (W32.of_int 601);
(W32.of_int 263144); (W32.of_int 81788928); (W32.of_int (-770891565));
(W32.of_int 625); (W32.of_int 328665); (W32.of_int 123731968);
(W32.of_int (-1965493508)); (W32.of_int 664); (W32.of_int 328645);
(W32.of_int 169869312); (W32.of_int (-901412889)); (W32.of_int 723);
(W32.of_int 394159); (W32.of_int 213909504); (W32.of_int (-1600085855));
(W32.of_int 804); (W32.of_int 394138); (W32.of_int 247463936);
(W32.of_int (-1965493508)); (W32.of_int 906); (W32.of_int 394122)]).

abbrev jmode3_hb_z1_esyms =
(BArray528.of_list32
[(W32.of_int 2097152); (W32.of_int (-1)); (W32.of_int 1023);
(W32.of_int 1023); (W32.of_int 2097152); (W32.of_int (-1));
(W32.of_int 1024); (W32.of_int 1023); (W32.of_int 2097152);
(W32.of_int (-1)); (W32.of_int 1025); (W32.of_int 1023);
(W32.of_int 2097152); (W32.of_int (-1)); (W32.of_int 1026);
(W32.of_int 1023); (W32.of_int 16777216); (W32.of_int (-2147483648));
(W32.of_int 4); (W32.of_int 132088); (W32.of_int 77594624);
(W32.of_int (-580400985)); (W32.of_int 12); (W32.of_int 328667);
(W32.of_int 234881024); (W32.of_int (-1840700269)); (W32.of_int 49);
(W32.of_int 394128); (W32.of_int 452984832); (W32.of_int (-1749801490));
(W32.of_int 161); (W32.of_int 459560); (W32.of_int 564133888);
(W32.of_int (-207563475)); (W32.of_int 377); (W32.of_int 525043);
(W32.of_int 452984832); (W32.of_int (-1749801490)); (W32.of_int 646);
(W32.of_int 459560); (W32.of_int 234881024); (W32.of_int (-1840700269));
(W32.of_int 862); (W32.of_int 394128); (W32.of_int 79691776);
(W32.of_int (-678152730)); (W32.of_int 974); (W32.of_int 328666);
(W32.of_int 16777216); (W32.of_int (-2147483648)); (W32.of_int 1012);
(W32.of_int 132088); (W32.of_int 2097152); (W32.of_int (-1));
(W32.of_int 2043); (W32.of_int 1023); (W32.of_int 2097152);
(W32.of_int (-1)); (W32.of_int 2044); (W32.of_int 1023);
(W32.of_int 2097152); (W32.of_int (-1)); (W32.of_int 2045);
(W32.of_int 1023); (W32.of_int 2097152); (W32.of_int (-1));
(W32.of_int 2046); (W32.of_int 1023); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0)]).

abbrev jmode3_h_esyms =
(BArray528.of_list32
[(W32.of_int 557842432); (W32.of_int (-161464935)); (W32.of_int 0);
(W32.of_int 525046); (W32.of_int 446693376); (W32.of_int (-1713954085));
(W32.of_int 266); (W32.of_int 459563); (W32.of_int 236978176);
(W32.of_int (-1862419446)); (W32.of_int 479); (W32.of_int 394127);
(W32.of_int 83886080); (W32.of_int (-858993459)); (W32.of_int 592);
(W32.of_int 328664); (W32.of_int 18874368); (W32.of_int (-477218588));
(W32.of_int 632); (W32.of_int 197623); (W32.of_int 2097152);
(W32.of_int (-1)); (W32.of_int 1664); (W32.of_int 1023);
(W32.of_int 2097152); (W32.of_int (-1)); (W32.of_int 1665);
(W32.of_int 1023); (W32.of_int 2097152); (W32.of_int (-1));
(W32.of_int 1666); (W32.of_int 1023); (W32.of_int 2097152);
(W32.of_int (-1)); (W32.of_int 1667); (W32.of_int 1023);
(W32.of_int 2097152); (W32.of_int (-1)); (W32.of_int 1668);
(W32.of_int 1023); (W32.of_int 2097152); (W32.of_int (-1));
(W32.of_int 1669); (W32.of_int 1023); (W32.of_int 2097152);
(W32.of_int (-1)); (W32.of_int 1670); (W32.of_int 1023);
(W32.of_int 2097152); (W32.of_int (-1)); (W32.of_int 1671);
(W32.of_int 1023); (W32.of_int 18874368); (W32.of_int (-477218588));
(W32.of_int 649); (W32.of_int 197623); (W32.of_int 83886080);
(W32.of_int (-858993459)); (W32.of_int 658); (W32.of_int 328664);
(W32.of_int 236978176); (W32.of_int (-1862419446)); (W32.of_int 698);
(W32.of_int 394127); (W32.of_int 446693376); (W32.of_int (-1713954085));
(W32.of_int 811); (W32.of_int 459563); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0)]).

abbrev jmode2_hb_z1_esyms =
(BArray528.of_list32
[(W32.of_int 2097152); (W32.of_int (-1)); (W32.of_int 1023);
(W32.of_int 1023); (W32.of_int 2097152); (W32.of_int (-1));
(W32.of_int 1024); (W32.of_int 1023); (W32.of_int 2097152);
(W32.of_int (-1)); (W32.of_int 1025); (W32.of_int 1023);
(W32.of_int 10485760); (W32.of_int (-858993459)); (W32.of_int 3);
(W32.of_int 132091); (W32.of_int 121634816); (W32.of_int (-1925330167));
(W32.of_int 8); (W32.of_int 328646); (W32.of_int 515899392);
(W32.of_int (-2060187564)); (W32.of_int 66); (W32.of_int 459530);
(W32.of_int 834666496); (W32.of_int (-1532375266)); (W32.of_int 312);
(W32.of_int 524914); (W32.of_int 517996544); (W32.of_int (-2069235255));
(W32.of_int 710); (W32.of_int 459529); (W32.of_int 123731968);
(W32.of_int (-1965493508)); (W32.of_int 957); (W32.of_int 328645);
(W32.of_int 10485760); (W32.of_int (-858993459)); (W32.of_int 1016);
(W32.of_int 132091); (W32.of_int 2097152); (W32.of_int (-1));
(W32.of_int 2044); (W32.of_int 1023); (W32.of_int 2097152);
(W32.of_int (-1)); (W32.of_int 2045); (W32.of_int 1023);
(W32.of_int 2097152); (W32.of_int (-1)); (W32.of_int 2046);
(W32.of_int 1023); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0)]).

abbrev jmode2_h_esyms =
(BArray528.of_list32
[(W32.of_int 801112064); (W32.of_int (-1416664605)); (W32.of_int 0);
(W32.of_int 524930); (W32.of_int 515899392); (W32.of_int (-2060187564));
(W32.of_int 382); (W32.of_int 459530); (W32.of_int 136314880);
(W32.of_int (-66076419)); (W32.of_int 628); (W32.of_int 394175);
(W32.of_int 14680064); (W32.of_int (-1840700269)); (W32.of_int 693);
(W32.of_int 132089); (W32.of_int 2097152); (W32.of_int (-1));
(W32.of_int 1723); (W32.of_int 1023); (W32.of_int 2097152);
(W32.of_int (-1)); (W32.of_int 1724); (W32.of_int 1023);
(W32.of_int 2097152); (W32.of_int (-1)); (W32.of_int 1725);
(W32.of_int 1023); (W32.of_int 2097152); (W32.of_int (-1));
(W32.of_int 1726); (W32.of_int 1023); (W32.of_int 2097152);
(W32.of_int (-1)); (W32.of_int 1727); (W32.of_int 1023);
(W32.of_int 2097152); (W32.of_int (-1)); (W32.of_int 1728);
(W32.of_int 1023); (W32.of_int 14680064); (W32.of_int (-1840700269));
(W32.of_int 706); (W32.of_int 132089); (W32.of_int 136314880);
(W32.of_int (-66076419)); (W32.of_int 713); (W32.of_int 394175);
(W32.of_int 515899392); (W32.of_int (-2060187564)); (W32.of_int 778);
(W32.of_int 459530); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0); (W32.of_int 0); (W32.of_int 0); (W32.of_int 0);
(W32.of_int 0)]).

abbrev jzetas_inv =
(BArray1024.of_list32
[(W32.of_int 20175); (W32.of_int (-8241)); (W32.of_int (-26554));
(W32.of_int (-31612)); (W32.of_int (-29003)); (W32.of_int 12979);
(W32.of_int (-17463)); (W32.of_int (-7947)); (W32.of_int 12831);
(W32.of_int (-25492)); (W32.of_int 14203); (W32.of_int 21126);
(W32.of_int (-9217)); (W32.of_int (-2931)); (W32.of_int 8099);
(W32.of_int (-13803)); (W32.of_int (-23078)); (W32.of_int (-15822));
(W32.of_int 27740); (W32.of_int 22820); (W32.of_int 16251);
(W32.of_int (-7655)); (W32.of_int 20206); (W32.of_int 994);
(W32.of_int 5823); (W32.of_int 9488); (W32.of_int (-23224));
(W32.of_int 1035); (W32.of_int (-8889)); (W32.of_int 21944);
(W32.of_int 27010); (W32.of_int (-21921)); (W32.of_int (-26934));
(W32.of_int 23751); (W32.of_int (-8908)); (W32.of_int (-10770));
(W32.of_int (-65)); (W32.of_int 3528); (W32.of_int 22805);
(W32.of_int 17737); (W32.of_int 4800); (W32.of_int 27298);
(W32.of_int (-1761)); (W32.of_int 10226); (W32.of_int 7729);
(W32.of_int 11242); (W32.of_int (-12069)); (W32.of_int (-13882));
(W32.of_int 22243); (W32.of_int 31368); (W32.of_int 2202);
(W32.of_int (-18282)); (W32.of_int 3304); (W32.of_int 8253);
(W32.of_int 26851); (W32.of_int (-17261)); (W32.of_int (-25636));
(W32.of_int 10865); (W32.of_int 26985); (W32.of_int (-10639));
(W32.of_int (-3808)); (W32.of_int 10170); (W32.of_int 25912);
(W32.of_int 29735); (W32.of_int 17374); (W32.of_int (-6080));
(W32.of_int (-21454)); (W32.of_int (-10672)); (W32.of_int 9939);
(W32.of_int 20316); (W32.of_int (-13283)); (W32.of_int 28190);
(W32.of_int 30274); (W32.of_int (-21422)); (W32.of_int 18166);
(W32.of_int (-7382)); (W32.of_int (-13642)); (W32.of_int (-5920));
(W32.of_int (-17494)); (W32.of_int (-17182)); (W32.of_int (-7742));
(W32.of_int (-23439)); (W32.of_int 16630); (W32.of_int 30332);
(W32.of_int 12882); (W32.of_int (-12380)); (W32.of_int 16160);
(W32.of_int (-28521)); (W32.of_int (-28254)); (W32.of_int 25921);
(W32.of_int 12543); (W32.of_int 21900); (W32.of_int 2648);
(W32.of_int 23016); (W32.of_int (-10971)); (W32.of_int (-1025));
(W32.of_int 16319); (W32.of_int 31332); (W32.of_int 1311);
(W32.of_int (-689)); (W32.of_int 19194); (W32.of_int 24162);
(W32.of_int (-14864)); (W32.of_int 8796); (W32.of_int 11808);
(W32.of_int (-7682)); (W32.of_int (-28847)); (W32.of_int 30317);
(W32.of_int 7401); (W32.of_int (-13633)); (W32.of_int (-30980));
(W32.of_int (-5764)); (W32.of_int (-13666)); (W32.of_int (-23475));
(W32.of_int 15739); (W32.of_int (-16588)); (W32.of_int 28772);
(W32.of_int 3529); (W32.of_int (-25555)); (W32.of_int (-2464));
(W32.of_int 9190); (W32.of_int 7374); (W32.of_int 21224);
(W32.of_int (-1657)); (W32.of_int 13857); (W32.of_int (-787));
(W32.of_int (-3350)); (W32.of_int 27989); (W32.of_int (-17671));
(W32.of_int (-9560)); (W32.of_int 21442); (W32.of_int (-30362));
(W32.of_int (-23844)); (W32.of_int 9874); (W32.of_int 18586);
(W32.of_int 9522); (W32.of_int (-5876)); (W32.of_int (-29439));
(W32.of_int (-2844)); (W32.of_int 16405); (W32.of_int (-5322));
(W32.of_int (-5913)); (W32.of_int 31064); (W32.of_int (-29563));
(W32.of_int (-7929)); (W32.of_int 14501); (W32.of_int (-12050));
(W32.of_int 18832); (W32.of_int 4127); (W32.of_int 16186);
(W32.of_int (-18731)); (W32.of_int (-21502)); (W32.of_int 27727);
(W32.of_int 10623); (W32.of_int (-11261)); (W32.of_int (-24985));
(W32.of_int 31327); (W32.of_int (-1160)); (W32.of_int (-28710));
(W32.of_int 14941); (W32.of_int (-15510)); (W32.of_int (-6759));
(W32.of_int (-22131)); (W32.of_int 29051); (W32.of_int (-16507));
(W32.of_int (-29068)); (W32.of_int (-9790)); (W32.of_int 5342);
(W32.of_int (-1806)); (W32.of_int 17631); (W32.of_int (-31352));
(W32.of_int 12442); (W32.of_int (-8311)); (W32.of_int (-1488));
(W32.of_int 27685); (W32.of_int (-3970)); (W32.of_int (-15546));
(W32.of_int (-835)); (W32.of_int (-4538)); (W32.of_int 29942);
(W32.of_int (-598)); (W32.of_int 19555); (W32.of_int 16267);
(W32.of_int (-17456)); (W32.of_int (-20353)); (W32.of_int (-19813));
(W32.of_int 9604); (W32.of_int 3761); (W32.of_int (-32114));
(W32.of_int (-12697)); (W32.of_int (-7814)); (W32.of_int (-11591));
(W32.of_int 9430); (W32.of_int (-10615)); (W32.of_int 11459);
(W32.of_int (-7597)); (W32.of_int (-27690)); (W32.of_int 19129);
(W32.of_int (-26533)); (W32.of_int 7941); (W32.of_int (-19616));
(W32.of_int 16608); (W32.of_int 23970); (W32.of_int (-30608));
(W32.of_int 2391); (W32.of_int 15130); (W32.of_int 19646);
(W32.of_int 21464); (W32.of_int (-7893)); (W32.of_int 8577);
(W32.of_int (-29643)); (W32.of_int 17941); (W32.of_int (-11782));
(W32.of_int 32076); (W32.of_int 19725); (W32.of_int 1296);
(W32.of_int (-18239)); (W32.of_int (-16446)); (W32.of_int 12296);
(W32.of_int (-16304)); (W32.of_int (-9383)); (W32.of_int 10049);
(W32.of_int 6789); (W32.of_int 22562); (W32.of_int (-25252));
(W32.of_int (-30820)); (W32.of_int 11361); (W32.of_int (-20143));
(W32.of_int 20035); (W32.of_int 29133); (W32.of_int 27527);
(W32.of_int (-28147)); (W32.of_int 29104); (W32.of_int (-22431));
(W32.of_int (-22935)); (W32.of_int (-10681)); (W32.of_int 19553);
(W32.of_int (-6241)); (W32.of_int 22946); (W32.of_int 16039);
(W32.of_int (-17599)); (W32.of_int (-21408)); (W32.of_int (-13744));
(W32.of_int (-32144)); (W32.of_int 8851); (W32.of_int (-22859));
(W32.of_int 30985); (W32.of_int (-9395)); (W32.of_int 31218);
(W32.of_int (-19064)); (W32.of_int (-20243)); (W32.of_int (-30746));
(W32.of_int (-22229)); (W32.of_int 16505); (W32.of_int (-26964));
(W32.of_int (-29720))]).

abbrev jzetas =
(BArray1024.of_list32
[(W32.of_int 0); (W32.of_int 26964); (W32.of_int (-16505));
(W32.of_int 22229); (W32.of_int 30746); (W32.of_int 20243);
(W32.of_int 19064); (W32.of_int (-31218)); (W32.of_int 9395);
(W32.of_int (-30985)); (W32.of_int 22859); (W32.of_int (-8851));
(W32.of_int 32144); (W32.of_int 13744); (W32.of_int 21408);
(W32.of_int 17599); (W32.of_int (-16039)); (W32.of_int (-22946));
(W32.of_int 6241); (W32.of_int (-19553)); (W32.of_int 10681);
(W32.of_int 22935); (W32.of_int 22431); (W32.of_int (-29104));
(W32.of_int 28147); (W32.of_int (-27527)); (W32.of_int (-29133));
(W32.of_int (-20035)); (W32.of_int 20143); (W32.of_int (-11361));
(W32.of_int 30820); (W32.of_int 25252); (W32.of_int (-22562));
(W32.of_int (-6789)); (W32.of_int (-10049)); (W32.of_int 9383);
(W32.of_int 16304); (W32.of_int (-12296)); (W32.of_int 16446);
(W32.of_int 18239); (W32.of_int (-1296)); (W32.of_int (-19725));
(W32.of_int (-32076)); (W32.of_int 11782); (W32.of_int (-17941));
(W32.of_int 29643); (W32.of_int (-8577)); (W32.of_int 7893);
(W32.of_int (-21464)); (W32.of_int (-19646)); (W32.of_int (-15130));
(W32.of_int (-2391)); (W32.of_int 30608); (W32.of_int (-23970));
(W32.of_int (-16608)); (W32.of_int 19616); (W32.of_int (-7941));
(W32.of_int 26533); (W32.of_int (-19129)); (W32.of_int 27690);
(W32.of_int 7597); (W32.of_int (-11459)); (W32.of_int 10615);
(W32.of_int (-9430)); (W32.of_int 11591); (W32.of_int 7814);
(W32.of_int 12697); (W32.of_int 32114); (W32.of_int (-3761));
(W32.of_int (-9604)); (W32.of_int 19813); (W32.of_int 20353);
(W32.of_int 17456); (W32.of_int (-16267)); (W32.of_int (-19555));
(W32.of_int 598); (W32.of_int (-29942)); (W32.of_int 4538); (W32.of_int 835);
(W32.of_int 15546); (W32.of_int 3970); (W32.of_int (-27685));
(W32.of_int 1488); (W32.of_int 8311); (W32.of_int (-12442));
(W32.of_int 31352); (W32.of_int (-17631)); (W32.of_int 1806);
(W32.of_int (-5342)); (W32.of_int 9790); (W32.of_int 29068);
(W32.of_int 16507); (W32.of_int (-29051)); (W32.of_int 22131);
(W32.of_int 6759); (W32.of_int 15510); (W32.of_int (-14941));
(W32.of_int 28710); (W32.of_int 1160); (W32.of_int (-31327));
(W32.of_int 24985); (W32.of_int 11261); (W32.of_int (-10623));
(W32.of_int (-27727)); (W32.of_int 21502); (W32.of_int 18731);
(W32.of_int (-16186)); (W32.of_int (-4127)); (W32.of_int (-18832));
(W32.of_int 12050); (W32.of_int (-14501)); (W32.of_int 7929);
(W32.of_int 29563); (W32.of_int (-31064)); (W32.of_int 5913);
(W32.of_int 5322); (W32.of_int (-16405)); (W32.of_int 2844);
(W32.of_int 29439); (W32.of_int 5876); (W32.of_int (-9522));
(W32.of_int (-18586)); (W32.of_int (-9874)); (W32.of_int 23844);
(W32.of_int 30362); (W32.of_int (-21442)); (W32.of_int 9560);
(W32.of_int 17671); (W32.of_int (-27989)); (W32.of_int 3350);
(W32.of_int 787); (W32.of_int (-13857)); (W32.of_int 1657);
(W32.of_int (-21224)); (W32.of_int (-7374)); (W32.of_int (-9190));
(W32.of_int 2464); (W32.of_int 25555); (W32.of_int (-3529));
(W32.of_int (-28772)); (W32.of_int 16588); (W32.of_int (-15739));
(W32.of_int 23475); (W32.of_int 13666); (W32.of_int 5764);
(W32.of_int 30980); (W32.of_int 13633); (W32.of_int (-7401));
(W32.of_int (-30317)); (W32.of_int 28847); (W32.of_int 7682);
(W32.of_int (-11808)); (W32.of_int (-8796)); (W32.of_int 14864);
(W32.of_int (-24162)); (W32.of_int (-19194)); (W32.of_int 689);
(W32.of_int (-1311)); (W32.of_int (-31332)); (W32.of_int (-16319));
(W32.of_int 1025); (W32.of_int 10971); (W32.of_int (-23016));
(W32.of_int (-2648)); (W32.of_int (-21900)); (W32.of_int (-12543));
(W32.of_int (-25921)); (W32.of_int 28254); (W32.of_int 28521);
(W32.of_int (-16160)); (W32.of_int 12380); (W32.of_int (-12882));
(W32.of_int (-30332)); (W32.of_int (-16630)); (W32.of_int 23439);
(W32.of_int 7742); (W32.of_int 17182); (W32.of_int 17494); (W32.of_int 5920);
(W32.of_int 13642); (W32.of_int 7382); (W32.of_int (-18166));
(W32.of_int 21422); (W32.of_int (-30274)); (W32.of_int (-28190));
(W32.of_int 13283); (W32.of_int (-20316)); (W32.of_int (-9939));
(W32.of_int 10672); (W32.of_int 21454); (W32.of_int 6080);
(W32.of_int (-17374)); (W32.of_int (-29735)); (W32.of_int (-25912));
(W32.of_int (-10170)); (W32.of_int 3808); (W32.of_int 10639);
(W32.of_int (-26985)); (W32.of_int (-10865)); (W32.of_int 25636);
(W32.of_int 17261); (W32.of_int (-26851)); (W32.of_int (-8253));
(W32.of_int (-3304)); (W32.of_int 18282); (W32.of_int (-2202));
(W32.of_int (-31368)); (W32.of_int (-22243)); (W32.of_int 13882);
(W32.of_int 12069); (W32.of_int (-11242)); (W32.of_int (-7729));
(W32.of_int (-10226)); (W32.of_int 1761); (W32.of_int (-27298));
(W32.of_int (-4800)); (W32.of_int (-17737)); (W32.of_int (-22805));
(W32.of_int (-3528)); (W32.of_int 65); (W32.of_int 10770); (W32.of_int 8908);
(W32.of_int (-23751)); (W32.of_int 26934); (W32.of_int 21921);
(W32.of_int (-27010)); (W32.of_int (-21944)); (W32.of_int 8889);
(W32.of_int (-1035)); (W32.of_int 23224); (W32.of_int (-9488));
(W32.of_int (-5823)); (W32.of_int (-994)); (W32.of_int (-20206));
(W32.of_int 7655); (W32.of_int (-16251)); (W32.of_int (-22820));
(W32.of_int (-27740)); (W32.of_int 15822); (W32.of_int 23078);
(W32.of_int 13803); (W32.of_int (-8099)); (W32.of_int 2931);
(W32.of_int 9217); (W32.of_int (-21126)); (W32.of_int (-14203));
(W32.of_int 25492); (W32.of_int (-12831)); (W32.of_int 7947);
(W32.of_int 17463); (W32.of_int (-12979)); (W32.of_int 29003);
(W32.of_int 31612); (W32.of_int 26554); (W32.of_int 8241);
(W32.of_int (-20175))]).

abbrev jcdt83_lo =
(BArray1328.of_list64
[(W64.of_int 767145465612017192); (W64.of_int 5708348702329189102);
(W64.of_int (-2986515139374512380)); (W64.of_int 7315992374869995997);
(W64.of_int (-7240595365343461296)); (W64.of_int 195392804384423549);
(W64.of_int 956154643040125894); (W64.of_int (-387090023418055461));
(W64.of_int (-6839973910006153600)); (W64.of_int 1752582669294548863);
(W64.of_int 4800866410357959959); (W64.of_int 3667394071068326311);
(W64.of_int 7998665258853332362); (W64.of_int 1039285826929998432);
(W64.of_int (-5325172712904727316)); (W64.of_int 8302908906926177525);
(W64.of_int 8594781109006420459); (W64.of_int (-5174631349969467793));
(W64.of_int 8655299069842505098); (W64.of_int (-5152057033357634684));
(W64.of_int (-7176303742971548487)); (W64.of_int (-4736152177093509389));
(W64.of_int 9014672416777812641); (W64.of_int 4984359074700584923);
(W64.of_int (-2887029340802828403)); (W64.of_int (-7587158779559040837));
(W64.of_int (-3226889267410948733)); (W64.of_int 2938417944103238712);
(W64.of_int (-2279529697979260704)); (W64.of_int 7021364755983520008);
(W64.of_int (-5699981999439543809)); (W64.of_int (-70422136106126370));
(W64.of_int 4972332497587472585); (W64.of_int (-1005689185452603130));
(W64.of_int (-6353529195586080244)); (W64.of_int 418384427087521389);
(W64.of_int (-9048179565493353424)); (W64.of_int 5860820516995035126);
(W64.of_int 6144759436214999286); (W64.of_int 2057362318352304828);
(W64.of_int (-1833664629943763904)); (W64.of_int (-5686588886910490621));
(W64.of_int 5484949054085740288); (W64.of_int 8266722527040612711);
(W64.of_int (-1736797318333312100)); (W64.of_int (-7619591592559817454));
(W64.of_int (-5653300277827871264)); (W64.of_int (-2805408635628270210));
(W64.of_int 4201673510770952224); (W64.of_int (-5542802630767400586));
(W64.of_int (-963011482571663333)); (W64.of_int (-7391284510404850280));
(W64.of_int 6273169357352979088); (W64.of_int 456876313255139270);
(W64.of_int (-4092082967717326062)); (W64.of_int 1621190494596410906);
(W64.of_int (-2053365783733785617)); (W64.of_int (-6670276636412627550));
(W64.of_int 7115633661535853623); (W64.of_int (-3128754293651494253));
(W64.of_int 6935088653178559021); (W64.of_int 3249567803139592707);
(W64.of_int 3228497872348613985); (W64.of_int 2608497649573788682);
(W64.of_int (-5557320224091228199)); (W64.of_int 6459840567858685922);
(W64.of_int (-9221884450999136146)); (W64.of_int 8703981739283037248);
(W64.of_int (-8798104171703783439)); (W64.of_int (-2620674995057133332));
(W64.of_int (-6683477291279709549)); (W64.of_int (-202686826310768826));
(W64.of_int 203645829219293199); (W64.of_int (-4039817201464381253));
(W64.of_int 6618745965193433548); (W64.of_int (-3860679526618670689));
(W64.of_int 2071704274388800110); (W64.of_int 6471675482471026258);
(W64.of_int (-8724390486189509312)); (W64.of_int (-6332167634226479284));
(W64.of_int (-4578558332206810384)); (W64.of_int (-3298093711129306011));
(W64.of_int (-2366758840984369973)); (W64.of_int (-1692001402250280346));
(W64.of_int (-1205041686108142602)); (W64.of_int (-854982138418773943));
(W64.of_int (-604316758675095801)); (W64.of_int (-425523836596219738));
(W64.of_int (-298492804824911630)); (W64.of_int (-208590077685954889));
(W64.of_int (-145211944389320022)); (W64.of_int (-100706867223975277));
(W64.of_int (-69576574077182978)); (W64.of_int (-47886531750657860));
(W64.of_int (-32832905617300018)); (W64.of_int (-22425909576001919));
(W64.of_int (-15259309166283028)); (W64.of_int (-10343392321865658));
(W64.of_int (-6984474311914934)); (W64.of_int (-4698360669985171));
(W64.of_int (-3148474636774176)); (W64.of_int (-2101815542697524));
(W64.of_int (-1397748079304948)); (W64.of_int (-925981864506689));
(W64.of_int (-611103417999386)); (W64.of_int (-401758429195526));
(W64.of_int (-263119325522126)); (W64.of_int (-171663273123127));
(W64.of_int (-111567669955921)); (W64.of_int (-72232911965015));
(W64.of_int (-46587256485616)); (W64.of_int (-29931872023758));
(W64.of_int (-19157324087377)); (W64.of_int (-12214326882085));
(W64.of_int (-7757780197058)); (W64.of_int (-4908379885196));
(W64.of_int (-3093649914360)); (W64.of_int (-1942388117830));
(W64.of_int (-1214876870458)); (W64.of_int (-756936566813));
(W64.of_int (-469804590101)); (W64.of_int (-290472590512));
(W64.of_int (-178905127292)); (W64.of_int (-109766482441));
(W64.of_int (-67088124190)); (W64.of_int (-40846054556));
(W64.of_int (-24773237568)); (W64.of_int (-14967292570));
(W64.of_int (-9008058511)); (W64.of_int (-5400652945));
(W64.of_int (-3225433705)); (W64.of_int (-1918917990));
(W64.of_int (-1137236592)); (W64.of_int (-671384067));
(W64.of_int (-394835975)); (W64.of_int (-231306359));
(W64.of_int (-134984312)); (W64.of_int (-78469989));
(W64.of_int (-45441029)); (W64.of_int (-26212999)); (W64.of_int (-15062913));
(W64.of_int (-8622330)); (W64.of_int (-4916583)); (W64.of_int (-2792704));
(W64.of_int (-1580188)); (W64.of_int (-890665)); (W64.of_int (-500082));
(W64.of_int (-279697)); (W64.of_int (-155831)); (W64.of_int (-86484));
(W64.of_int (-47811)); (W64.of_int (-26328)); (W64.of_int (-14441));
(W64.of_int (-7889)); (W64.of_int (-4292)); (W64.of_int (-2325));
(W64.of_int (-1253)); (W64.of_int (-672)); (W64.of_int (-358));
(W64.of_int (-189)); (W64.of_int (-98)); (W64.of_int (-50));
(W64.of_int (-25)); (W64.of_int (-12)); (W64.of_int (-5)); (W64.of_int (-2))]
).

abbrev jcdt83_hi =
(BArray304.of_list32
[(W32.of_int 25509); (W32.of_int 50968); (W32.of_int 76278);
(W32.of_int 101343); (W32.of_int 126067); (W32.of_int 150361);
(W32.of_int 174138); (W32.of_int 197318); (W32.of_int 219830);
(W32.of_int 241607); (W32.of_int 262590); (W32.of_int 282730);
(W32.of_int 301985); (W32.of_int 320323); (W32.of_int 337718);
(W32.of_int 354156); (W32.of_int 369628); (W32.of_int 384134);
(W32.of_int 397682); (W32.of_int 410285); (W32.of_int 421964);
(W32.of_int 432744); (W32.of_int 442656); (W32.of_int 451734);
(W32.of_int 460015); (W32.of_int 467541); (W32.of_int 474353);
(W32.of_int 480496); (W32.of_int 486012); (W32.of_int 490948);
(W32.of_int 495346); (W32.of_int 499250); (W32.of_int 502703);
(W32.of_int 505743); (W32.of_int 508411); (W32.of_int 510743);
(W32.of_int 512772); (W32.of_int 514532); (W32.of_int 516052);
(W32.of_int 517360); (W32.of_int 518480); (W32.of_int 519437);
(W32.of_int 520251); (W32.of_int 520940); (W32.of_int 521521);
(W32.of_int 522010); (W32.of_int 522419); (W32.of_int 522760);
(W32.of_int 523044); (W32.of_int 523278); (W32.of_int 523471);
(W32.of_int 523630); (W32.of_int 523760); (W32.of_int 523866);
(W32.of_int 523951); (W32.of_int 524021); (W32.of_int 524076);
(W32.of_int 524121); (W32.of_int 524157); (W32.of_int 524185);
(W32.of_int 524208); (W32.of_int 524226); (W32.of_int 524240);
(W32.of_int 524251); (W32.of_int 524259); (W32.of_int 524266);
(W32.of_int 524271); (W32.of_int 524275); (W32.of_int 524278);
(W32.of_int 524280); (W32.of_int 524282); (W32.of_int 524283);
(W32.of_int 524285); (W32.of_int 524285); (W32.of_int 524286);
(W32.of_int 524286)]).

abbrev haetae_keccak1600_rc =
(BArray192.of_list64
[(W64.of_int 1); (W64.of_int 32898); (W64.of_int (-9223372036854742902));
(W64.of_int (-9223372034707259392)); (W64.of_int 32907);
(W64.of_int 2147483649); (W64.of_int (-9223372034707259263));
(W64.of_int (-9223372036854743031)); (W64.of_int 138); (W64.of_int 136);
(W64.of_int 2147516425); (W64.of_int 2147483658); (W64.of_int 2147516555);
(W64.of_int (-9223372036854775669)); (W64.of_int (-9223372036854742903));
(W64.of_int (-9223372036854743037)); (W64.of_int (-9223372036854743038));
(W64.of_int (-9223372036854775680)); (W64.of_int 32778);
(W64.of_int (-9223372034707292150)); (W64.of_int (-9223372034707259263));
(W64.of_int (-9223372036854742912)); (W64.of_int 2147483649);
(W64.of_int (-9223372034707259384))]).

module type Syscall_t = {
  proc randombytes_32 (_:BArray32.t) : BArray32.t
}.

module Syscall : Syscall_t = {
  proc randombytes_32 (a:BArray32.t) : BArray32.t = {
    
    a <$ BArray32.darray;
    return a;
  }
}.

module M(SC:Syscall_t) = {
  proc _keccak_init_state (sp_0:BArray200.t) : BArray200.t = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 25))) {
      sp_0 <- (BArray200.set64 sp_0 (W64.to_uint i) (W64.of_int 0));
      i <- (i + (W64.of_int 1));
    }
    return sp_0;
  }
  proc _keccak_finalize (sp_0:BArray200.t, pos:W64.t, rate:W64.t, domain:W8.t) : 
  BArray200.t = {
    var lane:W64.t;
    var shift:W8.t;
    var t:W64.t;
    lane <- pos;
    lane <- (lane `>>` (W8.of_int 3));
    shift <- (truncateu8 pos);
    shift <- (shift `&` (W8.of_int 7));
    shift <- (shift `<<` (W8.of_int 3));
    t <- (zeroextu64 domain);
    t <- (t `<<` (shift `&` (W8.of_int 63)));
    sp_0 <-
    (BArray200.set64 sp_0 (W64.to_uint lane)
    ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
    lane <- rate;
    lane <- (lane `>>` (W8.of_int 3));
    lane <- (lane - (W64.of_int 1));
    t <- (W64.of_int 1);
    t <- (t `<<` (W8.of_int 63));
    sp_0 <-
    (BArray200.set64 sp_0 (W64.to_uint lane)
    ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
    return sp_0;
  }
  proc __keccakf1600_index (x:int, y:int) : int = {
    var r:int;
    r <- ((x %% 5) + (5 * (y %% 5)));
    return r;
  }
  proc __keccakf1600_rho_offset (i:int) : int = {
    var r:int;
    var x:int;
    var y:int;
    var t:int;
    var z:int;
    r <- 0;
    x <- 1;
    y <- 0;
    t <- 0;
    while ((t < 24)) {
      if ((i = (x + (5 * y)))) {
        r <- ((((t + 1) * (t + 2)) %/ 2) %% 64);
      } else {
        
      }
      z <- (((2 * x) + (3 * y)) %% 5);
      x <- y;
      y <- z;
      t <- (t + 1);
    }
    return r;
  }
  proc __keccakf1600_rho (x:int, y:int) : int = {
    var r:int;
    var i:int;
    i <@ __keccakf1600_index (x, y);
    r <@ __keccakf1600_rho_offset (i);
    return r;
  }
  proc __rol_u64 (x:W64.t, i:int) : W64.t = {
    var  _0:bool;
    var  _1:bool;
    if ((i <> 0)) {
      ( _0,  _1, x) <- (ROL_64 x (W8.of_int i));
    } else {
      
    }
    return x;
  }
  proc __andn_u64 (a:W64.t, b:W64.t) : W64.t = {
    var t:W64.t;
    t <- ((invw a) `&` b);
    return t;
  }
  proc __keccak_theta_sum (a:BArray200.t) : BArray40.t = {
    var c:BArray40.t;
    var x:int;
    var y:int;
    c <- witness;
    x <- 0;
    while ((x < 5)) {
      c <- (BArray40.set64 c x (BArray200.get64 a x));
      x <- (x + 1);
    }
    y <- 1;
    while ((y < 5)) {
      x <- 0;
      while ((x < 5)) {
        c <-
        (BArray40.set64 c x
        ((BArray40.get64 c x) `^` (BArray200.get64 a (x + (y * 5)))));
        x <- (x + 1);
      }
      y <- (y + 1);
    }
    return c;
  }
  proc __keccak_theta_rol (c:BArray40.t) : BArray40.t = {
    var aux:W64.t;
    var d:BArray40.t;
    var x:int;
    d <- witness;
    x <- 0;
    while ((x < 5)) {
      d <- (BArray40.set64 d x (BArray40.get64 c ((x + 1) %% 5)));
      aux <@ __rol_u64 ((BArray40.get64 d x), 1);
      d <- (BArray40.set64 d x aux);
      d <-
      (BArray40.set64 d x
      ((BArray40.get64 d x) `^` (BArray40.get64 c (((x - 1) + 5) %% 5))));
      x <- (x + 1);
    }
    return d;
  }
  proc __keccak_rol_sum (a:BArray200.t, d:BArray40.t, y:int) : BArray40.t = {
    var aux:W64.t;
    var b:BArray40.t;
    var x:int;
    var xp:int;
    var yp:int;
    var r:int;
    b <- witness;
    x <- 0;
    while ((x < 5)) {
      xp <- ((x + (3 * y)) %% 5);
      yp <- x;
      r <@ __keccakf1600_rho (xp, yp);
      b <- (BArray40.set64 b x (BArray200.get64 a (xp + (yp * 5))));
      b <-
      (BArray40.set64 b x ((BArray40.get64 b x) `^` (BArray40.get64 d xp)));
      aux <@ __rol_u64 ((BArray40.get64 b x), r);
      b <- (BArray40.set64 b x aux);
      x <- (x + 1);
    }
    return b;
  }
  proc __keccak_set_row (e:BArray200.t, b:BArray40.t, y:int) : BArray200.t = {
    var x:int;
    var x1:int;
    var x2:int;
    var t:W64.t;
    x <- 0;
    while ((x < 5)) {
      x1 <- ((x + 1) %% 5);
      x2 <- ((x + 2) %% 5);
      t <@ __andn_u64 ((BArray40.get64 b x1), (BArray40.get64 b x2));
      t <- (t `^` (BArray40.get64 b x));
      e <- (BArray200.set64 e (x + (y * 5)) t);
      x <- (x + 1);
    }
    return e;
  }
  proc _keccak_pround (e:BArray200.t, a:BArray200.t) : BArray200.t = {
    var c:BArray40.t;
    var d:BArray40.t;
    var y:int;
    var b:BArray40.t;
    b <- witness;
    c <- witness;
    d <- witness;
    c <@ __keccak_theta_sum (a);
    d <@ __keccak_theta_rol (c);
    y <- 0;
    while ((y < 5)) {
      b <@ __keccak_rol_sum (a, d, y);
      e <@ __keccak_set_row (e, b, y);
      y <- (y + 1);
    }
    return e;
  }
  proc __keccakf1600_statepermute (a:BArray200.t) : BArray200.t = {
    var se:BArray200.t;
    var e:BArray200.t;
    var rcp:BArray192.t;
    var c:int;
    var rc:W64.t;
    e <- witness;
    rcp <- witness;
    se <- witness;
    e <- se;
    c <- 0;
    while ((c < 12)) {
      e <@ _keccak_pround (e, a);
      (a, e) <- (swap_ e a);
      rcp <- haetae_keccak1600_rc;
      rc <- (BArray192.get64 rcp (2 * c));
      e <- (BArray200.set64 e 0 ((BArray200.get64 e 0) `^` rc));
      a <@ _keccak_pround (a, e);
      (a, e) <- (swap_ e a);
      rcp <- haetae_keccak1600_rc;
      rc <- (BArray192.get64 rcp ((2 * c) + 1));
      a <- (BArray200.set64 a 0 ((BArray200.get64 a 0) `^` rc));
      c <- (c + 1);
    }
    return a;
  }
  proc _keccakf1600 (sp_0:BArray200.t) : BArray200.t = {
    
    sp_0 <@ __keccakf1600_statepermute (sp_0);
    return sp_0;
  }
  proc __poly_sample_squeeze128 (outp:BArray1024.t, outoff:W64.t,
                                 sp_0:BArray200.t) : BArray1024.t *
                                                     BArray200.t = {
    var idx:W64.t;
    var ms:W64.t;
    var i:W64.t;
    var lane:W64.t;
    var t:W64.t;
    var j:W64.t;
    var b:W8.t;
    idx <- outoff;
    (* Erased call to spill *)
    sp_0 <@ _keccakf1600 (sp_0);
    (* Erased call to unspill *)
    ms <- (init_msf);
    outp <- (protect_ptr outp ms);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 168))) {
      lane <- i;
      lane <- (lane `>>` (W8.of_int 3));
      t <- (BArray200.get64 sp_0 (W64.to_uint lane));
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int 8))) {
        b <- (truncateu8 t);
        outp <- (BArray1024.set8 outp (W64.to_uint idx) b);
        t <- (t `>>` (W8.of_int 8));
        idx <- (idx + (W64.of_int 1));
        j <- (j + (W64.of_int 1));
      }
      i <- (i + (W64.of_int 8));
    }
    return (outp, sp_0);
  }
  proc __poly_uniform_consume (ap:BArray32768.t, base:W64.t, ctr:W64.t,
                               bp:BArray1024.t, buflen:W64.t) : BArray32768.t *
                                                                W64.t = {
    var pos:W64.t;
    var live:W64.t;
    var rem:W64.t;
    var byte:W8.t;
    var t:W32.t;
    var u:W32.t;
    var ms:W64.t;
    var b:bool;
    var idx:W64.t;
    pos <- (W64.of_int 0);
    live <- (W64.of_int 1);
    while ((live <> (W64.of_int 0))) {
      if (((W64.of_int 256) \ule ctr)) {
        live <- (W64.of_int 0);
      } else {
        rem <- buflen;
        rem <- (rem - pos);
        if ((rem \ult (W64.of_int 2))) {
          live <- (W64.of_int 0);
        } else {
          byte <- (BArray1024.get8 bp (W64.to_uint pos));
          t <- (zeroextu32 byte);
          pos <- (pos + (W64.of_int 1));
          byte <- (BArray1024.get8 bp (W64.to_uint pos));
          u <- (zeroextu32 byte);
          pos <- (pos + (W64.of_int 1));
          u <- (u `<<` (W8.of_int 8));
          t <- (t `|` u);
          (* Erased call to declassify *)
          ms <- (init_msf);
          t <- (protect_32 t ms);
          b <- (t \ult (W32.of_int 64513));
          if (b) {
            ms <- (update_msf b ms);
            idx <- base;
            idx <- (idx + ctr);
            ap <- (BArray32768.set32 ap (W64.to_uint idx) t);
            ctr <- (ctr + (W64.of_int 1));
          } else {
            ms <- (update_msf (! b) ms);
          }
        }
      }
    }
    return (ap, ctr);
  }
  proc __mul48 (a:W64.t, b:W64.t) : W64.t * W64.t = {
    var lo:W64.t;
    var hi:W64.t;
    var rax:W64.t;
    var rdx:W64.t;
    var top:W64.t;
    var mask:W64.t;
    rax <- a;
    (rdx, rax) <- (mulu_64 rax b);
    lo <- rax;
    hi <- rdx;
    hi <- (hi `<<` (W8.of_int 16));
    top <- lo;
    top <- (top `>>` (W8.of_int 48));
    hi <- (hi `^` top);
    mask <- (W64.of_int 281474976710655);
    lo <- (lo `&` mask);
    return (lo, hi);
  }
  proc __renormalize48 (x0:W64.t, x1:W64.t) : W64.t * W64.t = {
    var mask:W64.t;
    var carry:W64.t;
    mask <- (W64.of_int 281474976710655);
    carry <- x0;
    carry <- (carry `>>` (W8.of_int 48));
    x1 <- (x1 + carry);
    x0 <- (x0 `&` mask);
    return (x0, x1);
  }
  proc __bit_at_u8 (x:W32.t, shift:W8.t) : W8.t = {
    var r:W8.t;
    if ((shift = (W8.of_int 1))) {
      x <- (x `>>` (W8.of_int 1));
    } else {
      
    }
    if ((shift = (W8.of_int 2))) {
      x <- (x `>>` (W8.of_int 2));
    } else {
      
    }
    if ((shift = (W8.of_int 3))) {
      x <- (x `>>` (W8.of_int 3));
    } else {
      
    }
    if ((shift = (W8.of_int 4))) {
      x <- (x `>>` (W8.of_int 4));
    } else {
      
    }
    if ((shift = (W8.of_int 5))) {
      x <- (x `>>` (W8.of_int 5));
    } else {
      
    }
    if ((shift = (W8.of_int 6))) {
      x <- (x `>>` (W8.of_int 6));
    } else {
      
    }
    if ((shift = (W8.of_int 7))) {
      x <- (x `>>` (W8.of_int 7));
    } else {
      
    }
    x <- (x `&` (W32.of_int 1));
    r <- (truncateu8 x);
    return r;
  }
  proc __copy_cneg_regs (x0:W64.t, x1:W64.t, sign:W64.t) : W64.t * W64.t = {
    var y0:W64.t;
    var y1:W64.t;
    var lowmask:W64.t;
    var mask:W64.t;
    lowmask <- (W64.of_int 281474976710655);
    mask <- (W64.of_int 0);
    mask <- (mask - sign);
    y0 <- mask;
    y0 <- (y0 `&` lowmask);
    y0 <- (y0 `^` x0);
    y1 <- x1;
    y1 <- (y1 `^` mask);
    y0 <- (y0 + sign);
    (y0, y1) <@ __renormalize48 (y0, y1);
    return (y0, y1);
  }
  proc __sub_regs (x0:W64.t, x1:W64.t, y0:W64.t, y1:W64.t) : W64.t * W64.t = {
    var n0:W64.t;
    var n1:W64.t;
    (n0, n1) <@ __copy_cneg_regs (y0, y1, (W64.of_int 1));
    x0 <- (x0 + n0);
    x1 <- (x1 + n1);
    return (x0, x1);
  }
  proc __sub_from_threehalves_regs (x0:W64.t, x1:W64.t) : W64.t * W64.t = {
    var add:W64.t;
    (x0, x1) <@ __copy_cneg_regs (x0, x1, (W64.of_int 1));
    add <- (W64.of_int 3);
    add <- (add `<<` (W8.of_int 27));
    x1 <- (x1 + add);
    (x0, x1) <@ __renormalize48 (x0, x1);
    return (x0, x1);
  }
  proc __fixpoint_mul_regs (x0:W64.t, x1:W64.t, y0:W64.t, y1:W64.t) : 
  W64.t * W64.t = {
    var r0:W64.t;
    var r1:W64.t;
    var mask:W64.t;
    var lo:W64.t;
    var hi:W64.t;
    var tmp:W64.t;
    mask <- (W64.of_int 281474976710655);
    (lo, hi) <@ __mul48 (x0, y0);
    tmp <- lo;
    tmp <- (tmp `>>` (W8.of_int 47));
    tmp <- (tmp + (W64.of_int 1));
    tmp <- (tmp `>>` (W8.of_int 1));
    r0 <- hi;
    r0 <- (r0 + tmp);
    (lo, hi) <@ __mul48 (x0, y1);
    r0 <- (r0 + lo);
    r1 <- hi;
    (lo, hi) <@ __mul48 (x1, y0);
    r0 <- (r0 + lo);
    r1 <- (r1 + hi);
    tmp <- (W64.of_int 1);
    tmp <- (tmp `<<` (W8.of_int 27));
    r0 <- (r0 + tmp);
    r0 <- (r0 `>>` (W8.of_int 28));
    tmp <- r1;
    tmp <- (tmp `<<` (W8.of_int 20));
    tmp <- (tmp `&` mask);
    r0 <- (r0 + tmp);
    r1 <- (r1 `>>` (W8.of_int 28));
    tmp <- x1;
    (hi, tmp) <- (mulu_64 tmp y1);
    lo <- tmp;
    tmp <- lo;
    tmp <- (tmp `<<` (W8.of_int 20));
    tmp <- (tmp `&` mask);
    r0 <- (r0 + tmp);
    lo <- (lo `>>` (W8.of_int 28));
    hi <- (hi `<<` (W8.of_int 36));
    lo <- (lo + hi);
    r1 <- (r1 + lo);
    tmp <- r0;
    tmp <- (tmp `>>` (W8.of_int 48));
    r1 <- (r1 + tmp);
    r0 <- (r0 `&` mask);
    return (r0, r1);
  }
  proc __fixpoint_square_regs (x0:W64.t, x1:W64.t) : W64.t * W64.t = {
    var r0:W64.t;
    var r1:W64.t;
    var mask:W64.t;
    var lo:W64.t;
    var hi:W64.t;
    var tmp:W64.t;
    mask <- (W64.of_int 281474976710655);
    (lo, hi) <@ __mul48 (x0, x0);
    r0 <- lo;
    r0 <- (r0 `>>` (W8.of_int 48));
    r0 <- (r0 + hi);
    (lo, hi) <@ __mul48 (x0, x1);
    lo <- (lo `<<` (W8.of_int 1));
    r0 <- (r0 + lo);
    r1 <- hi;
    r1 <- (r1 `<<` (W8.of_int 1));
    r0 <- (r0 `>>` (W8.of_int 28));
    tmp <- r1;
    tmp <- (tmp `<<` (W8.of_int 20));
    tmp <- (tmp `&` mask);
    r0 <- (r0 + tmp);
    r1 <- (r1 `>>` (W8.of_int 28));
    tmp <- x1;
    (hi, tmp) <- (mulu_64 tmp x1);
    lo <- tmp;
    tmp <- lo;
    tmp <- (tmp `<<` (W8.of_int 20));
    tmp <- (tmp `&` mask);
    r0 <- (r0 + tmp);
    lo <- (lo `>>` (W8.of_int 28));
    hi <- (hi `<<` (W8.of_int 36));
    lo <- (lo + hi);
    r1 <- (r1 + lo);
    tmp <- r0;
    tmp <- (tmp `>>` (W8.of_int 48));
    r1 <- (r1 + tmp);
    r0 <- (r0 `&` mask);
    return (r0, r1);
  }
  proc __fixpoint_unsigned_signed_mul_regs (xy0:W64.t, xy1:W64.t, y0:W64.t,
                                            y1:W64.t) : W64.t * W64.t = {
    var z0:W64.t;
    var z1:W64.t;
    var sign:W64.t;
    var x0:W64.t;
    var x1:W64.t;
    sign <- y1;
    sign <- (sign `>>` (W8.of_int 63));
    sign <- (sign `&` (W64.of_int 1));
    (x0, x1) <@ __copy_cneg_regs (y0, y1, sign);
    (z0, z1) <@ __fixpoint_mul_regs (x0, x1, xy0, xy1);
    (z0, z1) <@ __copy_cneg_regs (z0, z1, sign);
    return (z0, z1);
  }
  proc _fixpoint_square (rp:BArray16.t, xp:BArray16.t) : BArray16.t = {
    var x0:W64.t;
    var x1:W64.t;
    var r0:W64.t;
    var r1:W64.t;
    x0 <- (BArray16.get64 xp 0);
    x1 <- (BArray16.get64 xp 1);
    (r0, r1) <@ __fixpoint_square_regs (x0, x1);
    rp <- (BArray16.set64 rp 0 r0);
    rp <- (BArray16.set64 rp 1 r1);
    return rp;
  }
  proc __fixpoint_mul_rnd13_regs (x:W64.t, y0:W64.t, y1:W64.t, sign:W64.t) : 
  W32.t = {
    var ret:W32.t;
    var x1:W64.t;
    var x0:W64.t;
    var r0:W64.t;
    var r1:W64.t;
    var res_0:W64.t;
    var mask:W64.t;
    x1 <- x;
    x1 <- (x1 `>>` (W8.of_int 32));
    x0 <- x;
    x0 <- (x0 `&` (W64.of_int 4294967295));
    x0 <- (x0 `<<` (W8.of_int 16));
    (r0, r1) <@ __fixpoint_mul_regs (x0, x1, y0, y1);
    res_0 <- r1;
    res_0 <- (res_0 + (W64.of_int 16384));
    res_0 <- (res_0 `>>` (W8.of_int 15));
    mask <- (W64.of_int 0);
    mask <- (mask - sign);
    res_0 <- (res_0 `^` mask);
    res_0 <- (res_0 + sign);
    ret <- (truncateu32 res_0);
    return ret;
  }
  proc __fixpoint_mul_high_regs (x0:W64.t, x1:W64.t, y:W64.t) : W64.t * W64.t = {
    var r0:W64.t;
    var r1:W64.t;
    var mask:W64.t;
    var tmp0:W64.t;
    var tmp1:W64.t;
    var add:W64.t;
    var t:W64.t;
    mask <- (W64.of_int 281474976710655);
    (r0, r1) <@ __mul48 (x0, y);
    (tmp0, tmp1) <@ __mul48 (x1, y);
    r1 <- (r1 + tmp0);
    add <- (W64.of_int 1);
    add <- (add `<<` (W8.of_int 27));
    r0 <- (r0 + add);
    r0 <- (r0 `>>` (W8.of_int 28));
    t <- r1;
    t <- (t `<<` (W8.of_int 20));
    t <- (t `&` mask);
    r0 <- (r0 + t);
    r1 <- (r1 `>>` (W8.of_int 28));
    tmp1 <- (tmp1 `<<` (W8.of_int 20));
    r1 <- (r1 + tmp1);
    (r0, r1) <@ __renormalize48 (r0, r1);
    return (r0, r1);
  }
  proc _fixpoint_mul_rnd13 (x:W64.t, yp:BArray16.t, sign:W8.t) : W32.t = {
    var ret:W32.t;
    var y0:W64.t;
    var y1:W64.t;
    var s:W64.t;
    y0 <- (BArray16.get64 yp 0);
    y1 <- (BArray16.get64 yp 1);
    s <- (zeroextu64 sign);
    ret <@ __fixpoint_mul_rnd13_regs (x, y0, y1, s);
    return ret;
  }
  proc _fixpoint_mul_high (rp:BArray16.t, xp:BArray16.t, y:W64.t) : BArray16.t = {
    var x0:W64.t;
    var x1:W64.t;
    var r0:W64.t;
    var r1:W64.t;
    x0 <- (BArray16.get64 xp 0);
    x1 <- (BArray16.get64 xp 1);
    (r0, r1) <@ __fixpoint_mul_high_regs (x0, x1, y);
    rp <- (BArray16.set64 rp 0 r0);
    rp <- (BArray16.set64 rp 1 r1);
    return rp;
  }
  proc _fixpoint_half_round (xp:BArray16.t) : BArray16.t = {
    var x0:W64.t;
    var x1:W64.t;
    var t:W64.t;
    x0 <- (BArray16.get64 xp 0);
    x1 <- (BArray16.get64 xp 1);
    x0 <- (x0 + (W64.of_int 1));
    x0 <- (x0 `>>` (W8.of_int 1));
    t <- x1;
    t <- (t `&` (W64.of_int 1));
    t <- (t `<<` (W8.of_int 47));
    x0 <- (x0 + t);
    x1 <- (x1 `>>` (W8.of_int 1));
    (x0, x1) <@ __renormalize48 (x0, x1);
    xp <- (BArray16.set64 xp 0 x0);
    xp <- (BArray16.set64 xp 1 x1);
    return xp;
  }
  proc _fixpoint_newton_invsqrt (rp:BArray16.t, xhalfp:BArray16.t,
                                 start_cubep:BArray16.t,
                                 start_threep:BArray16.t) : BArray16.t = {
    var x0:W64.t;
    var x1:W64.t;
    var sc0:W64.t;
    var sc1:W64.t;
    var st0:W64.t;
    var st1:W64.t;
    var tmp0:W64.t;
    var tmp1:W64.t;
    var inv0:W64.t;
    var inv1:W64.t;
    var i:W64.t;
    var tmp20:W64.t;
    var tmp21:W64.t;
    x0 <- (BArray16.get64 xhalfp 0);
    x1 <- (BArray16.get64 xhalfp 1);
    sc0 <- (BArray16.get64 start_cubep 0);
    sc1 <- (BArray16.get64 start_cubep 1);
    st0 <- (BArray16.get64 start_threep 0);
    st1 <- (BArray16.get64 start_threep 1);
    (tmp0, tmp1) <@ __fixpoint_mul_regs (x0, x1, sc0, sc1);
    (inv0, inv1) <@ __sub_regs (st0, st1, tmp0, tmp1);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 6))) {
      (tmp0, tmp1) <@ __fixpoint_square_regs (inv0, inv1);
      (tmp20, tmp21) <@ __fixpoint_mul_regs (x0, x1, tmp0, tmp1);
      (tmp20, tmp21) <@ __sub_from_threehalves_regs (tmp20, tmp21);
      (inv0, inv1) <@ __fixpoint_unsigned_signed_mul_regs (inv0, inv1, 
      tmp20, tmp21);
      i <- (i + (W64.of_int 1));
    }
    rp <- (BArray16.set64 rp 0 inv0);
    rp <- (BArray16.set64 rp 1 inv1);
    return rp;
  }
  proc _polyfixveclk_scale_samples (y1p:BArray8192.t, y2p:BArray8192.t,
                                    samplesp:BArray32768.t,
                                    signsp:BArray512.t, scalep:BArray16.t,
                                    counts:W64.t) : BArray8192.t *
                                                    BArray8192.t = {
    var lcount:W64.t;
    var total:W64.t;
    var ms:W64.t;
    var i:W64.t;
    var byte_idx:W64.t;
    var sign32:W32.t;
    var shift:W8.t;
    var sign8:W8.t;
    var sample:W64.t;
    var r:W32.t;
    var j:W64.t;
    lcount <- counts;
    lcount <- (lcount `&` (W64.of_int 4294967295));
    total <- counts;
    total <- (total `>>` (W8.of_int 32));
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    y1p <- (protect_ptr y1p ms);
    y2p <- (protect_ptr y2p ms);
    samplesp <- (protect_ptr samplesp ms);
    signsp <- (protect_ptr signsp ms);
    scalep <- (protect_ptr scalep ms);
    lcount <- (protect_64 lcount ms);
    total <- (protect_64 total ms);
    i <- (W64.of_int 0);
    while ((i \ult lcount)) {
      byte_idx <- i;
      byte_idx <- (byte_idx `>>` (W8.of_int 3));
      sign32 <- (zeroextu32 (BArray512.get8 signsp (W64.to_uint byte_idx)));
      shift <- (truncateu8 i);
      shift <- (shift `&` (W8.of_int 7));
      sign8 <@ __bit_at_u8 (sign32, shift);
      sample <- (BArray32768.get64 samplesp (W64.to_uint i));
      (* Erased call to spill *)
      r <@ _fixpoint_mul_rnd13 (sample, scalep, sign8);
      (* Erased call to unspill *)
      ms <- (init_msf);
      y1p <- (protect_ptr y1p ms);
      y2p <- (protect_ptr y2p ms);
      samplesp <- (protect_ptr samplesp ms);
      signsp <- (protect_ptr signsp ms);
      scalep <- (protect_ptr scalep ms);
      lcount <- (protect_64 lcount ms);
      total <- (protect_64 total ms);
      i <- (protect_64 i ms);
      y1p <- (BArray8192.set32 y1p (W64.to_uint i) r);
      i <- (i + (W64.of_int 1));
    }
    j <- (W64.of_int 0);
    while ((i \ult total)) {
      byte_idx <- i;
      byte_idx <- (byte_idx `>>` (W8.of_int 3));
      sign32 <- (zeroextu32 (BArray512.get8 signsp (W64.to_uint byte_idx)));
      shift <- (truncateu8 i);
      shift <- (shift `&` (W8.of_int 7));
      sign8 <@ __bit_at_u8 (sign32, shift);
      sample <- (BArray32768.get64 samplesp (W64.to_uint i));
      (* Erased call to spill *)
      r <@ _fixpoint_mul_rnd13 (sample, scalep, sign8);
      (* Erased call to unspill *)
      ms <- (init_msf);
      y1p <- (protect_ptr y1p ms);
      y2p <- (protect_ptr y2p ms);
      samplesp <- (protect_ptr samplesp ms);
      signsp <- (protect_ptr signsp ms);
      scalep <- (protect_ptr scalep ms);
      total <- (protect_64 total ms);
      i <- (protect_64 i ms);
      j <- (protect_64 j ms);
      y2p <- (BArray8192.set32 y2p (W64.to_uint j) r);
      i <- (i + (W64.of_int 1));
      j <- (j + (W64.of_int 1));
    }
    return (y1p, y2p);
  }
  proc _sample_gauss83 (rand_lo:W64.t, rand_hi:W32.t) : W64.t = {
    var r:W64.t;
    var hip:BArray304.t;
    var lop:BArray1328.t;
    var rndhi:W64.t;
    var i:W64.t;
    var c:W32.t;
    var hi:W64.t;
    var lo:W64.t;
    var borrow:bool;
    var  _0:bool;
    var  _1:bool;
    hip <- witness;
    lop <- witness;
    hip <- jcdt83_hi;
    lop <- jcdt83_lo;
    rndhi <- (zeroextu64 rand_hi);
    i <- (W64.of_int 0);
    r <- (W64.of_int 0);
    while ((i \ult (W64.of_int 76))) {
      c <- (BArray304.get32 hip (W64.to_uint i));
      hi <- (zeroextu64 c);
      lo <- (BArray1328.get64 lop (W64.to_uint i));
      (borrow, lo) <- (sbb_64 lo rand_lo false);
      ( _0, hi) <- (sbb_64 hi rndhi borrow);
      hi <- (hi `>>` (W8.of_int 63));
      r <- (r + hi);
      i <- (i + (W64.of_int 1));
    }
    while ((i \ult (W64.of_int 166))) {
      hi <- (W64.of_int 524287);
      lo <- (BArray1328.get64 lop (W64.to_uint i));
      (borrow, lo) <- (sbb_64 lo rand_lo false);
      ( _1, hi) <- (sbb_64 hi rndhi borrow);
      hi <- (hi `>>` (W8.of_int 63));
      r <- (r + hi);
      i <- (i + (W64.of_int 1));
    }
    return r;
  }
  proc __smulh48 (a:W64.t, b:W64.t) : W64.t = {
    var r:W64.t;
    var rax:W64.t;
    var rdx:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var tmp:W64.t;
    var rem:W64.t;
    rax <- a;
    (rdx, rax) <- (mulu_64 rax b);
    hi <- rdx;
    lo <- rax;
    tmp <- a;
    tmp <- (tmp `|>>` (W8.of_int 63));
    tmp <- (tmp `&` b);
    hi <- (hi - tmp);
    r <- hi;
    r <- (r `<<` (W8.of_int 16));
    tmp <- lo;
    tmp <- (tmp `>>` (W8.of_int 48));
    r <- (r `|` tmp);
    rem <- lo;
    rem <- (rem `&` (W64.of_int 281474976710655));
    tmp <- (W64.of_int 0);
    tmp <- (tmp - rem);
    rem <- (rem `|` tmp);
    rem <- (rem `>>` (W8.of_int 63));
    r <- (r + rem);
    return r;
  }
  proc _approx_exp (x:W64.t) : W64.t = {
    var result:W64.t;
    result <- (W64.of_int 55868746);
    result <@ __smulh48 (result, x);
    result <- (result - (W64.of_int 743564434));
    result <@ __smulh48 (result, x);
    result <- (result + (W64.of_int 6953427278));
    result <@ __smulh48 (result, x);
    result <- (result - (W64.of_int 55833338892));
    result <@ __smulh48 (result, x);
    result <- (result + (W64.of_int 390932311155));
    result <@ __smulh48 (result, x);
    result <- (result - (W64.of_int 2345623661771));
    result <@ __smulh48 (result, x);
    result <- (result + (W64.of_int 11728123872951));
    result <@ __smulh48 (result, x);
    result <- (result - (W64.of_int 46912496106200));
    result <@ __smulh48 (result, x);
    result <- (result + (W64.of_int 140737488354861));
    result <@ __smulh48 (result, x);
    result <- (result - (W64.of_int 281474976710650));
    result <@ __smulh48 (result, x);
    result <- (result + (W64.of_int 281474976710657));
    return result;
  }
  proc __sample_gauss_sigma76_regs (randp:BArray26.t) : W64.t * W64.t *
                                                        W64.t * W64.t = {
    var rounded:W64.t;
    var sqr0:W64.t;
    var sqr1:W64.t;
    var accepted:W64.t;
    var byte:W8.t;
    var rand_gauss83_lo:W64.t;
    var t:W64.t;
    var u:W64.t;
    var rand_gauss83_hi:W32.t;
    var x:W64.t;
    var rand_rej:W64.t;
    var y0:W64.t;
    var y1:W64.t;
    var y:BArray16.t;
    var yp:BArray16.t;
    var sqrbuf:BArray16.t;
    var sqrp:BArray16.t;
    var exp_in:W64.t;
    var ms:W64.t;
    var exp:W64.t;
    sqrbuf <- witness;
    sqrp <- witness;
    y <- witness;
    yp <- witness;
    byte <- (BArray26.get8 randp 0);
    rand_gauss83_lo <- (zeroextu64 byte);
    byte <- (BArray26.get8 randp 1);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 8));
    rand_gauss83_lo <- (rand_gauss83_lo `|` t);
    byte <- (BArray26.get8 randp 2);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 16));
    rand_gauss83_lo <- (rand_gauss83_lo `|` t);
    byte <- (BArray26.get8 randp 3);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 24));
    rand_gauss83_lo <- (rand_gauss83_lo `|` t);
    byte <- (BArray26.get8 randp 4);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 32));
    rand_gauss83_lo <- (rand_gauss83_lo `|` t);
    byte <- (BArray26.get8 randp 5);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 40));
    rand_gauss83_lo <- (rand_gauss83_lo `|` t);
    byte <- (BArray26.get8 randp 6);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 48));
    rand_gauss83_lo <- (rand_gauss83_lo `|` t);
    byte <- (BArray26.get8 randp 7);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 56));
    rand_gauss83_lo <- (rand_gauss83_lo `|` t);
    byte <- (BArray26.get8 randp 8);
    u <- (zeroextu64 byte);
    byte <- (BArray26.get8 randp 9);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 8));
    u <- (u `|` t);
    byte <- (BArray26.get8 randp 10);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 16));
    u <- (u `|` t);
    u <- (u `&` (W64.of_int 524287));
    rand_gauss83_hi <- (truncateu32 u);
    x <@ _sample_gauss83 (rand_gauss83_lo, rand_gauss83_hi);
    byte <- (BArray26.get8 randp 11);
    rand_rej <- (zeroextu64 byte);
    byte <- (BArray26.get8 randp 12);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 8));
    rand_rej <- (rand_rej `|` t);
    byte <- (BArray26.get8 randp 13);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 16));
    rand_rej <- (rand_rej `|` t);
    byte <- (BArray26.get8 randp 14);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 24));
    rand_rej <- (rand_rej `|` t);
    byte <- (BArray26.get8 randp 15);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 32));
    rand_rej <- (rand_rej `|` t);
    byte <- (BArray26.get8 randp 16);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 40));
    rand_rej <- (rand_rej `|` t);
    byte <- (BArray26.get8 randp 17);
    y0 <- (zeroextu64 byte);
    byte <- (BArray26.get8 randp 18);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 8));
    y0 <- (y0 `|` t);
    byte <- (BArray26.get8 randp 19);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 16));
    y0 <- (y0 `|` t);
    byte <- (BArray26.get8 randp 20);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 24));
    y0 <- (y0 `|` t);
    byte <- (BArray26.get8 randp 21);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 32));
    y0 <- (y0 `|` t);
    byte <- (BArray26.get8 randp 22);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 40));
    y0 <- (y0 `|` t);
    byte <- (BArray26.get8 randp 23);
    y1 <- (zeroextu64 byte);
    byte <- (BArray26.get8 randp 24);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 8));
    y1 <- (y1 `|` t);
    byte <- (BArray26.get8 randp 25);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 16));
    y1 <- (y1 `|` t);
    t <- x;
    t <- (t `<<` (W8.of_int 24));
    y1 <- (y1 `|` t);
    rounded <- y0;
    rounded <- (rounded `>>` (W8.of_int 15));
    rounded <- (rounded + (W64.of_int 1));
    rounded <- (rounded `>>` (W8.of_int 1));
    t <- y1;
    t <- (t `<<` (W8.of_int 32));
    rounded <- (rounded + t);
    y <- (BArray16.set64 y 0 y0);
    y <- (BArray16.set64 y 1 y1);
    yp <- y;
    sqrp <- sqrbuf;
    sqrp <@ _fixpoint_square (sqrp, yp);
    sqr0 <- (BArray16.get64 sqrp 0);
    sqr1 <- (BArray16.get64 sqrp 1);
    exp_in <- sqr1;
    t <- x;
    t <- (t * x);
    t <- (t `<<` (W8.of_int 20));
    exp_in <- (exp_in - t);
    exp_in <- (exp_in `<<` (W8.of_int 20));
    t <- sqr0;
    t <- (t `>>` (W8.of_int 28));
    exp_in <- (exp_in `|` t);
    exp_in <- (exp_in + (W64.of_int 1));
    exp_in <- (exp_in `>>` (W8.of_int 1));
    (* Erased call to declassify *)
    ms <- (init_msf);
    exp_in <- (protect_64 exp_in ms);
    exp <@ _approx_exp (exp_in);
    accepted <- rand_rej;
    t <- rand_rej;
    t <- (t `&` (W64.of_int 1));
    accepted <- (accepted `^` t);
    accepted <- (accepted - exp);
    accepted <- (accepted `|>>` (W8.of_int 63));
    t <- (W64.of_int 0);
    t <- (t - rounded);
    u <- rounded;
    u <- (u `|` t);
    u <- (u `>>` (W8.of_int 63));
    u <- (u `|` rand_rej);
    accepted <- (accepted `&` u);
    accepted <- (accepted `&` (W64.of_int 1));
    return (rounded, sqr0, sqr1, accepted);
  }
  proc _sample_gauss_N_carry (bufp:BArray8192.t, bytecnt:W64.t,
                              signbytes:W64.t, firstflag:W64.t, off:W64.t) : 
  BArray8192.t = {
    var src:W64.t;
    var i:W64.t;
    var idx:W64.t;
    var b:W8.t;
    src <- bytecnt;
    if ((firstflag <> (W64.of_int 0))) {
      src <- (src + signbytes);
    } else {
      
    }
    src <- (src - off);
    i <- (W64.of_int 0);
    while ((i \ult off)) {
      idx <- src;
      idx <- (idx + i);
      b <- (BArray8192.get8 bufp (W64.to_uint idx));
      bufp <- (BArray8192.set8 bufp (W64.to_uint i) b);
      i <- (i + (W64.of_int 1));
    }
    return bufp;
  }
  proc __sample_full_squeeze256 (outp:BArray8192.t, outoff:W64.t,
                                 sp_0:BArray200.t) : BArray8192.t *
                                                     BArray200.t = {
    var idx:W64.t;
    var ms:W64.t;
    var i:W64.t;
    var lane:W64.t;
    var t:W64.t;
    var j:W64.t;
    var b:W8.t;
    idx <- outoff;
    (* Erased call to spill *)
    sp_0 <@ _keccakf1600 (sp_0);
    (* Erased call to unspill *)
    ms <- (init_msf);
    outp <- (protect_ptr outp ms);
    sp_0 <- (protect_ptr sp_0 ms);
    idx <- (protect_64 idx ms);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 136))) {
      lane <- i;
      lane <- (lane `>>` (W8.of_int 3));
      t <- (BArray200.get64 sp_0 (W64.to_uint lane));
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int 8))) {
        b <- (truncateu8 t);
        outp <- (BArray8192.set8 outp (W64.to_uint idx) b);
        t <- (t `>>` (W8.of_int 8));
        idx <- (idx + (W64.of_int 1));
        j <- (j + (W64.of_int 1));
      }
      i <- (i + (W64.of_int 8));
    }
    return (outp, sp_0);
  }
  proc __sample_gauss_at (rp:BArray32768.t, sqsump:BArray16.t,
                          coefcntp:BArray8.t, bufp:BArray8192.t,
                          counts:W64.t, dont_write_last:W64.t, bufoff:W64.t,
                          outoff:W64.t) : BArray32768.t * BArray16.t *
                                          BArray8.t = {
    var srp:BArray32768.t;
    var ssqsump:BArray16.t;
    var scoefcntp:BArray8.t;
    var sbufp:BArray8192.t;
    var sdont:W64.t;
    var sbufoff:W64.t;
    var soutoff:W64.t;
    var len:W64.t;
    var bytecnt:W64.t;
    var slen:W64.t;
    var sbytecnt:W64.t;
    var spos:W64.t;
    var scoefcnt:W64.t;
    var randbuf:BArray26.t;
    var randp:BArray26.t;
    var pos:W64.t;
    var base:W64.t;
    var bufp_tmp:BArray8192.t;
    var k:int;
    var byte:W8.t;
    var coefcnt:W64.t;
    var sample:W64.t;
    var sqr0:W64.t;
    var sqr1:W64.t;
    var accepted:W64.t;
    var ms:W64.t;
    var last_0:W64.t;
    var dont:W64.t;
    var rp_tmp:BArray32768.t;
    var outidx:W64.t;
    var accepted64:W64.t;
    var mask:W64.t;
    var sqsum_tmp:BArray16.t;
    var s0:W64.t;
    var s1:W64.t;
    var carry:W64.t;
    var coefcntp_tmp:BArray8.t;
    bufp_tmp <- witness;
    coefcntp_tmp <- witness;
    randbuf <- witness;
    randp <- witness;
    rp_tmp <- witness;
    sbufp <- witness;
    scoefcntp <- witness;
    sqsum_tmp <- witness;
    srp <- witness;
    ssqsump <- witness;
    srp <- rp;
    ssqsump <- sqsump;
    scoefcntp <- coefcntp;
    sbufp <- bufp;
    sdont <- dont_write_last;
    sbufoff <- bufoff;
    soutoff <- outoff;
    len <- counts;
    len <- (len `&` (W64.of_int 4294967295));
    bytecnt <- counts;
    bytecnt <- (bytecnt `>>` (W8.of_int 32));
    slen <- len;
    sbytecnt <- bytecnt;
    spos <- (W64.of_int 0);
    scoefcnt <- (W64.of_int 0);
    randp <- randbuf;
    coefcnt <- scoefcnt;
    len <- slen;
    while ((coefcnt \ult len)) {
      bytecnt <- sbytecnt;
      if ((bytecnt \ult (W64.of_int 26))) {
        slen <- coefcnt;
      } else {
        pos <- spos;
        base <- sbufoff;
        base <- (base + pos);
        bufp_tmp <- sbufp;
        k <- 0;
        while ((k < 26)) {
          byte <-
          (BArray8192.get8 bufp_tmp (W64.to_uint (base + (W64.of_int k))));
          randp <- (BArray26.set8 randp k byte);
          k <- (k + 1);
        }
        (* Erased call to spill *)
        (sample, sqr0, sqr1, accepted) <@ __sample_gauss_sigma76_regs (
        randp);
        (* Erased call to unspill *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        ms <- (init_msf);
        coefcnt <- (protect_64 coefcnt ms);
        len <- (protect_64 len ms);
        pos <- (protect_64 pos ms);
        bytecnt <- (protect_64 bytecnt ms);
        accepted <- (protect_64 accepted ms);
        last_0 <- len;
        last_0 <- (last_0 - (W64.of_int 1));
        dont <- sdont;
        (* Erased call to declassify *)
        dont <- (protect_64 dont ms);
        rp_tmp <- srp;
        rp_tmp <- (protect_ptr rp_tmp ms);
        if ((dont <> (W64.of_int 0))) {
          if ((coefcnt = last_0)) {
            accepted64 <- accepted;
          } else {
            outidx <- soutoff;
            outidx <- (outidx + coefcnt);
            rp_tmp <- (BArray32768.set64 rp_tmp (W64.to_uint outidx) sample);
            srp <- rp_tmp;
            accepted64 <- accepted;
          }
        } else {
          outidx <- soutoff;
          outidx <- (outidx + coefcnt);
          rp_tmp <- (BArray32768.set64 rp_tmp (W64.to_uint outidx) sample);
          srp <- rp_tmp;
          accepted64 <- accepted;
        }
        coefcnt <- (coefcnt + accepted64);
        pos <- (pos + (W64.of_int 26));
        bytecnt <- (bytecnt - (W64.of_int 26));
        mask <- (W64.of_int 0);
        mask <- (mask - accepted64);
        sqr0 <- (sqr0 `&` mask);
        sqr1 <- (sqr1 `&` mask);
        sqsum_tmp <- ssqsump;
        ms <- (init_msf);
        sqsum_tmp <- (protect_ptr sqsum_tmp ms);
        s0 <- (BArray16.get64 sqsum_tmp 0);
        s1 <- (BArray16.get64 sqsum_tmp 1);
        s0 <- (s0 + sqr0);
        s1 <- (s1 + sqr1);
        sqsum_tmp <- (BArray16.set64 sqsum_tmp 0 s0);
        sqsum_tmp <- (BArray16.set64 sqsum_tmp 1 s1);
        ssqsump <- sqsum_tmp;
        scoefcnt <- coefcnt;
        spos <- pos;
        sbytecnt <- bytecnt;
      }
      coefcnt <- scoefcnt;
      len <- slen;
    }
    sqsum_tmp <- ssqsump;
    s0 <- (BArray16.get64 sqsum_tmp 0);
    s1 <- (BArray16.get64 sqsum_tmp 1);
    carry <- s0;
    carry <- (carry `>>` (W8.of_int 48));
    s1 <- (s1 + carry);
    mask <- (W64.of_int 281474976710655);
    s0 <- (s0 `&` mask);
    sqsum_tmp <- (BArray16.set64 sqsum_tmp 0 s0);
    sqsum_tmp <- (BArray16.set64 sqsum_tmp 1 s1);
    ssqsump <- sqsum_tmp;
    coefcnt <- scoefcnt;
    coefcntp_tmp <- scoefcntp;
    coefcntp_tmp <- (BArray8.set64 coefcntp_tmp 0 coefcnt);
    scoefcntp <- coefcntp_tmp;
    rp <- srp;
    sqsump <- ssqsump;
    coefcntp <- scoefcntp;
    return (rp, sqsump, coefcntp);
  }
  proc __sample_gauss_N_copy_signs_at (signsp:BArray512.t, bufp:BArray8192.t,
                                       signbytes:W64.t, signoff:W64.t) : 
  BArray512.t = {
    var i:W64.t;
    var b:W8.t;
    var idx:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult signbytes)) {
      b <- (BArray8192.get8 bufp (W64.to_uint i));
      idx <- signoff;
      idx <- (idx + i);
      signsp <- (BArray512.set8 signsp (W64.to_uint idx) b);
      i <- (i + (W64.of_int 1));
    }
    return signsp;
  }
  proc _polyfixveclk_sqnorm2_2048 (ap:BArray8192.t, acount:W64.t,
                                   bp:BArray8192.t, bcount:W64.t) : W64.t = {
    var total:W64.t;
    var i:W64.t;
    var a:W32.t;
    var coeff:W64.t;
    var prod:W64.t;
    total <- (W64.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult acount)) {
      a <- (BArray8192.get32 ap (W64.to_uint i));
      coeff <- (sigextu64 a);
      prod <- (coeff * coeff);
      total <- (total + prod);
      i <- (i + (W64.of_int 1));
    }
    i <- (W64.of_int 0);
    while ((i \ult bcount)) {
      a <- (BArray8192.get32 bp (W64.to_uint i));
      coeff <- (sigextu64 a);
      prod <- (coeff * coeff);
      total <- (total + prod);
      i <- (i + (W64.of_int 1));
    }
    return total;
  }
  proc __montgomery_reduce (a:W64.t) : W32.t = {
    var t32:W32.t;
    var t64:W64.t;
    t32 <- (truncateu32 a);
    t32 <- (t32 * (W32.of_int 940508161));
    t64 <- (sigextu64 t32);
    t64 <- (t64 * (W64.of_int 64513));
    a <- (a - t64);
    a <- (a `|>>` (W8.of_int 32));
    t32 <- (truncateu32 a);
    return t32;
  }
  proc __fqmul (a:W32.t, b:W32.t) : W32.t = {
    var r:W32.t;
    var ta:W64.t;
    var tb:W64.t;
    var t:W64.t;
    ta <- (sigextu64 a);
    tb <- (sigextu64 b);
    t <- (ta * tb);
    r <@ __montgomery_reduce (t);
    return r;
  }
  proc __freeze2q (a:W32.t) : W32.t = {
    var mask32:W32.t;
    var x:W64.t;
    var t:W64.t;
    var mask64:W64.t;
    x <- (sigextu64 a);
    t <- x;
    t <- (t * (W64.of_int 33287));
    t <- (t `|>>` (W8.of_int 32));
    t <- (t * (W64.of_int 129026));
    x <- (x - t);
    mask64 <- x;
    mask64 <- (mask64 `|>>` (W8.of_int 31));
    mask64 <- (mask64 `&` (W64.of_int 258052));
    x <- (x + mask64);
    mask64 <- x;
    mask64 <- (mask64 - (W64.of_int 129026));
    mask64 <- (mask64 `|>>` (W8.of_int 31));
    mask32 <- (truncateu32 mask64);
    mask32 <- (mask32 + (W32.of_int 1));
    mask32 <- (mask32 * (W32.of_int 129026));
    mask64 <- (zeroextu64 mask32);
    x <- (x - mask64);
    mask32 <- (truncateu32 x);
    return mask32;
  }
  proc _poly_ntt (rp:BArray1024.t) : BArray1024.t = {
    var zetasp:BArray1024.t;
    var zeta_0:W32.t;
    var s:W32.t;
    var coeff:W32.t;
    var t:W32.t;
    var zetasctr:int;
    var len:int;
    var start:int;
    var j:int;
    var cmp:int;
    var offset:int;
    zetasp <- witness;
    zetasp <- jzetas;
    zetasctr <- 0;
    len <- 128;
    while ((0 < len)) {
      start <- 0;
      while ((start < 256)) {
        zetasctr <- (zetasctr + 1);
        zeta_0 <- (BArray1024.get32 zetasp zetasctr);
        j <- start;
        cmp <- start;
        cmp <- (cmp + len);
        while ((j < cmp)) {
          s <- (BArray1024.get32 rp j);
          offset <- j;
          offset <- (offset + len);
          coeff <- (BArray1024.get32 rp offset);
          t <@ __fqmul (zeta_0, coeff);
          coeff <- s;
          coeff <- (coeff - t);
          rp <- (BArray1024.set32 rp offset coeff);
          s <- (s + t);
          rp <- (BArray1024.set32 rp j s);
          j <- (j + 1);
        }
        start <- j;
        start <- (start + len);
      }
      len <- (len `|>>` 1);
    }
    return rp;
  }
  proc _polyvec_ntt (xp:BArray8192.t, count:W64.t) : BArray8192.t = {
    var zetasp:BArray1024.t;
    var poly:W64.t;
    var base:W64.t;
    var zetasctr:W64.t;
    var len:W64.t;
    var start:W64.t;
    var zeta_0:W32.t;
    var j:W64.t;
    var cmp:W64.t;
    var idx:W64.t;
    var s:W32.t;
    var offset:W64.t;
    var idx2:W64.t;
    var coeff:W32.t;
    var t:W32.t;
    zetasp <- witness;
    zetasp <- jzetas;
    poly <- (W64.of_int 0);
    base <- (W64.of_int 0);
    while ((poly \ult count)) {
      zetasctr <- (W64.of_int 0);
      len <- (W64.of_int 128);
      while (((W64.of_int 0) \ult len)) {
        start <- (W64.of_int 0);
        while ((start \ult (W64.of_int 256))) {
          zetasctr <- (zetasctr + (W64.of_int 1));
          zeta_0 <- (BArray1024.get32 zetasp (W64.to_uint zetasctr));
          j <- start;
          cmp <- start;
          cmp <- (cmp + len);
          while ((j \ult cmp)) {
            idx <- base;
            idx <- (idx + j);
            s <- (BArray8192.get32 xp (W64.to_uint idx));
            offset <- j;
            offset <- (offset + len);
            idx2 <- base;
            idx2 <- (idx2 + offset);
            coeff <- (BArray8192.get32 xp (W64.to_uint idx2));
            t <@ __fqmul (zeta_0, coeff);
            coeff <- s;
            coeff <- (coeff - t);
            xp <- (BArray8192.set32 xp (W64.to_uint idx2) coeff);
            s <- (s + t);
            xp <- (BArray8192.set32 xp (W64.to_uint idx) s);
            j <- (j + (W64.of_int 1));
          }
          start <- j;
          start <- (start + len);
        }
        len <- (len `>>` (W8.of_int 1));
      }
      base <- (base + (W64.of_int 256));
      poly <- (poly + (W64.of_int 1));
    }
    return xp;
  }
  proc _polyvec_invntt (xp:BArray8192.t, count:W64.t) : BArray8192.t = {
    var zetasp:BArray1024.t;
    var poly:W64.t;
    var base:W64.t;
    var zetasctr:W64.t;
    var len:W64.t;
    var start:W64.t;
    var zeta_0:W32.t;
    var j:W64.t;
    var cmp:W64.t;
    var idx:W64.t;
    var t:W32.t;
    var offset:W64.t;
    var idx2:W64.t;
    var coeff:W32.t;
    var s:W32.t;
    zetasp <- witness;
    zetasp <- jzetas_inv;
    poly <- (W64.of_int 0);
    base <- (W64.of_int 0);
    while ((poly \ult count)) {
      zetasctr <- (W64.of_int 0);
      len <- (W64.of_int 1);
      while ((len \ult (W64.of_int 256))) {
        start <- (W64.of_int 0);
        while ((start \ult (W64.of_int 256))) {
          zeta_0 <- (BArray1024.get32 zetasp (W64.to_uint zetasctr));
          zetasctr <- (zetasctr + (W64.of_int 1));
          j <- start;
          cmp <- start;
          cmp <- (cmp + len);
          while ((j \ult cmp)) {
            idx <- base;
            idx <- (idx + j);
            t <- (BArray8192.get32 xp (W64.to_uint idx));
            offset <- j;
            offset <- (offset + len);
            idx2 <- base;
            idx2 <- (idx2 + offset);
            coeff <- (BArray8192.get32 xp (W64.to_uint idx2));
            s <- t;
            s <- (s + coeff);
            xp <- (BArray8192.set32 xp (W64.to_uint idx) s);
            t <- (t - coeff);
            t <@ __fqmul (zeta_0, t);
            xp <- (BArray8192.set32 xp (W64.to_uint idx2) t);
            j <- (j + (W64.of_int 1));
          }
          start <- j;
          start <- (start + len);
        }
        len <- (len `<<` (W8.of_int 1));
      }
      zeta_0 <- (BArray1024.get32 zetasp 255);
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int 256))) {
        idx <- base;
        idx <- (idx + j);
        coeff <- (BArray8192.get32 xp (W64.to_uint idx));
        t <@ __fqmul (zeta_0, coeff);
        xp <- (BArray8192.set32 xp (W64.to_uint idx) t);
        j <- (j + (W64.of_int 1));
      }
      base <- (base + (W64.of_int 256));
      poly <- (poly + (W64.of_int 1));
    }
    return xp;
  }
  proc _polyvec_poly_pointwise (rp:BArray8192.t, up:BArray8192.t,
                                vp:BArray1024.t, count:W64.t) : BArray8192.t = {
    var k:W64.t;
    var off:W64.t;
    var j:W64.t;
    var idx:W64.t;
    var a:W32.t;
    var b:W32.t;
    var t:W32.t;
    k <- (W64.of_int 0);
    off <- (W64.of_int 0);
    while ((k \ult count)) {
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int 256))) {
        idx <- off;
        idx <- (idx + j);
        a <- (BArray8192.get32 up (W64.to_uint idx));
        b <- (BArray1024.get32 vp (W64.to_uint j));
        t <@ __fqmul (a, b);
        rp <- (BArray8192.set32 rp (W64.to_uint idx) t);
        j <- (j + (W64.of_int 1));
      }
      off <- (off + (W64.of_int 256));
      k <- (k + (W64.of_int 1));
    }
    return rp;
  }
  proc _polyvec_freeze2q (vp:BArray8192.t, count:W64.t) : BArray8192.t = {
    var i:W64.t;
    var a:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult count)) {
      a <- (BArray8192.get32 vp (W64.to_uint i));
      a <@ __freeze2q (a);
      vp <- (BArray8192.set32 vp (W64.to_uint i) a);
      i <- (i + (W64.of_int 1));
    }
    return vp;
  }
  proc _polyvec_double (vp:BArray8192.t, count:W64.t) : BArray8192.t = {
    var i:W64.t;
    var a:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult count)) {
      a <- (BArray8192.get32 vp (W64.to_uint i));
      a <- (a `<<` (W8.of_int 1));
      vp <- (BArray8192.set32 vp (W64.to_uint i) a);
      i <- (i + (W64.of_int 1));
    }
    return vp;
  }
  proc _polymat_pointwise_acc (tp:BArray8192.t, mp:BArray32768.t,
                               vp:BArray8192.t, rows:W64.t, cols:W64.t) : 
  BArray8192.t = {
    var row:W64.t;
    var row_out:W64.t;
    var row_mat:W64.t;
    var j:W64.t;
    var oidx:W64.t;
    var col:W64.t;
    var col_off:W64.t;
    var midx:W64.t;
    var vidx:W64.t;
    var a:W32.t;
    var b:W32.t;
    var t:W32.t;
    var acc:W32.t;
    row <- (W64.of_int 0);
    row_out <- (W64.of_int 0);
    row_mat <- (W64.of_int 0);
    while ((row \ult rows)) {
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int 256))) {
        oidx <- row_out;
        oidx <- (oidx + j);
        tp <- (BArray8192.set32 tp (W64.to_uint oidx) (W32.of_int 0));
        j <- (j + (W64.of_int 1));
      }
      col <- (W64.of_int 0);
      col_off <- (W64.of_int 0);
      while ((col \ult cols)) {
        j <- (W64.of_int 0);
        while ((j \ult (W64.of_int 256))) {
          midx <- row_mat;
          midx <- (midx + col_off);
          midx <- (midx + j);
          vidx <- col_off;
          vidx <- (vidx + j);
          oidx <- row_out;
          oidx <- (oidx + j);
          a <- (BArray32768.get32 mp (W64.to_uint midx));
          b <- (BArray8192.get32 vp (W64.to_uint vidx));
          t <@ __fqmul (a, b);
          acc <- (BArray8192.get32 tp (W64.to_uint oidx));
          acc <- (acc + t);
          tp <- (BArray8192.set32 tp (W64.to_uint oidx) acc);
          j <- (j + (W64.of_int 1));
        }
        col_off <- (col_off + (W64.of_int 256));
        col <- (col + (W64.of_int 1));
      }
      row_mat <- (row_mat + col_off);
      row_out <- (row_out + (W64.of_int 256));
      row <- (row + (W64.of_int 1));
    }
    return tp;
  }
  proc _polymatkl_double (mp:BArray32768.t, rows:W64.t, cols:W64.t) : 
  BArray32768.t = {
    var row:W64.t;
    var row_off:W64.t;
    var col:W64.t;
    var col_off:W64.t;
    var j:W64.t;
    var idx:W64.t;
    var a:W32.t;
    row <- (W64.of_int 0);
    row_off <- (W64.of_int 0);
    while ((row \ult rows)) {
      col <- (W64.of_int 1);
      col_off <- (W64.of_int 256);
      while ((col \ult cols)) {
        j <- (W64.of_int 0);
        while ((j \ult (W64.of_int 256))) {
          idx <- row_off;
          idx <- (idx + col_off);
          idx <- (idx + j);
          a <- (BArray32768.get32 mp (W64.to_uint idx));
          a <- (a `<<` (W8.of_int 1));
          mp <- (BArray32768.set32 mp (W64.to_uint idx) a);
          j <- (j + (W64.of_int 1));
        }
        col_off <- (col_off + (W64.of_int 256));
        col <- (col + (W64.of_int 1));
      }
      row_off <- (row_off + col_off);
      row <- (row + (W64.of_int 1));
    }
    return mp;
  }
  proc _polymat_set_first_column (mp:BArray32768.t, vp:BArray8192.t,
                                  rows:W64.t, cols:W64.t) : BArray32768.t = {
    var stride:W64.t;
    var row:W64.t;
    var row_off:W64.t;
    var src_off:W64.t;
    var j:W64.t;
    var midx:W64.t;
    var vidx:W64.t;
    var a:W32.t;
    stride <- cols;
    stride <- (stride * (W64.of_int 256));
    row <- (W64.of_int 0);
    row_off <- (W64.of_int 0);
    src_off <- (W64.of_int 0);
    while ((row \ult rows)) {
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int 256))) {
        midx <- row_off;
        midx <- (midx + j);
        vidx <- src_off;
        vidx <- (vidx + j);
        a <- (BArray8192.get32 vp (W64.to_uint vidx));
        mp <- (BArray32768.set32 mp (W64.to_uint midx) a);
        j <- (j + (W64.of_int 1));
      }
      row_off <- (row_off + stride);
      src_off <- (src_off + (W64.of_int 256));
      row <- (row + (W64.of_int 1));
    }
    return mp;
  }
  proc _pack_poly_lsb (bp:BArray32.t, ap:BArray1024.t) : BArray32.t = {
    var out:W32.t;
    var j:int;
    var i:int;
    var a:W32.t;
    var bit:W32.t;
    i <- 0;
    while ((i < 32)) {
      out <- (W32.of_int 0);
      j <- 0;
      while ((j < 8)) {
        a <- (BArray1024.get32 ap ((8 * i) + j));
        bit <- a;
        bit <- (bit `&` (W32.of_int 1));
        bit <- (bit `<<` (W8.of_int j));
        out <- (out `|` bit);
        j <- (j + 1);
      }
      bp <- (BArray32.set8 bp i (truncateu8 out));
      i <- (i + 1);
    }
    return bp;
  }
  proc _pack_sig_prefix (sigp:BArray2948.t, cp:BArray1024.t,
                         lowp:BArray8192.t, lcount:W64.t, sigbytes:W64.t) : 
  BArray2948.t = {
    var i:W64.t;
    var out:W32.t;
    var idx:W64.t;
    var j:int;
    var bit:W32.t;
    var off:W64.t;
    var total:W64.t;
    var a:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult sigbytes)) {
      sigp <- (BArray2948.set8 sigp (W64.to_uint i) (W8.of_int 0));
      i <- (i + (W64.of_int 1));
    }
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      out <- (W32.of_int 0);
      j <- 0;
      while ((j < 8)) {
        idx <- ((W64.of_int 8) * i);
        idx <- (idx + (W64.of_int j));
        bit <- (BArray1024.get32 cp (W64.to_uint idx));
        bit <- (bit `&` (W32.of_int 1));
        bit <- (bit `<<` (W8.of_int j));
        out <- (out `|` bit);
        j <- (j + 1);
      }
      sigp <- (BArray2948.set8 sigp (W64.to_uint i) (truncateu8 out));
      i <- (i + (W64.of_int 1));
    }
    off <- (W64.of_int 32);
    total <- lcount;
    total <- (total * (W64.of_int 256));
    i <- (W64.of_int 0);
    while ((i \ult total)) {
      idx <- off;
      idx <- (idx + i);
      a <- (BArray8192.get32 lowp (W64.to_uint i));
      sigp <- (BArray2948.set8 sigp (W64.to_uint idx) (truncateu8 a));
      i <- (i + (W64.of_int 1));
    }
    return sigp;
  }
  proc __pack_sig_size_offsets_values (hbsize:W64.t, hsize:W64.t,
                                       base_hb:W64.t, base_h:W64.t,
                                       payload_limit:W64.t) : W64.t * W64.t = {
    var packed:W64.t;
    var bad:W64.t;
    var upper_hb:W64.t;
    var upper_h:W64.t;
    var total:W64.t;
    var off_hb:W64.t;
    var off_h:W64.t;
    bad <- (W64.of_int 0);
    if ((hsize = (W64.of_int 0))) {
      bad <- (W64.of_int 1);
    } else {
      
    }
    if ((hbsize = (W64.of_int 0))) {
      bad <- (W64.of_int 1);
    } else {
      
    }
    upper_hb <- base_hb;
    upper_hb <- (upper_hb + (W64.of_int 255));
    upper_h <- base_h;
    upper_h <- (upper_h + (W64.of_int 255));
    if ((hbsize \ult base_hb)) {
      bad <- (W64.of_int 1);
    } else {
      
    }
    if ((hsize \ult base_h)) {
      bad <- (W64.of_int 1);
    } else {
      
    }
    if ((upper_hb \ult hbsize)) {
      bad <- (W64.of_int 1);
    } else {
      
    }
    if ((upper_h \ult hsize)) {
      bad <- (W64.of_int 1);
    } else {
      
    }
    total <- hbsize;
    total <- (total + hsize);
    if ((payload_limit \ult total)) {
      bad <- (W64.of_int 1);
    } else {
      
    }
    packed <- (W64.of_int 0);
    if ((bad = (W64.of_int 0))) {
      off_hb <- hbsize;
      off_hb <- (off_hb - base_hb);
      off_h <- hsize;
      off_h <- (off_h - base_h);
      packed <- off_h;
      packed <- (packed `<<` (W8.of_int 8));
      packed <- (packed `|` off_hb);
    } else {
      
    }
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    return (packed, bad);
  }
  proc _unpack_vec_eta_from (vp:BArray8192.t, inp:BArray2752.t, in_off:W64.t,
                             count:W64.t) : BArray8192.t = {
    var poly:W64.t;
    var coeff_base:W64.t;
    var pos:W64.t;
    var i:W64.t;
    var base:W64.t;
    var b:W32.t;
    var t:W32.t;
    var r:W32.t;
    poly <- (W64.of_int 0);
    coeff_base <- (W64.of_int 0);
    pos <- in_off;
    while ((poly \ult count)) {
      i <- (W64.of_int 0);
      while ((i \ult (W64.of_int 64))) {
        base <- coeff_base;
        base <- (base + ((W64.of_int 4) * i));
        b <- (zeroextu32 (BArray2752.get8 inp (W64.to_uint pos)));
        t <- b;
        t <- (t `&` (W32.of_int 3));
        r <- (W32.of_int 1);
        r <- (r - t);
        vp <- (BArray8192.set32 vp (W64.to_uint (base + (W64.of_int 0))) r);
        t <- b;
        t <- (t `>>` (W8.of_int 2));
        t <- (t `&` (W32.of_int 3));
        r <- (W32.of_int 1);
        r <- (r - t);
        vp <- (BArray8192.set32 vp (W64.to_uint (base + (W64.of_int 1))) r);
        t <- b;
        t <- (t `>>` (W8.of_int 4));
        t <- (t `&` (W32.of_int 3));
        r <- (W32.of_int 1);
        r <- (r - t);
        vp <- (BArray8192.set32 vp (W64.to_uint (base + (W64.of_int 2))) r);
        t <- b;
        t <- (t `>>` (W8.of_int 6));
        t <- (t `&` (W32.of_int 3));
        r <- (W32.of_int 1);
        r <- (r - t);
        vp <- (BArray8192.set32 vp (W64.to_uint (base + (W64.of_int 3))) r);
        i <- (i + (W64.of_int 1));
        pos <- (pos + (W64.of_int 1));
      }
      coeff_base <- (coeff_base + (W64.of_int 256));
      poly <- (poly + (W64.of_int 1));
    }
    return vp;
  }
  proc _unpack_vec_eta_from_second (vp:BArray8192.t, inp:BArray2752.t,
                                    in_off:W64.t, count:W64.t) : BArray8192.t = {
    var poly:W64.t;
    var coeff_base:W64.t;
    var pos:W64.t;
    var i:W64.t;
    var base:W64.t;
    var b:W32.t;
    var t:W32.t;
    var r:W32.t;
    poly <- (W64.of_int 0);
    coeff_base <- (W64.of_int 0);
    pos <- in_off;
    while ((poly \ult count)) {
      i <- (W64.of_int 0);
      while ((i \ult (W64.of_int 64))) {
        base <- coeff_base;
        base <- (base + ((W64.of_int 4) * i));
        b <- (zeroextu32 (BArray2752.get8 inp (W64.to_uint pos)));
        t <- b;
        t <- (t `&` (W32.of_int 3));
        r <- (W32.of_int 1);
        r <- (r - t);
        vp <- (BArray8192.set32 vp (W64.to_uint (base + (W64.of_int 0))) r);
        t <- b;
        t <- (t `>>` (W8.of_int 2));
        t <- (t `&` (W32.of_int 3));
        r <- (W32.of_int 1);
        r <- (r - t);
        vp <- (BArray8192.set32 vp (W64.to_uint (base + (W64.of_int 1))) r);
        t <- b;
        t <- (t `>>` (W8.of_int 4));
        t <- (t `&` (W32.of_int 3));
        r <- (W32.of_int 1);
        r <- (r - t);
        vp <- (BArray8192.set32 vp (W64.to_uint (base + (W64.of_int 2))) r);
        t <- b;
        t <- (t `>>` (W8.of_int 6));
        t <- (t `&` (W32.of_int 3));
        r <- (W32.of_int 1);
        r <- (r - t);
        vp <- (BArray8192.set32 vp (W64.to_uint (base + (W64.of_int 3))) r);
        i <- (i + (W64.of_int 1));
        pos <- (pos + (W64.of_int 1));
      }
      coeff_base <- (coeff_base + (W64.of_int 256));
      poly <- (poly + (W64.of_int 1));
    }
    return vp;
  }
  proc _unpack_vec2_eta_from (vp:BArray8192.t, inp:BArray2752.t,
                              in_off:W64.t, count:W64.t) : BArray8192.t = {
    var poly:W64.t;
    var coeff_base:W64.t;
    var pos:W64.t;
    var i:W64.t;
    var base:W64.t;
    var b:W32.t;
    var t:W32.t;
    var r:W32.t;
    var next:W32.t;
    poly <- (W64.of_int 0);
    coeff_base <- (W64.of_int 0);
    pos <- in_off;
    while ((poly \ult count)) {
      i <- (W64.of_int 0);
      while ((i \ult (W64.of_int 32))) {
        base <- coeff_base;
        base <- (base + ((W64.of_int 8) * i));
        b <-
        (zeroextu32
        (BArray2752.get8 inp (W64.to_uint (pos + (W64.of_int 0)))));
        t <- b;
        t <- (t `&` (W32.of_int 7));
        r <- (W32.of_int (2 * 1));
        r <- (r - t);
        vp <- (BArray8192.set32 vp (W64.to_uint (base + (W64.of_int 0))) r);
        t <- b;
        t <- (t `>>` (W8.of_int 3));
        t <- (t `&` (W32.of_int 7));
        r <- (W32.of_int (2 * 1));
        r <- (r - t);
        vp <- (BArray8192.set32 vp (W64.to_uint (base + (W64.of_int 1))) r);
        t <- b;
        t <- (t `>>` (W8.of_int 6));
        next <-
        (zeroextu32
        (BArray2752.get8 inp (W64.to_uint (pos + (W64.of_int 1)))));
        b <- next;
        next <- (next `<<` (W8.of_int 2));
        t <- (t `|` next);
        t <- (t `&` (W32.of_int 7));
        r <- (W32.of_int (2 * 1));
        r <- (r - t);
        vp <- (BArray8192.set32 vp (W64.to_uint (base + (W64.of_int 2))) r);
        t <- b;
        t <- (t `>>` (W8.of_int 1));
        t <- (t `&` (W32.of_int 7));
        r <- (W32.of_int (2 * 1));
        r <- (r - t);
        vp <- (BArray8192.set32 vp (W64.to_uint (base + (W64.of_int 3))) r);
        t <- b;
        t <- (t `>>` (W8.of_int 4));
        t <- (t `&` (W32.of_int 7));
        r <- (W32.of_int (2 * 1));
        r <- (r - t);
        vp <- (BArray8192.set32 vp (W64.to_uint (base + (W64.of_int 4))) r);
        t <- b;
        t <- (t `>>` (W8.of_int 7));
        next <-
        (zeroextu32
        (BArray2752.get8 inp (W64.to_uint (pos + (W64.of_int 2)))));
        b <- next;
        next <- (next `<<` (W8.of_int 1));
        t <- (t `|` next);
        t <- (t `&` (W32.of_int 7));
        r <- (W32.of_int (2 * 1));
        r <- (r - t);
        vp <- (BArray8192.set32 vp (W64.to_uint (base + (W64.of_int 5))) r);
        t <- b;
        t <- (t `>>` (W8.of_int 2));
        t <- (t `&` (W32.of_int 7));
        r <- (W32.of_int (2 * 1));
        r <- (r - t);
        vp <- (BArray8192.set32 vp (W64.to_uint (base + (W64.of_int 6))) r);
        t <- b;
        t <- (t `>>` (W8.of_int 5));
        t <- (t `&` (W32.of_int 7));
        r <- (W32.of_int (2 * 1));
        r <- (r - t);
        vp <- (BArray8192.set32 vp (W64.to_uint (base + (W64.of_int 7))) r);
        i <- (i + (W64.of_int 1));
        pos <- (pos + (W64.of_int 3));
      }
      coeff_base <- (coeff_base + (W64.of_int 256));
      poly <- (poly + (W64.of_int 1));
    }
    return vp;
  }
  proc _unpack_sk_m23 (s0p:BArray8192.t, s1p:BArray8192.t, keyp:BArray32.t,
                       skp:BArray2752.t, vkbytes:W64.t, mcount:W64.t,
                       kcount:W64.t) : BArray8192.t * BArray8192.t *
                                       BArray32.t = {
    var off:W64.t;
    var step:W64.t;
    var i:W64.t;
    var idx:W64.t;
    off <- vkbytes;
    s0p <@ _unpack_vec_eta_from (s0p, skp, off, mcount);
    step <- mcount;
    step <- (step * (W64.of_int 64));
    off <- (off + step);
    s1p <@ _unpack_vec2_eta_from (s1p, skp, off, kcount);
    step <- kcount;
    step <- (step * (W64.of_int 96));
    off <- (off + step);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      idx <- off;
      idx <- (idx + i);
      keyp <-
      (BArray32.set8 keyp (W64.to_uint i)
      (BArray2752.get8 skp (W64.to_uint idx)));
      i <- (i + (W64.of_int 1));
    }
    return (s0p, s1p, keyp);
  }
  proc _unpack_sk_m5 (s0p:BArray8192.t, s1p:BArray8192.t, keyp:BArray32.t,
                      skp:BArray2752.t, vkbytes:W64.t, mcount:W64.t,
                      kcount:W64.t) : BArray8192.t * BArray8192.t *
                                      BArray32.t = {
    var off:W64.t;
    var step:W64.t;
    var i:W64.t;
    var idx:W64.t;
    off <- vkbytes;
    s0p <@ _unpack_vec_eta_from (s0p, skp, off, mcount);
    step <- mcount;
    step <- (step * (W64.of_int 64));
    off <- (off + step);
    s1p <@ _unpack_vec_eta_from_second (s1p, skp, off, kcount);
    step <- kcount;
    step <- (step * (W64.of_int 64));
    off <- (off + step);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      idx <- off;
      idx <- (idx + i);
      keyp <-
      (BArray32.set8 keyp (W64.to_uint i)
      (BArray2752.get8 skp (W64.to_uint idx)));
      i <- (i + (W64.of_int 1));
    }
    return (s0p, s1p, keyp);
  }
  proc _pack_vec_highbits_m23 (bp:BArray1152.t, ap:BArray8192.t, count:W64.t) : 
  BArray1152.t = {
    var poly:W64.t;
    var coeff_base:W64.t;
    var out_base:W64.t;
    var i:W64.t;
    var idx:W64.t;
    var a:W32.t;
    poly <- (W64.of_int 0);
    coeff_base <- (W64.of_int 0);
    out_base <- (W64.of_int 0);
    while ((poly \ult count)) {
      i <- (W64.of_int 0);
      while ((i \ult (W64.of_int 256))) {
        idx <- coeff_base;
        idx <- (idx + i);
        a <- (BArray8192.get32 ap (W64.to_uint idx));
        idx <- out_base;
        idx <- (idx + i);
        bp <- (BArray1152.set8 bp (W64.to_uint idx) (truncateu8 a));
        i <- (i + (W64.of_int 1));
      }
      coeff_base <- (coeff_base + (W64.of_int 256));
      out_base <- (out_base + (W64.of_int 288));
      poly <- (poly + (W64.of_int 1));
    }
    return bp;
  }
  proc _pack_vec_highbits_m5 (bp:BArray1152.t, ap:BArray8192.t, count:W64.t) : 
  BArray1152.t = {
    var poly:W64.t;
    var coeff_base:W64.t;
    var off:W64.t;
    var i:W64.t;
    var base:W64.t;
    var a:W32.t;
    var out:W32.t;
    var next:W32.t;
    var part:W32.t;
    poly <- (W64.of_int 0);
    coeff_base <- (W64.of_int 0);
    off <- (W64.of_int 0);
    while ((poly \ult count)) {
      i <- (W64.of_int 0);
      while ((i \ult (W64.of_int 32))) {
        base <- coeff_base;
        base <- (base + ((W64.of_int 8) * i));
        a <- (BArray8192.get32 ap (W64.to_uint (base + (W64.of_int 0))));
        bp <-
        (BArray1152.set8 bp (W64.to_uint (off + (W64.of_int 0)))
        (truncateu8 a));
        out <- a;
        out <- (out `>>` (W8.of_int 8));
        out <- (out `&` (W32.of_int 1));
        next <- (BArray8192.get32 ap (W64.to_uint (base + (W64.of_int 1))));
        part <- next;
        part <- (part `<<` (W8.of_int 1));
        part <- (part `&` (W32.of_int 255));
        out <- (out `|` part);
        bp <-
        (BArray1152.set8 bp (W64.to_uint (off + (W64.of_int 1)))
        (truncateu8 out));
        a <- next;
        out <- a;
        out <- (out `>>` (W8.of_int 7));
        out <- (out `&` (W32.of_int 3));
        next <- (BArray8192.get32 ap (W64.to_uint (base + (W64.of_int 2))));
        part <- next;
        part <- (part `<<` (W8.of_int 2));
        part <- (part `&` (W32.of_int 255));
        out <- (out `|` part);
        bp <-
        (BArray1152.set8 bp (W64.to_uint (off + (W64.of_int 2)))
        (truncateu8 out));
        a <- next;
        out <- a;
        out <- (out `>>` (W8.of_int 6));
        out <- (out `&` (W32.of_int 7));
        next <- (BArray8192.get32 ap (W64.to_uint (base + (W64.of_int 3))));
        part <- next;
        part <- (part `<<` (W8.of_int 3));
        part <- (part `&` (W32.of_int 255));
        out <- (out `|` part);
        bp <-
        (BArray1152.set8 bp (W64.to_uint (off + (W64.of_int 3)))
        (truncateu8 out));
        a <- next;
        out <- a;
        out <- (out `>>` (W8.of_int 5));
        out <- (out `&` (W32.of_int 15));
        next <- (BArray8192.get32 ap (W64.to_uint (base + (W64.of_int 4))));
        part <- next;
        part <- (part `<<` (W8.of_int 4));
        part <- (part `&` (W32.of_int 255));
        out <- (out `|` part);
        bp <-
        (BArray1152.set8 bp (W64.to_uint (off + (W64.of_int 4)))
        (truncateu8 out));
        a <- next;
        out <- a;
        out <- (out `>>` (W8.of_int 4));
        out <- (out `&` (W32.of_int 31));
        next <- (BArray8192.get32 ap (W64.to_uint (base + (W64.of_int 5))));
        part <- next;
        part <- (part `<<` (W8.of_int 5));
        part <- (part `&` (W32.of_int 255));
        out <- (out `|` part);
        bp <-
        (BArray1152.set8 bp (W64.to_uint (off + (W64.of_int 5)))
        (truncateu8 out));
        a <- next;
        out <- a;
        out <- (out `>>` (W8.of_int 3));
        out <- (out `&` (W32.of_int 63));
        next <- (BArray8192.get32 ap (W64.to_uint (base + (W64.of_int 6))));
        part <- next;
        part <- (part `<<` (W8.of_int 6));
        part <- (part `&` (W32.of_int 255));
        out <- (out `|` part);
        bp <-
        (BArray1152.set8 bp (W64.to_uint (off + (W64.of_int 6)))
        (truncateu8 out));
        a <- next;
        out <- a;
        out <- (out `>>` (W8.of_int 2));
        out <- (out `&` (W32.of_int 127));
        next <- (BArray8192.get32 ap (W64.to_uint (base + (W64.of_int 7))));
        part <- next;
        part <- (part `<<` (W8.of_int 7));
        part <- (part `&` (W32.of_int 255));
        out <- (out `|` part);
        bp <-
        (BArray1152.set8 bp (W64.to_uint (off + (W64.of_int 7)))
        (truncateu8 out));
        out <- next;
        out <- (out `>>` (W8.of_int 1));
        bp <-
        (BArray1152.set8 bp (W64.to_uint (off + (W64.of_int 8)))
        (truncateu8 out));
        i <- (i + (W64.of_int 1));
        off <- (off + (W64.of_int 9));
      }
      coeff_base <- (coeff_base + (W64.of_int 256));
      poly <- (poly + (W64.of_int 1));
    }
    return bp;
  }
  proc _encode_h_prepare (symsp:BArray2048.t, badp:BArray8.t,
                          hp:BArray8192.t, count:W64.t, mh:W64.t,
                          offset:W64.t) : BArray2048.t * BArray8.t = {
    var ms:W64.t;
    var hcut:W64.t;
    var upper:W64.t;
    var off32:W32.t;
    var bad:W64.t;
    var i:W64.t;
    var tmp:W32.t;
    var tmp64:W64.t;
    var s:W8.t;
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    hp <- (protect_ptr hp ms);
    count <- (protect_64 count ms);
    mh <- (protect_64 mh ms);
    offset <- (protect_64 offset ms);
    hcut <- mh;
    hcut <- (hcut - (W64.of_int 1));
    hcut <- (hcut `>>` (W8.of_int 1));
    upper <- hcut;
    upper <- (upper + offset);
    off32 <- (truncateu32 offset);
    bad <- (W64.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult count)) {
      if ((bad <> (W64.of_int 0))) {
        count <- i;
      } else {
        tmp <- (BArray8192.get32 hp (W64.to_uint i));
        tmp64 <- (zeroextu64 tmp);
        (* Erased call to declassify *)
        ms <- (init_msf);
        tmp64 <- (protect_64 tmp64 ms);
        if ((hcut \ult tmp64)) {
          if ((tmp64 \ule upper)) {
            bad <- (W64.of_int 1);
          } else {
            tmp <- (tmp - off32);
          }
        } else {
          
        }
        s <- (truncateu8 tmp);
        symsp <- (BArray2048.set8 symsp (W64.to_uint i) s);
        i <- (i + (W64.of_int 1));
      }
    }
    badp <- (BArray8.set64 badp 0 bad);
    return (symsp, badp);
  }
  proc _rans_encode (encp:BArray2048.t, statep:BArray16.t,
                     symsp:BArray2048.t, esymsp:BArray528.t, count:W64.t) : 
  BArray2048.t * BArray16.t = {
    var x:W32.t;
    var off:W64.t;
    var bad:W64.t;
    var i:W64.t;
    var s:W8.t;
    var idx:W64.t;
    var ms:W64.t;
    var x_max:W32.t;
    var rcp_freq:W32.t;
    var bias:W32.t;
    var packed:W32.t;
    var cmpl_freq:W32.t;
    var rcp_shift:W32.t;
    var byte:W8.t;
    var prod:W64.t;
    var hi:W64.t;
    var q:W32.t;
    var byte32:W32.t;
    x <- (W32.of_int 8388608);
    off <- count;
    bad <- (W64.of_int 0);
    i <- count;
    while (((W64.of_int 0) \ult i)) {
      if ((bad <> (W64.of_int 0))) {
        i <- (W64.of_int 0);
      } else {
        i <- (i - (W64.of_int 1));
        s <- (BArray2048.get8 symsp (W64.to_uint i));
        idx <- (zeroextu64 s);
        idx <- (idx * (W64.of_int 4));
        (* Erased call to declassify *)
        ms <- (init_msf);
        idx <- (protect_64 idx ms);
        x_max <- (BArray528.get32 esymsp (W64.to_uint idx));
        (* Erased call to declassify *)
        ms <- (init_msf);
        x_max <- (protect_32 x_max ms);
        idx <- (idx + (W64.of_int 1));
        rcp_freq <- (BArray528.get32 esymsp (W64.to_uint idx));
        idx <- (idx + (W64.of_int 1));
        bias <- (BArray528.get32 esymsp (W64.to_uint idx));
        idx <- (idx + (W64.of_int 1));
        packed <- (BArray528.get32 esymsp (W64.to_uint idx));
        cmpl_freq <- packed;
        cmpl_freq <- (cmpl_freq `&` (W32.of_int 65535));
        rcp_shift <- packed;
        rcp_shift <- (rcp_shift `>>` (W8.of_int 16));
        (* Erased call to declassify *)
        ms <- (init_msf);
        rcp_shift <- (protect_32 rcp_shift ms);
        while ((x_max \ule x)) {
          off <- (off - (W64.of_int 1));
          byte <- (truncateu8 x);
          encp <- (BArray2048.set8 encp (W64.to_uint off) byte);
          x <- (x `>>` (W8.of_int 8));
        }
        prod <- (zeroextu64 x);
        hi <- (zeroextu64 rcp_freq);
        prod <- (prod * hi);
        prod <- (prod `>>` (W8.of_int 32));
        q <- (truncateu32 prod);
        if ((rcp_shift = (W32.of_int 1))) {
          q <- (q `>>` (W8.of_int 1));
        } else {
          if ((rcp_shift = (W32.of_int 2))) {
            q <- (q `>>` (W8.of_int 2));
          } else {
            if ((rcp_shift = (W32.of_int 3))) {
              q <- (q `>>` (W8.of_int 3));
            } else {
              if ((rcp_shift = (W32.of_int 4))) {
                q <- (q `>>` (W8.of_int 4));
              } else {
                if ((rcp_shift = (W32.of_int 5))) {
                  q <- (q `>>` (W8.of_int 5));
                } else {
                  if ((rcp_shift = (W32.of_int 6))) {
                    q <- (q `>>` (W8.of_int 6));
                  } else {
                    if ((rcp_shift = (W32.of_int 7))) {
                      q <- (q `>>` (W8.of_int 7));
                    } else {
                      if ((rcp_shift = (W32.of_int 8))) {
                        q <- (q `>>` (W8.of_int 8));
                      } else {
                        if ((rcp_shift = (W32.of_int 9))) {
                          q <- (q `>>` (W8.of_int 9));
                        } else {
                          if ((rcp_shift = (W32.of_int 10))) {
                            q <- (q `>>` (W8.of_int 10));
                          } else {
                            if ((rcp_shift = (W32.of_int 11))) {
                              q <- (q `>>` (W8.of_int 11));
                            } else {
                              if ((rcp_shift = (W32.of_int 12))) {
                                q <- (q `>>` (W8.of_int 12));
                              } else {
                                if ((rcp_shift = (W32.of_int 13))) {
                                  q <- (q `>>` (W8.of_int 13));
                                } else {
                                  if ((rcp_shift = (W32.of_int 14))) {
                                    q <- (q `>>` (W8.of_int 14));
                                  } else {
                                    if ((rcp_shift = (W32.of_int 15))) {
                                      q <- (q `>>` (W8.of_int 15));
                                    } else {
                                      
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
        q <- (q * cmpl_freq);
        x <- (x + bias);
        x <- (x + q);
        if ((off \ult (W64.of_int 4))) {
          bad <- (W64.of_int 1);
        } else {
          
        }
      }
    }
    if ((bad = (W64.of_int 0))) {
      off <- (off - (W64.of_int 4));
      byte32 <- x;
      byte <- (truncateu8 byte32);
      encp <- (BArray2048.set8 encp (W64.to_uint off) byte);
      idx <- off;
      idx <- (idx + (W64.of_int 1));
      byte32 <- (byte32 `>>` (W8.of_int 8));
      byte <- (truncateu8 byte32);
      encp <- (BArray2048.set8 encp (W64.to_uint idx) byte);
      idx <- (idx + (W64.of_int 1));
      byte32 <- (byte32 `>>` (W8.of_int 8));
      byte <- (truncateu8 byte32);
      encp <- (BArray2048.set8 encp (W64.to_uint idx) byte);
      idx <- (idx + (W64.of_int 1));
      byte32 <- (byte32 `>>` (W8.of_int 8));
      byte <- (truncateu8 byte32);
      encp <- (BArray2048.set8 encp (W64.to_uint idx) byte);
    } else {
      
    }
    statep <- (BArray16.set64 statep 0 off);
    statep <- (BArray16.set64 statep 1 bad);
    return (encp, statep);
  }
  proc _encode_hb_z1_prepare (symsp:BArray2048.t, badp:BArray8.t,
                              hp:BArray8192.t, count:W64.t, mhb:W64.t,
                              offset:W64.t) : BArray2048.t * BArray8.t = {
    var ms:W64.t;
    var bad:W64.t;
    var i:W64.t;
    var a:W32.t;
    var tmp:W64.t;
    var neg:W64.t;
    var b:bool;
    var s:W8.t;
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    hp <- (protect_ptr hp ms);
    count <- (protect_64 count ms);
    mhb <- (protect_64 mhb ms);
    offset <- (protect_64 offset ms);
    bad <- (W64.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult count)) {
      if ((bad <> (W64.of_int 0))) {
        count <- i;
      } else {
        a <- (BArray8192.get32 hp (W64.to_uint i));
        tmp <- (sigextu64 a);
        tmp <- (tmp + offset);
        neg <- tmp;
        neg <- (neg `|>>` (W8.of_int 63));
        (* Erased call to declassify *)
        ms <- (init_msf);
        neg <- (protect_64 neg ms);
        b <- (neg <> (W64.of_int 0));
        if (b) {
          ms <- (update_msf b ms);
          bad <- (W64.of_int 1);
        } else {
          ms <- (update_msf (! b) ms);
          (* Erased call to declassify *)
          tmp <- (protect_64 tmp ms);
          b <- (mhb \ule tmp);
          if (b) {
            ms <- (update_msf b ms);
            bad <- (W64.of_int 1);
          } else {
            ms <- (update_msf (! b) ms);
            s <- (truncateu8 tmp);
            symsp <- (BArray2048.set8 symsp (W64.to_uint i) s);
          }
        }
        i <- (i + (W64.of_int 1));
      }
    }
    badp <- (BArray8.set64 badp 0 bad);
    return (symsp, badp);
  }
  proc __copy_encoded_suffix (outp:BArray2048.t, encp:BArray2048.t,
                              off:W64.t, size:W64.t) : BArray2048.t = {
    var i:W64.t;
    var idx:W64.t;
    var b:W8.t;
    i <- (W64.of_int 0);
    while ((i \ult size)) {
      idx <- off;
      idx <- (idx + i);
      b <- (BArray2048.get8 encp (W64.to_uint idx));
      outp <- (BArray2048.set8 outp (W64.to_uint i) b);
      i <- (i + (W64.of_int 1));
    }
    return outp;
  }
  proc _encode_h_full (outp:BArray2048.t, hp:BArray8192.t,
                       esymsp:BArray528.t, count:W64.t, mh:W64.t,
                       offset:W64.t) : BArray2048.t * W64.t = {
    var size:W64.t;
    var symbols:BArray2048.t;
    var symsp:BArray2048.t;
    var encoding:BArray2048.t;
    var encp:BArray2048.t;
    var state:BArray16.t;
    var statep:BArray16.t;
    var bad:BArray8.t;
    var badp:BArray8.t;
    var badv:W64.t;
    var ms:W64.t;
    var b:bool;
    var off:W64.t;
    bad <- witness;
    badp <- witness;
    encoding <- witness;
    encp <- witness;
    state <- witness;
    statep <- witness;
    symbols <- witness;
    symsp <- witness;
    symsp <- symbols;
    encp <- encoding;
    statep <- state;
    badp <- bad;
    (* Erased call to spill *)
    (symsp, badp) <@ _encode_h_prepare (symsp, badp, hp, count, mh, offset);
    (* Erased call to unspill *)
    badv <- (BArray8.get64 badp 0);
    (* Erased call to declassify *)
    ms <- (init_msf);
    badv <- (protect_64 badv ms);
    b <- (badv <> (W64.of_int 0));
    if (b) {
      ms <- (update_msf b ms);
      size <- (W64.of_int 0);
    } else {
      ms <- (update_msf (! b) ms);
      (* Erased call to spill *)
      (encp, statep) <@ _rans_encode (encp, statep, symsp, esymsp, count);
      (* Erased call to unspill *)
      badv <- (BArray16.get64 statep 1);
      (* Erased call to declassify *)
      ms <- (init_msf);
      badv <- (protect_64 badv ms);
      b <- (badv <> (W64.of_int 0));
      if (b) {
        ms <- (update_msf b ms);
        size <- (W64.of_int 0);
      } else {
        ms <- (update_msf (! b) ms);
        off <- (BArray16.get64 statep 0);
        size <- count;
        size <- (size - off);
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        ms <- (init_msf);
        off <- (protect_64 off ms);
        size <- (protect_64 size ms);
        outp <@ __copy_encoded_suffix (outp, encp, off, size);
      }
    }
    return (outp, size);
  }
  proc _encode_hb_z1_full (outp:BArray2048.t, hp:BArray8192.t,
                           esymsp:BArray528.t, count:W64.t, mhb:W64.t,
                           offset:W64.t) : BArray2048.t * W64.t = {
    var size:W64.t;
    var symbols:BArray2048.t;
    var symsp:BArray2048.t;
    var encoding:BArray2048.t;
    var encp:BArray2048.t;
    var state:BArray16.t;
    var statep:BArray16.t;
    var bad:BArray8.t;
    var badp:BArray8.t;
    var badv:W64.t;
    var ms:W64.t;
    var b:bool;
    var off:W64.t;
    bad <- witness;
    badp <- witness;
    encoding <- witness;
    encp <- witness;
    state <- witness;
    statep <- witness;
    symbols <- witness;
    symsp <- witness;
    symsp <- symbols;
    encp <- encoding;
    statep <- state;
    badp <- bad;
    (* Erased call to spill *)
    (symsp, badp) <@ _encode_hb_z1_prepare (symsp, badp, hp, count, mhb,
    offset);
    (* Erased call to unspill *)
    badv <- (BArray8.get64 badp 0);
    (* Erased call to declassify *)
    ms <- (init_msf);
    badv <- (protect_64 badv ms);
    b <- (badv <> (W64.of_int 0));
    if (b) {
      ms <- (update_msf b ms);
      size <- (W64.of_int 0);
    } else {
      ms <- (update_msf (! b) ms);
      (* Erased call to spill *)
      (encp, statep) <@ _rans_encode (encp, statep, symsp, esymsp, count);
      (* Erased call to unspill *)
      badv <- (BArray16.get64 statep 1);
      (* Erased call to declassify *)
      ms <- (init_msf);
      badv <- (protect_64 badv ms);
      b <- (badv <> (W64.of_int 0));
      if (b) {
        ms <- (update_msf b ms);
        size <- (W64.of_int 0);
      } else {
        ms <- (update_msf (! b) ms);
        off <- (BArray16.get64 statep 0);
        size <- count;
        size <- (size - off);
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        ms <- (init_msf);
        off <- (protect_64 off ms);
        size <- (protect_64 size ms);
        outp <@ __copy_encoded_suffix (outp, encp, off, size);
      }
    }
    return (outp, size);
  }
  proc __hamming_weight_8 (x:W32.t) : W32.t = {
    var y:W32.t;
    y <- x;
    y <- (y `&` (W32.of_int 85));
    x <- (x `>>` (W8.of_int 1));
    x <- (x `&` (W32.of_int 85));
    x <- (x + y);
    y <- x;
    y <- (y `&` (W32.of_int 51));
    x <- (x `>>` (W8.of_int 2));
    x <- (x `&` (W32.of_int 51));
    x <- (x + y);
    y <- x;
    y <- (y `&` (W32.of_int 15));
    x <- (x `>>` (W8.of_int 4));
    x <- (x `&` (W32.of_int 15));
    x <- (x + y);
    return x;
  }
  proc _poly_challenge_m5_frombytes (cp:BArray1024.t, bp:BArray32.t) : 
  BArray1024.t = {
    var hwt:W32.t;
    var i:W64.t;
    var byte:W32.t;
    var cond:W32.t;
    var cand:W32.t;
    var w0:W32.t;
    var mask:W32.t;
    var sel:W32.t;
    var neg:W32.t;
    var idx:W64.t;
    var j:int;
    var bit:W32.t;
    hwt <- (W32.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      byte <- (zeroextu32 (BArray32.get8 bp (W64.to_uint i)));
      byte <@ __hamming_weight_8 (byte);
      hwt <- (hwt + byte);
      i <- (i + (W64.of_int 1));
    }
    cond <- (W32.of_int 128);
    cond <- (cond - hwt);
    cand <- cond;
    cand <- (cand `>>` (W8.of_int 8));
    cand <- (cand `&` (W32.of_int 255));
    w0 <- (zeroextu32 (BArray32.get8 bp 0));
    w0 <- (w0 `&` (W32.of_int 1));
    mask <- (W32.of_int 0);
    mask <- (mask - w0);
    mask <- (mask `&` (W32.of_int 255));
    w0 <- mask;
    sel <- cond;
    neg <- (W32.of_int 0);
    neg <- (neg - cond);
    sel <- (sel `|` neg);
    sel <- (sel `|>>` (W8.of_int 31));
    mask <- cand;
    mask <- (mask `^` w0);
    mask <- (mask `&` sel);
    mask <- (mask `^` w0);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      byte <- (zeroextu32 (BArray32.get8 bp (W64.to_uint i)));
      byte <- (byte `^` mask);
      j <- 0;
      while ((j < 8)) {
        idx <- i;
        idx <- (idx * (W64.of_int 8));
        idx <- (idx + (W64.of_int j));
        bit <- byte;
        bit <- (bit `>>` (W8.of_int j));
        bit <- (bit `&` (W32.of_int 1));
        (* Erased call to declassify *)
        cp <- (BArray1024.set32 cp (W64.to_uint idx) bit);
        j <- (j + 1);
      }
      i <- (i + (W64.of_int 1));
    }
    return cp;
  }
  proc _poly_challenge_m23_init (cp:BArray1024.t) : BArray1024.t = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      cp <- (BArray1024.set32 cp (W64.to_uint i) (W32.of_int 0));
      i <- (i + (W64.of_int 1));
    }
    return cp;
  }
  proc __poly_challenge_shake256_finalize (sp_0:BArray200.t,
                                           statep:BArray16.t) : BArray200.t = {
    var ms:W64.t;
    var pos:W64.t;
    var lane:W64.t;
    var shift:W8.t;
    var t:W64.t;
    ms <- (init_msf);
    pos <- (BArray16.get64 statep 0);
    (* Erased call to declassify *)
    pos <- (protect_64 pos ms);
    lane <- pos;
    lane <- (lane `>>` (W8.of_int 3));
    shift <- (truncateu8 pos);
    shift <- (shift `&` (W8.of_int 7));
    shift <- (shift `<<` (W8.of_int 3));
    t <- (W64.of_int 31);
    t <- (t `<<` (shift `&` (W8.of_int 63)));
    sp_0 <-
    (BArray200.set64 sp_0 (W64.to_uint lane)
    ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
    t <- (W64.of_int 1);
    t <- (t `<<` (W8.of_int 63));
    sp_0 <- (BArray200.set64 sp_0 16 ((BArray200.get64 sp_0 16) `^` t));
    return sp_0;
  }
  proc __poly_challenge_squeeze256_136 (outp:BArray136.t, sp_0:BArray200.t) : 
  BArray136.t * BArray200.t = {
    var idx:W64.t;
    var ms:W64.t;
    var i:W64.t;
    var lane:W64.t;
    var t:W64.t;
    var j:W64.t;
    var b:W8.t;
    idx <- (W64.of_int 0);
    (* Erased call to spill *)
    sp_0 <@ _keccakf1600 (sp_0);
    (* Erased call to unspill *)
    ms <- (init_msf);
    outp <- (protect_ptr outp ms);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 136))) {
      lane <- i;
      lane <- (lane `>>` (W8.of_int 3));
      t <- (BArray200.get64 sp_0 (W64.to_uint lane));
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int 8))) {
        b <- (truncateu8 t);
        outp <- (BArray136.set8 outp (W64.to_uint idx) b);
        t <- (t `>>` (W8.of_int 8));
        idx <- (idx + (W64.of_int 1));
        j <- (j + (W64.of_int 1));
      }
      i <- (i + (W64.of_int 8));
    }
    return (outp, sp_0);
  }
  proc __poly_challenge_squeeze256_32 (outp:BArray32.t, sp_0:BArray200.t) : 
  BArray32.t * BArray200.t = {
    var idx:W64.t;
    var ms:W64.t;
    var i:W64.t;
    var lane:W64.t;
    var t:W64.t;
    var j:W64.t;
    var b:W8.t;
    idx <- (W64.of_int 0);
    (* Erased call to spill *)
    sp_0 <@ _keccakf1600 (sp_0);
    (* Erased call to unspill *)
    ms <- (init_msf);
    outp <- (protect_ptr outp ms);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      lane <- i;
      lane <- (lane `>>` (W8.of_int 3));
      t <- (BArray200.get64 sp_0 (W64.to_uint lane));
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int 8))) {
        b <- (truncateu8 t);
        outp <- (BArray32.set8 outp (W64.to_uint idx) b);
        t <- (t `>>` (W8.of_int 8));
        idx <- (idx + (W64.of_int 1));
        j <- (j + (W64.of_int 1));
      }
      i <- (i + (W64.of_int 8));
    }
    return (outp, sp_0);
  }
  proc _polyvec_decompose_z1 (lowp:BArray8192.t, highp:BArray8192.t,
                              ap:BArray8192.t, count:W64.t) : BArray8192.t *
                                                              BArray8192.t = {
    var i:W64.t;
    var a:W32.t;
    var hb:W32.t;
    var lb:W32.t;
    var center:W32.t;
    var sub:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult count)) {
      a <- (BArray8192.get32 ap (W64.to_uint i));
      hb <- a;
      hb <- (hb + (W32.of_int 128));
      hb <- (hb `|>>` (W8.of_int 8));
      highp <- (BArray8192.set32 highp (W64.to_uint i) hb);
      lb <- a;
      lb <- (lb `&` (W32.of_int (256 - 1)));
      center <- (W32.of_int 128);
      center <- (center - lb);
      center <- (center - (W32.of_int 1));
      center <- (center `|>>` (W8.of_int 31));
      sub <- center;
      sub <- (sub `&` (W32.of_int 256));
      lb <- (lb - sub);
      lowp <- (BArray8192.set32 lowp (W64.to_uint i) lb);
      i <- (i + (W64.of_int 1));
    }
    return (lowp, highp);
  }
  proc _polyvec_highbits_hint_m23 (rp:BArray8192.t, ap:BArray8192.t,
                                   count:W64.t) : BArray8192.t = {
    var i:W64.t;
    var hb:W32.t;
    var edge:W32.t;
    var sub:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult count)) {
      hb <- (BArray8192.get32 ap (W64.to_uint i));
      hb <- (hb + (W32.of_int 256));
      hb <- (hb `|>>` (W8.of_int 9));
      edge <- (W32.of_int 252);
      edge <- (edge - hb);
      edge <- (edge - (W32.of_int 1));
      edge <- (edge `|>>` (W8.of_int 31));
      sub <- edge;
      sub <- (sub `&` (W32.of_int 252));
      hb <- (hb - sub);
      rp <- (BArray8192.set32 rp (W64.to_uint i) hb);
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc _polyvec_highbits_hint_m5 (rp:BArray8192.t, ap:BArray8192.t,
                                  count:W64.t) : BArray8192.t = {
    var i:W64.t;
    var hb:W32.t;
    var edge:W32.t;
    var sub:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult count)) {
      hb <- (BArray8192.get32 ap (W64.to_uint i));
      hb <- (hb + (W32.of_int 128));
      hb <- (hb `|>>` (W8.of_int 8));
      edge <- (W32.of_int 504);
      edge <- (edge - hb);
      edge <- (edge - (W32.of_int 1));
      edge <- (edge `|>>` (W8.of_int 31));
      sub <- edge;
      sub <- (sub `&` (W32.of_int 504));
      hb <- (hb - sub);
      rp <- (BArray8192.set32 rp (W64.to_uint i) hb);
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc _sign_prepare_cs (cs1p:BArray8192.t, chatp:BArray1024.t,
                         cp:BArray1024.t) : BArray8192.t * BArray1024.t = {
    var i:W64.t;
    var a:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      a <- (BArray1024.get32 cp (W64.to_uint i));
      cs1p <- (BArray8192.set32 cs1p (W64.to_uint i) a);
      chatp <- (BArray1024.set32 chatp (W64.to_uint i) a);
      i <- (i + (W64.of_int 1));
    }
    chatp <@ _poly_ntt (chatp);
    return (cs1p, chatp);
  }
  proc _sign_compute_cs1_tail (cs1p:BArray8192.t, chatp:BArray1024.t,
                               s1p:BArray8192.t, lcount:W64.t) : BArray8192.t = {
    var poly:W64.t;
    var base:W64.t;
    var srcbase:W64.t;
    var j:W64.t;
    var idx:W64.t;
    var idx2:W64.t;
    var a:W32.t;
    var b:W32.t;
    var t:W32.t;
    var zetasp:BArray1024.t;
    var zetasctr:W64.t;
    var len:W64.t;
    var start:W64.t;
    var zeta_0:W32.t;
    var cmp:W64.t;
    var offset:W64.t;
    var coeff:W32.t;
    var s:W32.t;
    zetasp <- witness;
    poly <- (W64.of_int 1);
    base <- (W64.of_int 256);
    srcbase <- (W64.of_int 0);
    while ((poly \ult lcount)) {
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int 256))) {
        idx <- srcbase;
        idx <- (idx + j);
        idx2 <- base;
        idx2 <- (idx2 + j);
        a <- (BArray8192.get32 s1p (W64.to_uint idx));
        b <- (BArray1024.get32 chatp (W64.to_uint j));
        t <@ __fqmul (a, b);
        cs1p <- (BArray8192.set32 cs1p (W64.to_uint idx2) t);
        j <- (j + (W64.of_int 1));
      }
      base <- (base + (W64.of_int 256));
      srcbase <- (srcbase + (W64.of_int 256));
      poly <- (poly + (W64.of_int 1));
    }
    zetasp <- jzetas_inv;
    poly <- (W64.of_int 1);
    base <- (W64.of_int 256);
    while ((poly \ult lcount)) {
      zetasctr <- (W64.of_int 0);
      len <- (W64.of_int 1);
      while ((len \ult (W64.of_int 256))) {
        start <- (W64.of_int 0);
        while ((start \ult (W64.of_int 256))) {
          zeta_0 <- (BArray1024.get32 zetasp (W64.to_uint zetasctr));
          zetasctr <- (zetasctr + (W64.of_int 1));
          j <- start;
          cmp <- start;
          cmp <- (cmp + len);
          while ((j \ult cmp)) {
            idx <- base;
            idx <- (idx + j);
            t <- (BArray8192.get32 cs1p (W64.to_uint idx));
            offset <- j;
            offset <- (offset + len);
            idx2 <- base;
            idx2 <- (idx2 + offset);
            coeff <- (BArray8192.get32 cs1p (W64.to_uint idx2));
            s <- t;
            s <- (s + coeff);
            cs1p <- (BArray8192.set32 cs1p (W64.to_uint idx) s);
            t <- (t - coeff);
            t <@ __fqmul (zeta_0, t);
            cs1p <- (BArray8192.set32 cs1p (W64.to_uint idx2) t);
            j <- (j + (W64.of_int 1));
          }
          start <- j;
          start <- (start + len);
        }
        len <- (len `<<` (W8.of_int 1));
      }
      zeta_0 <- (BArray1024.get32 zetasp 255);
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int 256))) {
        idx <- base;
        idx <- (idx + j);
        coeff <- (BArray8192.get32 cs1p (W64.to_uint idx));
        t <@ __fqmul (zeta_0, coeff);
        cs1p <- (BArray8192.set32 cs1p (W64.to_uint idx) t);
        j <- (j + (W64.of_int 1));
      }
      base <- (base + (W64.of_int 256));
      poly <- (poly + (W64.of_int 1));
    }
    return cs1p;
  }
  proc _sign_add_double_z2rnd (ayp:BArray8192.t, z2p:BArray8192.t,
                               count:W64.t) : BArray8192.t * BArray8192.t = {
    var i:W64.t;
    var z:W32.t;
    var ay:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult count)) {
      z <- (BArray8192.get32 z2p (W64.to_uint i));
      z <- (z `<<` (W8.of_int 1));
      z2p <- (BArray8192.set32 z2p (W64.to_uint i) z);
      ay <- (BArray8192.get32 ayp (W64.to_uint i));
      ay <- (ay + z);
      ayp <- (BArray8192.set32 ayp (W64.to_uint i) ay);
      i <- (i + (W64.of_int 1));
    }
    return (ayp, z2p);
  }
  proc _sign_make_hint (hp:BArray8192.t, highbitsp:BArray8192.t,
                        ayp:BArray8192.t, z2rndp:BArray8192.t, count:W64.t,
                        half_alpha:int, log_alpha:int, bound:int) : BArray8192.t = {
    var i:W64.t;
    var ay:W32.t;
    var z:W32.t;
    var tmp:W32.t;
    var hb:W32.t;
    var edge:W32.t;
    var sub:W32.t;
    var h:W32.t;
    var add:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult count)) {
      ay <- (BArray8192.get32 ayp (W64.to_uint i));
      z <- (BArray8192.get32 z2rndp (W64.to_uint i));
      z <- (z `<<` (W8.of_int 1));
      tmp <- ay;
      tmp <- (tmp - z);
      tmp <@ __freeze2q (tmp);
      hb <- tmp;
      hb <- (hb + (W32.of_int half_alpha));
      hb <- (hb `|>>` (W8.of_int log_alpha));
      edge <- (W32.of_int bound);
      edge <- (edge - hb);
      edge <- (edge - (W32.of_int 1));
      edge <- (edge `|>>` (W8.of_int 31));
      sub <- edge;
      sub <- (sub `&` (W32.of_int bound));
      hb <- (hb - sub);
      h <- (BArray8192.get32 highbitsp (W64.to_uint i));
      h <- (h - hb);
      add <- h;
      add <- (add `|>>` (W8.of_int 31));
      add <- (add `&` (W32.of_int bound));
      h <- (h + add);
      hp <- (BArray8192.set32 hp (W64.to_uint i) h);
      i <- (i + (W64.of_int 1));
    }
    return hp;
  }
  proc __pack_sig_suffix_at (sigp:BArray2948.t, hbencp:BArray2048.t,
                             hencp:BArray2048.t, off:W64.t, hbsize:W64.t,
                             hsize:W64.t, offsets:W64.t) : BArray2948.t = {
    var b:W32.t;
    var dst:W64.t;
    var i:W64.t;
    b <- (truncateu32 offsets);
    sigp <- (BArray2948.set8 sigp (W64.to_uint off) (truncateu8 b));
    b <- (truncateu32 offsets);
    b <- (b `>>` (W8.of_int 8));
    sigp <-
    (BArray2948.set8 sigp (W64.to_uint (off + (W64.of_int 1))) (truncateu8 b)
    );
    dst <- off;
    dst <- (dst + (W64.of_int 2));
    i <- (W64.of_int 0);
    while ((i \ult hbsize)) {
      b <- (zeroextu32 (BArray2048.get8 hbencp (W64.to_uint i)));
      sigp <- (BArray2948.set8 sigp (W64.to_uint dst) (truncateu8 b));
      dst <- (dst + (W64.of_int 1));
      i <- (i + (W64.of_int 1));
    }
    i <- (W64.of_int 0);
    while ((i \ult hsize)) {
      b <- (zeroextu32 (BArray2048.get8 hencp (W64.to_uint i)));
      sigp <- (BArray2948.set8 sigp (W64.to_uint dst) (truncateu8 b));
      dst <- (dst + (W64.of_int 1));
      i <- (i + (W64.of_int 1));
    }
    return sigp;
  }
  proc _pack_sig_full (sigp:BArray2948.t, badp:BArray8.t, cp:BArray1024.t,
                       lowp:BArray8192.t, hbzp:BArray8192.t, hp:BArray8192.t,
                       hb_esymsp:BArray528.t, h_esymsp:BArray528.t,
                       sigbytes_i:int, lcount_i:int, hb_count_i:int,
                       hb_m_i:int, hb_offset_i:int, h_count_i:int, h_m_i:int,
                       h_offset_i:int, base_hb_i:int, base_h_i:int,
                       payload_limit_i:int) : BArray2948.t * BArray8.t = {
    var hbenc:BArray2048.t;
    var hbencp:BArray2048.t;
    var henc:BArray2048.t;
    var hencp:BArray2048.t;
    var sigbytes:W64.t;
    var lcount:W64.t;
    var hb_count:W64.t;
    var hb_m:W64.t;
    var hb_offset:W64.t;
    var hbsize:W64.t;
    var h_count:W64.t;
    var h_m:W64.t;
    var h_offset:W64.t;
    var hsize:W64.t;
    var base_hb:W64.t;
    var base_h:W64.t;
    var payload_limit:W64.t;
    var ms:W64.t;
    var offsets:W64.t;
    var bad:W64.t;
    var prefix_off:W64.t;
    hbenc <- witness;
    hbencp <- witness;
    henc <- witness;
    hencp <- witness;
    hbencp <- hbenc;
    hencp <- henc;
    sigbytes <- (W64.of_int sigbytes_i);
    lcount <- (W64.of_int lcount_i);
    (* Erased call to spill *)
    sigp <@ _pack_sig_prefix (sigp, cp, lowp, lcount, sigbytes);
    (* Erased call to unspill *)
    hb_count <- (W64.of_int hb_count_i);
    hb_m <- (W64.of_int hb_m_i);
    hb_offset <- (W64.of_int hb_offset_i);
    (* Erased call to spill *)
    (hbencp, hbsize) <@ _encode_hb_z1_full (hbencp, hbzp, hb_esymsp,
    hb_count, hb_m, hb_offset);
    (* Erased call to unspill *)
    h_count <- (W64.of_int h_count_i);
    h_m <- (W64.of_int h_m_i);
    h_offset <- (W64.of_int h_offset_i);
    (* Erased call to spill *)
    (hencp, hsize) <@ _encode_h_full (hencp, hp, h_esymsp, h_count, h_m,
    h_offset);
    (* Erased call to unspill *)
    base_hb <- (W64.of_int base_hb_i);
    base_h <- (W64.of_int base_h_i);
    payload_limit <- (W64.of_int payload_limit_i);
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    hbsize <- (protect_64 hbsize ms);
    hsize <- (protect_64 hsize ms);
    (offsets, bad) <@ __pack_sig_size_offsets_values (hbsize, hsize, 
    base_hb, base_h, payload_limit);
    ms <- (init_msf);
    offsets <- (protect_64 offsets ms);
    bad <- (protect_64 bad ms);
    if ((bad = (W64.of_int 0))) {
      lcount <- (W64.of_int lcount_i);
      prefix_off <- lcount;
      prefix_off <- (prefix_off * (W64.of_int 256));
      prefix_off <- (prefix_off + (W64.of_int 32));
      sigp <@ __pack_sig_suffix_at (sigp, hbencp, hencp, prefix_off, 
      hbsize, hsize, offsets);
    } else {
      
    }
    badp <- (BArray8.set64 badp 0 bad);
    return (sigp, badp);
  }
  proc __unpack_vk_m23_coeffs (bp:BArray8192.t, vkp:BArray2752.t, count:W64.t) : 
  BArray8192.t = {
    var poly:W64.t;
    var coeff_base:W64.t;
    var in_base:W64.t;
    var i:W64.t;
    var off:W64.t;
    var base:W64.t;
    var r:W32.t;
    var part:W32.t;
    poly <- (W64.of_int 0);
    coeff_base <- (W64.of_int 0);
    in_base <- (W64.of_int 32);
    while ((poly \ult count)) {
      i <- (W64.of_int 0);
      off <- in_base;
      while ((i \ult (W64.of_int 32))) {
        base <- coeff_base;
        base <- (base + ((W64.of_int 8) * i));
        r <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 0)))));
        part <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 1)))));
        part <- (part `&` (W32.of_int 127));
        part <- (part `<<` (W8.of_int 8));
        r <- (r `|` part);
        bp <- (BArray8192.set32 bp (W64.to_uint (base + (W64.of_int 0))) r);
        r <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 1)))));
        r <- (r `>>` (W8.of_int 7));
        part <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 2)))));
        part <- (part `<<` (W8.of_int 1));
        r <- (r `|` part);
        part <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 3)))));
        part <- (part `&` (W32.of_int 63));
        part <- (part `<<` (W8.of_int 9));
        r <- (r `|` part);
        bp <- (BArray8192.set32 bp (W64.to_uint (base + (W64.of_int 1))) r);
        r <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 3)))));
        r <- (r `>>` (W8.of_int 6));
        part <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 4)))));
        part <- (part `<<` (W8.of_int 2));
        r <- (r `|` part);
        part <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 5)))));
        part <- (part `&` (W32.of_int 31));
        part <- (part `<<` (W8.of_int 10));
        r <- (r `|` part);
        bp <- (BArray8192.set32 bp (W64.to_uint (base + (W64.of_int 2))) r);
        r <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 5)))));
        r <- (r `>>` (W8.of_int 5));
        part <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 6)))));
        part <- (part `<<` (W8.of_int 3));
        r <- (r `|` part);
        part <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 7)))));
        part <- (part `&` (W32.of_int 15));
        part <- (part `<<` (W8.of_int 11));
        r <- (r `|` part);
        bp <- (BArray8192.set32 bp (W64.to_uint (base + (W64.of_int 3))) r);
        r <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 7)))));
        r <- (r `>>` (W8.of_int 4));
        part <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 8)))));
        part <- (part `<<` (W8.of_int 4));
        r <- (r `|` part);
        part <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 9)))));
        part <- (part `&` (W32.of_int 7));
        part <- (part `<<` (W8.of_int 12));
        r <- (r `|` part);
        bp <- (BArray8192.set32 bp (W64.to_uint (base + (W64.of_int 4))) r);
        r <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 9)))));
        r <- (r `>>` (W8.of_int 3));
        part <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 10)))));
        part <- (part `<<` (W8.of_int 5));
        r <- (r `|` part);
        part <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 11)))));
        part <- (part `&` (W32.of_int 3));
        part <- (part `<<` (W8.of_int 13));
        r <- (r `|` part);
        bp <- (BArray8192.set32 bp (W64.to_uint (base + (W64.of_int 5))) r);
        r <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 11)))));
        r <- (r `>>` (W8.of_int 2));
        part <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 12)))));
        part <- (part `<<` (W8.of_int 6));
        r <- (r `|` part);
        part <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 13)))));
        part <- (part `&` (W32.of_int 1));
        part <- (part `<<` (W8.of_int 14));
        r <- (r `|` part);
        bp <- (BArray8192.set32 bp (W64.to_uint (base + (W64.of_int 6))) r);
        r <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 13)))));
        r <- (r `>>` (W8.of_int 1));
        r <- (r `&` (W32.of_int 127));
        part <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 14)))));
        part <- (part `<<` (W8.of_int 7));
        r <- (r `|` part);
        bp <- (BArray8192.set32 bp (W64.to_uint (base + (W64.of_int 7))) r);
        i <- (i + (W64.of_int 1));
        off <- (off + (W64.of_int 15));
      }
      coeff_base <- (coeff_base + (W64.of_int 256));
      in_base <- (in_base + (W64.of_int 480));
      poly <- (poly + (W64.of_int 1));
    }
    return bp;
  }
  proc __unpack_vk_m5_coeffs (bp:BArray8192.t, vkp:BArray2752.t, count:W64.t) : 
  BArray8192.t = {
    var poly:W64.t;
    var coeff_base:W64.t;
    var in_base:W64.t;
    var i:W64.t;
    var off:W64.t;
    var idx:W64.t;
    var b0:W32.t;
    var b1:W32.t;
    var r:W32.t;
    poly <- (W64.of_int 0);
    coeff_base <- (W64.of_int 0);
    in_base <- (W64.of_int 32);
    while ((poly \ult count)) {
      i <- (W64.of_int 0);
      off <- in_base;
      while ((i \ult (W64.of_int 256))) {
        idx <- coeff_base;
        idx <- (idx + i);
        b0 <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 0)))));
        b1 <-
        (zeroextu32
        (BArray2752.get8 vkp (W64.to_uint (off + (W64.of_int 1)))));
        r <- b0;
        b1 <- (b1 `<<` (W8.of_int 8));
        r <- (r `|` b1);
        bp <- (BArray8192.set32 bp (W64.to_uint idx) r);
        i <- (i + (W64.of_int 1));
        off <- (off + (W64.of_int 2));
      }
      coeff_base <- (coeff_base + (W64.of_int 256));
      in_base <- (in_base + (W64.of_int 512));
      poly <- (poly + (W64.of_int 1));
    }
    return bp;
  }
  proc __polyvec_sub_left_inplace (bp:BArray8192.t, matp:BArray32768.t,
                                   l:W64.t, rows:W64.t) : BArray8192.t = {
    var stride:W64.t;
    var row:W64.t;
    var bpidx:W64.t;
    var rowbase:W64.t;
    var j:W64.t;
    var matidx:W64.t;
    var a:W32.t;
    var b:W32.t;
    stride <- l;
    stride <- (stride * (W64.of_int 256));
    row <- (W64.of_int 0);
    bpidx <- (W64.of_int 0);
    rowbase <- (W64.of_int 0);
    while ((row \ult rows)) {
      j <- (W64.of_int 0);
      matidx <- rowbase;
      while ((j \ult (W64.of_int 256))) {
        a <- (BArray32768.get32 matp (W64.to_uint matidx));
        b <- (BArray8192.get32 bp (W64.to_uint bpidx));
        a <- (a - b);
        bp <- (BArray8192.set32 bp (W64.to_uint bpidx) a);
        bpidx <- (bpidx + (W64.of_int 1));
        matidx <- (matidx + (W64.of_int 1));
        j <- (j + (W64.of_int 1));
      }
      rowbase <- (rowbase + stride);
      row <- (row + (W64.of_int 1));
    }
    return bp;
  }
  proc _api_copy_addr_to_32 (dstp:BArray32.t, srcp:W64.t) : BArray32.t = {
    var i:W64.t;
    var addr:W64.t;
    var b:W8.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      addr <- srcp;
      addr <- (addr + i);
      b <- (loadW8 Glob.mem (W64.to_uint addr));
      dstp <- (BArray32.set8 dstp (W64.to_uint i) b);
      i <- (i + (W64.of_int 1));
    }
    return dstp;
  }
  proc _api_copy_addr_to_2752_prefix (dstp:BArray2752.t, srcp:W64.t,
                                      len:W64.t) : BArray2752.t = {
    var i:W64.t;
    var addr:W64.t;
    var b:W8.t;
    i <- (W64.of_int 0);
    while ((i \ult len)) {
      addr <- srcp;
      addr <- (addr + i);
      b <- (loadW8 Glob.mem (W64.to_uint addr));
      dstp <- (BArray2752.set8 dstp (W64.to_uint i) b);
      i <- (i + (W64.of_int 1));
    }
    while ((i \ult (W64.of_int 2752))) {
      dstp <- (BArray2752.set8 dstp (W64.to_uint i) (W8.of_int 0));
      i <- (i + (W64.of_int 1));
    }
    return dstp;
  }
  proc _api_copy_2948_to_raw (dstp:int, srcp:BArray2948.t, len:int) : int = {
    var b:W8.t;
    var i:int;
    var addr:int;
    i <- 0;
    while ((i < len)) {
      b <- (BArray2948.get8 srcp (W64.to_uint (W64.of_int i)));
      addr <- dstp;
      addr <- (addr + i);
      Glob.mem <- (storeW8 Glob.mem addr b);
      i <- (i + 1);
    }
    return dstp;
  }
  proc _api_copy_addr_to_addr_backward (dstp:W64.t, srcp:W64.t, len:W64.t) : 
  W64.t = {
    var i:W64.t;
    var src:W64.t;
    var dst:W64.t;
    var b:W8.t;
    i <- len;
    while ((i <> (W64.of_int 0))) {
      i <- (i - (W64.of_int 1));
      src <- srcp;
      src <- (src + i);
      dst <- dstp;
      dst <- (dst + i);
      b <- (loadW8 Glob.mem (W64.to_uint src));
      Glob.mem <- (storeW8 Glob.mem (W64.to_uint dst) b);
    }
    return dstp;
  }
  proc _api_reject () : W64.t = {
    var r:W64.t;
    r <- (W64.of_int 0);
    r <- (r - (W64.of_int 1));
    return r;
  }
  proc _sf_shake256_absorb_addr (sp_0:BArray200.t, statep:BArray16.t,
                                 inp:W64.t, inlen:W64.t) : BArray200.t *
                                                           BArray16.t = {
    var ms:W64.t;
    var pos:W64.t;
    var lane:W64.t;
    var b:W8.t;
    var t:W64.t;
    var shift:W8.t;
    ms <- (init_msf);
    statep <- (protect_ptr statep ms);
    sp_0 <- (protect_ptr sp_0 ms);
    pos <- (BArray16.get64 statep 0);
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    pos <- (protect_64 pos ms);
    inp <- (protect_64 inp ms);
    inlen <- (protect_64 inlen ms);
    while ((inlen <> (W64.of_int 0))) {
      lane <- pos;
      lane <- (lane `>>` (W8.of_int 3));
      b <- (loadW8 Glob.mem (W64.to_uint inp));
      t <- (zeroextu64 b);
      shift <- (truncateu8 pos);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      inp <- (inp + (W64.of_int 1));
      pos <- (pos + (W64.of_int 1));
      inlen <- (inlen - (W64.of_int 1));
      if ((pos = (W64.of_int 136))) {
        (* Erased call to spill *)
        sp_0 <@ _keccakf1600 (sp_0);
        (* Erased call to unspill *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        ms <- (init_msf);
        statep <- (protect_ptr statep ms);
        sp_0 <- (protect_ptr sp_0 ms);
        inp <- (protect_64 inp ms);
        inlen <- (protect_64 inlen ms);
        pos <- (protect_64 pos ms);
        pos <- (W64.of_int 0);
      } else {
        
      }
    }
    ms <- (init_msf);
    statep <- (protect_ptr statep ms);
    statep <- (BArray16.set64 statep 0 pos);
    return (sp_0, statep);
  }
  proc _sf_shake256_absorb_sk (sp_0:BArray200.t, statep:BArray16.t,
                               skp:BArray2752.t, inlen:W64.t) : BArray200.t *
                                                                BArray16.t = {
    var ms:W64.t;
    var pos:W64.t;
    var i:W64.t;
    var lane:W64.t;
    var b:W8.t;
    var t:W64.t;
    var shift:W8.t;
    ms <- (init_msf);
    statep <- (protect_ptr statep ms);
    sp_0 <- (protect_ptr sp_0 ms);
    skp <- (protect_ptr skp ms);
    pos <- (BArray16.get64 statep 0);
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    pos <- (protect_64 pos ms);
    inlen <- (protect_64 inlen ms);
    i <- (W64.of_int 0);
    while ((i \ult inlen)) {
      lane <- pos;
      lane <- (lane `>>` (W8.of_int 3));
      b <- (BArray2752.get8 skp (W64.to_uint i));
      t <- (zeroextu64 b);
      shift <- (truncateu8 pos);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      i <- (i + (W64.of_int 1));
      pos <- (pos + (W64.of_int 1));
      if ((pos = (W64.of_int 136))) {
        (* Erased call to spill *)
        sp_0 <@ _keccakf1600 (sp_0);
        (* Erased call to unspill *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        ms <- (init_msf);
        statep <- (protect_ptr statep ms);
        sp_0 <- (protect_ptr sp_0 ms);
        skp <- (protect_ptr skp ms);
        inlen <- (protect_64 inlen ms);
        i <- (protect_64 i ms);
        pos <- (protect_64 pos ms);
        pos <- (W64.of_int 0);
      } else {
        
      }
    }
    ms <- (init_msf);
    statep <- (protect_ptr statep ms);
    statep <- (BArray16.set64 statep 0 pos);
    return (sp_0, statep);
  }
  proc _sf_shake256_absorb_pre (sp_0:BArray200.t, statep:BArray16.t,
                                prep:BArray257.t, inlen:W64.t) : BArray200.t *
                                                                 BArray16.t = {
    var ms:W64.t;
    var pos:W64.t;
    var i:W64.t;
    var lane:W64.t;
    var b:W8.t;
    var t:W64.t;
    var shift:W8.t;
    ms <- (init_msf);
    statep <- (protect_ptr statep ms);
    sp_0 <- (protect_ptr sp_0 ms);
    prep <- (protect_ptr prep ms);
    pos <- (BArray16.get64 statep 0);
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    pos <- (protect_64 pos ms);
    inlen <- (protect_64 inlen ms);
    i <- (W64.of_int 0);
    while ((i \ult inlen)) {
      lane <- pos;
      lane <- (lane `>>` (W8.of_int 3));
      b <- (BArray257.get8 prep (W64.to_uint i));
      t <- (zeroextu64 b);
      shift <- (truncateu8 pos);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      i <- (i + (W64.of_int 1));
      pos <- (pos + (W64.of_int 1));
      if ((pos = (W64.of_int 136))) {
        (* Erased call to spill *)
        sp_0 <@ _keccakf1600 (sp_0);
        (* Erased call to unspill *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        ms <- (init_msf);
        statep <- (protect_ptr statep ms);
        sp_0 <- (protect_ptr sp_0 ms);
        prep <- (protect_ptr prep ms);
        inlen <- (protect_64 inlen ms);
        i <- (protect_64 i ms);
        pos <- (protect_64 pos ms);
        pos <- (W64.of_int 0);
      } else {
        
      }
    }
    ms <- (init_msf);
    statep <- (protect_ptr statep ms);
    statep <- (BArray16.set64 statep 0 pos);
    return (sp_0, statep);
  }
  proc _sf_shake256_finalize (sp_0:BArray200.t, statep:BArray16.t) : 
  BArray200.t = {
    var ms:W64.t;
    var pos:W64.t;
    var lane:W64.t;
    var shift:W8.t;
    var t:W64.t;
    ms <- (init_msf);
    statep <- (protect_ptr statep ms);
    sp_0 <- (protect_ptr sp_0 ms);
    pos <- (BArray16.get64 statep 0);
    (* Erased call to declassify *)
    pos <- (protect_64 pos ms);
    lane <- pos;
    lane <- (lane `>>` (W8.of_int 3));
    shift <- (truncateu8 pos);
    shift <- (shift `&` (W8.of_int 7));
    shift <- (shift `<<` (W8.of_int 3));
    t <- (W64.of_int 31);
    t <- (t `<<` (shift `&` (W8.of_int 63)));
    sp_0 <-
    (BArray200.set64 sp_0 (W64.to_uint lane)
    ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
    t <- (W64.of_int 1);
    t <- (t `<<` (W8.of_int 63));
    sp_0 <- (BArray200.set64 sp_0 16 ((BArray200.get64 sp_0 16) `^` t));
    return sp_0;
  }
  proc _sf_shake256_squeeze64 (outp:BArray64.t, sp_0:BArray200.t) : BArray64.t *
                                                                    BArray200.t = {
    var ms:W64.t;
    var i:W64.t;
    var lane:W64.t;
    var t:W64.t;
    ms <- (init_msf);
    outp <- (protect_ptr outp ms);
    sp_0 <- (protect_ptr sp_0 ms);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 64))) {
      lane <- i;
      lane <- (lane `>>` (W8.of_int 3));
      t <- (BArray200.get64 sp_0 (W64.to_uint lane));
      outp <- (BArray64.set64d outp (W64.to_uint i) t);
      i <- (i + (W64.of_int 8));
    }
    return (outp, sp_0);
  }
  proc _sf_mu_rawpre (mup:BArray64.t, skp:BArray2752.t, vkbytes:W64.t,
                      preaddr:W64.t, prelen:W64.t, maddr:W64.t, mlen:W64.t) : 
  BArray64.t = {
    var state:BArray200.t;
    var sp_0:BArray200.t;
    var st:BArray16.t;
    var stp:BArray16.t;
    var ms:W64.t;
    sp_0 <- witness;
    st <- witness;
    state <- witness;
    stp <- witness;
    (* Erased call to declassify *)
    sp_0 <- state;
    stp <- st;
    stp <- (BArray16.set64 stp 0 (W64.of_int 0));
    stp <- (BArray16.set64 stp 1 (W64.of_int 136));
    sp_0 <@ _keccak_init_state (sp_0);
    (* Erased call to spill *)
    (sp_0, stp) <@ _sf_shake256_absorb_sk (sp_0, stp, skp, vkbytes);
    (* Erased call to unspill *)
    (* Erased call to spill *)
    (sp_0, stp) <@ _sf_shake256_absorb_addr (sp_0, stp, preaddr, prelen);
    (* Erased call to unspill *)
    (* Erased call to spill *)
    (sp_0, stp) <@ _sf_shake256_absorb_addr (sp_0, stp, maddr, mlen);
    (* Erased call to unspill *)
    (* Erased call to spill *)
    sp_0 <@ _sf_shake256_finalize (sp_0, stp);
    (* Erased call to unspill *)
    (* Erased call to declassify *)
    (* Erased call to spill *)
    sp_0 <@ _keccakf1600 (sp_0);
    (* Erased call to unspill *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    mup <- (protect_ptr mup ms);
    (mup, sp_0) <@ _sf_shake256_squeeze64 (mup, sp_0);
    return mup;
  }
  proc _sf_mu_preptr (mup:BArray64.t, skp:BArray2752.t, vkbytes:W64.t,
                      prep:BArray257.t, prelen:W64.t, maddr:W64.t, mlen:W64.t) : 
  BArray64.t = {
    var state:BArray200.t;
    var sp_0:BArray200.t;
    var st:BArray16.t;
    var stp:BArray16.t;
    var ms:W64.t;
    sp_0 <- witness;
    st <- witness;
    state <- witness;
    stp <- witness;
    (* Erased call to declassify *)
    sp_0 <- state;
    stp <- st;
    stp <- (BArray16.set64 stp 0 (W64.of_int 0));
    stp <- (BArray16.set64 stp 1 (W64.of_int 136));
    sp_0 <@ _keccak_init_state (sp_0);
    (* Erased call to spill *)
    (sp_0, stp) <@ _sf_shake256_absorb_sk (sp_0, stp, skp, vkbytes);
    (* Erased call to unspill *)
    (* Erased call to spill *)
    (sp_0, stp) <@ _sf_shake256_absorb_pre (sp_0, stp, prep, prelen);
    (* Erased call to unspill *)
    (* Erased call to spill *)
    (sp_0, stp) <@ _sf_shake256_absorb_addr (sp_0, stp, maddr, mlen);
    (* Erased call to unspill *)
    (* Erased call to spill *)
    sp_0 <@ _sf_shake256_finalize (sp_0, stp);
    (* Erased call to unspill *)
    (* Erased call to declassify *)
    (* Erased call to spill *)
    sp_0 <@ _keccakf1600 (sp_0);
    (* Erased call to unspill *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    mup <- (protect_ptr mup ms);
    (mup, sp_0) <@ _sf_shake256_squeeze64 (mup, sp_0);
    return mup;
  }
  proc _sf_sign_expand_seedbuf (outp:BArray64.t, keyp:BArray32.t,
                                rndp:BArray32.t, mup:BArray64.t) : BArray64.t = {
    var s:BArray200.t;
    var sp_0:BArray200.t;
    var pos:W64.t;
    var b:W8.t;
    var lane:W64.t;
    var t:W64.t;
    var shift:W8.t;
    var idx:W64.t;
    var domain:W8.t;
    var rate:W64.t;
    s <- witness;
    sp_0 <- witness;
    sp_0 <- s;
    sp_0 <@ _keccak_init_state (sp_0);
    pos <- (W64.of_int 0);
    while ((pos \ult (W64.of_int 32))) {
      b <- (BArray32.get8 keyp (W64.to_uint pos));
      lane <- pos;
      lane <- (lane `>>` (W8.of_int 3));
      t <- (zeroextu64 b);
      shift <- (truncateu8 pos);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      pos <- (pos + (W64.of_int 1));
    }
    idx <- (W64.of_int 0);
    while ((idx \ult (W64.of_int 32))) {
      b <- (BArray32.get8 rndp (W64.to_uint idx));
      lane <- pos;
      lane <- (lane `>>` (W8.of_int 3));
      t <- (zeroextu64 b);
      shift <- (truncateu8 pos);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      pos <- (pos + (W64.of_int 1));
      idx <- (idx + (W64.of_int 1));
    }
    idx <- (W64.of_int 0);
    while ((idx \ult (W64.of_int 64))) {
      b <- (BArray64.get8 mup (W64.to_uint idx));
      lane <- pos;
      lane <- (lane `>>` (W8.of_int 3));
      t <- (zeroextu64 b);
      shift <- (truncateu8 pos);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      pos <- (pos + (W64.of_int 1));
      idx <- (idx + (W64.of_int 1));
    }
    domain <- (W8.of_int 31);
    rate <- (W64.of_int 136);
    sp_0 <@ _keccak_finalize (sp_0, pos, rate, domain);
    sp_0 <@ _keccakf1600 (sp_0);
    idx <- (W64.of_int 0);
    while ((idx \ult (W64.of_int 64))) {
      lane <- idx;
      lane <- (lane `>>` (W8.of_int 3));
      t <- (BArray200.get64 sp_0 (W64.to_uint lane));
      shift <- (truncateu8 idx);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `>>` (shift `&` (W8.of_int 63)));
      b <- (truncateu8 t);
      outp <- (BArray64.set8 outp (W64.to_uint idx) b);
      idx <- (idx + (W64.of_int 1));
    }
    return outp;
  }
  proc _sf_prepare_pre_raw (prep:BArray257.t, ctxaddr:W64.t, ctxlen:W64.t) : 
  BArray257.t = {
    var b:W8.t;
    var i:W64.t;
    var dst:W64.t;
    b <- (truncateu8 ctxlen);
    prep <- (BArray257.set8 prep 0 b);
    i <- (W64.of_int 0);
    while ((i \ult ctxlen)) {
      b <- (loadW8 Glob.mem (W64.to_uint ctxaddr));
      dst <- i;
      dst <- (dst + (W64.of_int 1));
      prep <- (BArray257.set8 prep (W64.to_uint dst) b);
      ctxaddr <- (ctxaddr + (W64.of_int 1));
      i <- (i + (W64.of_int 1));
    }
    return prep;
  }
  proc _sf_shake128_init_seed32 (sp_0:BArray200.t, seedp:BArray2752.t,
                                 nonce:W64.t) : BArray200.t = {
    var n:W64.t;
    var pos:W64.t;
    var lane:W64.t;
    var b:W8.t;
    var t:W64.t;
    var shift:W8.t;
    var k:int;
    sp_0 <@ _keccak_init_state (sp_0);
    n <- nonce;
    pos <- (W64.of_int 0);
    while ((pos \ult (W64.of_int 32))) {
      lane <- pos;
      lane <- (lane `>>` (W8.of_int 3));
      b <- (BArray2752.get8 seedp (W64.to_uint pos));
      t <- (zeroextu64 b);
      shift <- (truncateu8 pos);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      pos <- (pos + (W64.of_int 1));
    }
    k <- 0;
    while ((k < 2)) {
      lane <- pos;
      lane <- (lane `>>` (W8.of_int 3));
      b <- (truncateu8 n);
      t <- (zeroextu64 b);
      shift <- (truncateu8 pos);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      n <- (n `>>` (W8.of_int 8));
      pos <- (pos + (W64.of_int 1));
      k <- (k + 1);
    }
    t <- (W64.of_int 31);
    t <- (t `<<` (W8.of_int 16));
    sp_0 <- (BArray200.set64 sp_0 4 ((BArray200.get64 sp_0 4) `^` t));
    t <- (W64.of_int 1);
    t <- (t `<<` (W8.of_int 63));
    sp_0 <- (BArray200.set64 sp_0 20 ((BArray200.get64 sp_0 20) `^` t));
    return sp_0;
  }
  proc _sf_poly_uniform_at_seed32 (ap:BArray32768.t, base:W64.t,
                                   seedp:BArray2752.t, nonce:W64.t) : 
  BArray32768.t = {
    var state:BArray200.t;
    var sp_0:BArray200.t;
    var buf:BArray1024.t;
    var bufp:BArray1024.t;
    var off:W64.t;
    var ctr:W64.t;
    var buflen:W64.t;
    var ms:W64.t;
    var i:W64.t;
    var idx:W64.t;
    var b:W8.t;
    buf <- witness;
    bufp <- witness;
    sp_0 <- witness;
    state <- witness;
    sp_0 <- state;
    bufp <- buf;
    sp_0 <@ _sf_shake128_init_seed32 (sp_0, seedp, nonce);
    off <- (W64.of_int 0);
    (* Erased call to spill *)
    (bufp, sp_0) <@ __poly_sample_squeeze128 (bufp, off, sp_0);
    (* Erased call to declassify *)
    off <- (W64.of_int 168);
    (bufp, sp_0) <@ __poly_sample_squeeze128 (bufp, off, sp_0);
    (* Erased call to declassify *)
    off <- (W64.of_int 336);
    (bufp, sp_0) <@ __poly_sample_squeeze128 (bufp, off, sp_0);
    (* Erased call to declassify *)
    off <- (W64.of_int 504);
    (bufp, sp_0) <@ __poly_sample_squeeze128 (bufp, off, sp_0);
    (* Erased call to declassify *)
    (* Erased call to unspill *)
    ctr <- (W64.of_int 0);
    buflen <- (W64.of_int 672);
    (ap, ctr) <@ __poly_uniform_consume (ap, base, ctr, bufp, buflen);
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    ap <- (protect_ptr ap ms);
    bufp <- (protect_ptr bufp ms);
    base <- (protect_64 base ms);
    ctr <- (protect_64 ctr ms);
    while ((ctr \ult (W64.of_int 256))) {
      off <- buflen;
      off <- (off `&` (W64.of_int 1));
      i <- (W64.of_int 0);
      while ((i \ult off)) {
        idx <- buflen;
        idx <- (idx - off);
        idx <- (idx + i);
        b <- (BArray1024.get8 bufp (W64.to_uint idx));
        bufp <- (BArray1024.set8 bufp (W64.to_uint i) b);
        i <- (i + (W64.of_int 1));
      }
      (* Erased call to spill *)
      (bufp, sp_0) <@ __poly_sample_squeeze128 (bufp, off, sp_0);
      (* Erased call to declassify *)
      (* Erased call to unspill *)
      buflen <- (W64.of_int 168);
      buflen <- (buflen + off);
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      ms <- (init_msf);
      ap <- (protect_ptr ap ms);
      bufp <- (protect_ptr bufp ms);
      base <- (protect_64 base ms);
      ctr <- (protect_64 ctr ms);
      buflen <- (protect_64 buflen ms);
      (ap, ctr) <@ __poly_uniform_consume (ap, base, ctr, bufp, buflen);
      (* Erased call to declassify *)
      ms <- (init_msf);
      ap <- (protect_ptr ap ms);
      bufp <- (protect_ptr bufp ms);
      ctr <- (protect_64 ctr ms);
    }
    return ap;
  }
  proc _sf_polymatkl_expand_with_vecA_seed32 (matp:BArray32768.t,
                                              seedp:BArray2752.t, rows:W64.t,
                                              cols:W64.t, m:W64.t) : 
  BArray32768.t = {
    var i:W64.t;
    var base:W64.t;
    var nonce:W64.t;
    var ms:W64.t;
    var j:W64.t;
    i <- (W64.of_int 0);
    base <- (W64.of_int 0);
    while ((i \ult rows)) {
      nonce <- rows;
      nonce <- (nonce `<<` (W8.of_int 8));
      nonce <- (nonce + m);
      nonce <- (nonce + i);
      (* Erased call to spill *)
      matp <@ _sf_poly_uniform_at_seed32 (matp, base, seedp, nonce);
      (* Erased call to unspill *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      ms <- (init_msf);
      matp <- (protect_ptr matp ms);
      seedp <- (protect_ptr seedp ms);
      rows <- (protect_64 rows ms);
      cols <- (protect_64 cols ms);
      m <- (protect_64 m ms);
      i <- (protect_64 i ms);
      base <- (protect_64 base ms);
      base <- (base + (W64.of_int 256));
      j <- (W64.of_int 0);
      while ((j \ult m)) {
        nonce <- i;
        nonce <- (nonce `<<` (W8.of_int 8));
        nonce <- (nonce + j);
        (* Erased call to spill *)
        matp <@ _sf_poly_uniform_at_seed32 (matp, base, seedp, nonce);
        (* Erased call to unspill *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        ms <- (init_msf);
        matp <- (protect_ptr matp ms);
        seedp <- (protect_ptr seedp ms);
        rows <- (protect_64 rows ms);
        cols <- (protect_64 cols ms);
        m <- (protect_64 m ms);
        i <- (protect_64 i ms);
        j <- (protect_64 j ms);
        base <- (protect_64 base ms);
        j <- (j + (W64.of_int 1));
        base <- (base + (W64.of_int 256));
      }
      i <- (i + (W64.of_int 1));
    }
    return matp;
  }
  proc _sf_polymatkl_expand_seed32 (matp:BArray32768.t, seedp:BArray2752.t,
                                    rows:W64.t, cols:W64.t) : BArray32768.t = {
    var m:W64.t;
    var i:W64.t;
    var rowbase:W64.t;
    var j:W64.t;
    var nonce:W64.t;
    var base:W64.t;
    var ms:W64.t;
    m <- cols;
    m <- (m - (W64.of_int 1));
    i <- (W64.of_int 0);
    rowbase <- (W64.of_int 0);
    while ((i \ult rows)) {
      j <- (W64.of_int 0);
      while ((j \ult m)) {
        nonce <- i;
        nonce <- (nonce `<<` (W8.of_int 8));
        nonce <- (nonce + j);
        base <- rowbase;
        base <- (base + j);
        base <- (base + (W64.of_int 1));
        base <- (base * (W64.of_int 256));
        (* Erased call to spill *)
        matp <@ _sf_poly_uniform_at_seed32 (matp, base, seedp, nonce);
        (* Erased call to unspill *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        ms <- (init_msf);
        matp <- (protect_ptr matp ms);
        seedp <- (protect_ptr seedp ms);
        rows <- (protect_64 rows ms);
        cols <- (protect_64 cols ms);
        m <- (protect_64 m ms);
        i <- (protect_64 i ms);
        j <- (protect_64 j ms);
        rowbase <- (protect_64 rowbase ms);
        j <- (j + (W64.of_int 1));
      }
      rowbase <- (rowbase + cols);
      i <- (i + (W64.of_int 1));
    }
    return matp;
  }
  proc _sf_unpack_sk_mode2 (matp:BArray32768.t, s1p:BArray8192.t,
                            s2p:BArray8192.t, keyp:BArray32.t,
                            skp:BArray2752.t) : BArray32768.t *
                                                BArray8192.t * BArray8192.t *
                                                BArray32.t = {
    var kr:W64.t;
    var lr:W64.t;
    var mr:W64.t;
    var vkbr:W64.t;
    var b:BArray8192.t;
    var bp:BArray8192.t;
    var count:W64.t;
    var ms:W64.t;
    b <- witness;
    bp <- witness;
    kr <- (W64.of_int 2);
    lr <- (W64.of_int 4);
    mr <- (W64.of_int 3);
    vkbr <- (W64.of_int 992);
    bp <- b;
    bp <@ __unpack_vk_m23_coeffs (bp, skp, kr);
    (* Erased call to spill *)
    matp <@ _sf_polymatkl_expand_with_vecA_seed32 (matp, skp, kr, lr, mr);
    (* Erased call to unspill *)
    bp <- b;
    matp <@ _polymatkl_double (matp, kr, lr);
    count <- kr;
    count <- (count * (W64.of_int 256));
    bp <@ _polyvec_double (bp, count);
    bp <@ __polyvec_sub_left_inplace (bp, matp, lr, kr);
    bp <@ _polyvec_double (bp, count);
    (* Erased call to spill *)
    bp <@ _polyvec_ntt (bp, kr);
    (* Erased call to unspill *)
    ms <- (init_msf);
    matp <- (protect_ptr matp ms);
    bp <- (protect_ptr bp ms);
    kr <- (protect_64 kr ms);
    lr <- (protect_64 lr ms);
    matp <@ _polymat_set_first_column (matp, bp, kr, lr);
    (s1p, s2p, keyp) <@ _unpack_sk_m23 (s1p, s2p, keyp, skp, vkbr, mr, kr);
    return (matp, s1p, s2p, keyp);
  }
  proc _sf_unpack_sk_mode3 (matp:BArray32768.t, s1p:BArray8192.t,
                            s2p:BArray8192.t, keyp:BArray32.t,
                            skp:BArray2752.t) : BArray32768.t *
                                                BArray8192.t * BArray8192.t *
                                                BArray32.t = {
    var kr:W64.t;
    var lr:W64.t;
    var mr:W64.t;
    var vkbr:W64.t;
    var b:BArray8192.t;
    var bp:BArray8192.t;
    var count:W64.t;
    var ms:W64.t;
    b <- witness;
    bp <- witness;
    kr <- (W64.of_int 3);
    lr <- (W64.of_int 6);
    mr <- (W64.of_int 5);
    vkbr <- (W64.of_int 1472);
    bp <- b;
    bp <@ __unpack_vk_m23_coeffs (bp, skp, kr);
    (* Erased call to spill *)
    matp <@ _sf_polymatkl_expand_with_vecA_seed32 (matp, skp, kr, lr, mr);
    (* Erased call to unspill *)
    bp <- b;
    matp <@ _polymatkl_double (matp, kr, lr);
    count <- kr;
    count <- (count * (W64.of_int 256));
    bp <@ _polyvec_double (bp, count);
    bp <@ __polyvec_sub_left_inplace (bp, matp, lr, kr);
    bp <@ _polyvec_double (bp, count);
    (* Erased call to spill *)
    bp <@ _polyvec_ntt (bp, kr);
    (* Erased call to unspill *)
    ms <- (init_msf);
    matp <- (protect_ptr matp ms);
    bp <- (protect_ptr bp ms);
    kr <- (protect_64 kr ms);
    lr <- (protect_64 lr ms);
    matp <@ _polymat_set_first_column (matp, bp, kr, lr);
    (s1p, s2p, keyp) <@ _unpack_sk_m23 (s1p, s2p, keyp, skp, vkbr, mr, kr);
    return (matp, s1p, s2p, keyp);
  }
  proc _sf_unpack_sk_mode5 (matp:BArray32768.t, s1p:BArray8192.t,
                            s2p:BArray8192.t, keyp:BArray32.t,
                            skp:BArray2752.t) : BArray32768.t *
                                                BArray8192.t * BArray8192.t *
                                                BArray32.t = {
    var kr:W64.t;
    var lr:W64.t;
    var mr:W64.t;
    var vkbr:W64.t;
    var b:BArray8192.t;
    var bp:BArray8192.t;
    var ms:W64.t;
    b <- witness;
    bp <- witness;
    kr <- (W64.of_int 4);
    lr <- (W64.of_int 7);
    mr <- (W64.of_int 6);
    vkbr <- (W64.of_int 2080);
    bp <- b;
    bp <@ __unpack_vk_m5_coeffs (bp, skp, kr);
    (* Erased call to spill *)
    matp <@ _sf_polymatkl_expand_seed32 (matp, skp, kr, lr);
    (* Erased call to unspill *)
    bp <- b;
    matp <@ _polymatkl_double (matp, kr, lr);
    ms <- (init_msf);
    matp <- (protect_ptr matp ms);
    bp <- (protect_ptr bp ms);
    kr <- (protect_64 kr ms);
    lr <- (protect_64 lr ms);
    matp <@ _polymat_set_first_column (matp, bp, kr, lr);
    (s1p, s2p, keyp) <@ _unpack_sk_m5 (s1p, s2p, keyp, skp, vkbr, mr, kr);
    return (matp, s1p, s2p, keyp);
  }
  proc _sf_shake256_init_seed64 (sp_0:BArray200.t, seedp:BArray64.t,
                                 nonce:W64.t) : BArray200.t = {
    var n:W64.t;
    var pos:W64.t;
    var lane:W64.t;
    var b:W8.t;
    var t:W64.t;
    var shift:W8.t;
    var k:int;
    sp_0 <@ _keccak_init_state (sp_0);
    n <- nonce;
    pos <- (W64.of_int 0);
    while ((pos \ult (W64.of_int 64))) {
      lane <- pos;
      lane <- (lane `>>` (W8.of_int 3));
      b <- (BArray64.get8 seedp (W64.to_uint pos));
      t <- (zeroextu64 b);
      shift <- (truncateu8 pos);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      pos <- (pos + (W64.of_int 1));
    }
    k <- 0;
    while ((k < 2)) {
      lane <- pos;
      lane <- (lane `>>` (W8.of_int 3));
      b <- (truncateu8 n);
      t <- (zeroextu64 b);
      shift <- (truncateu8 pos);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      n <- (n `>>` (W8.of_int 8));
      pos <- (pos + (W64.of_int 1));
      k <- (k + 1);
    }
    t <- (W64.of_int 31);
    t <- (t `<<` (W8.of_int 16));
    sp_0 <- (BArray200.set64 sp_0 8 ((BArray200.get64 sp_0 8) `^` t));
    t <- (W64.of_int 1);
    t <- (t `<<` (W8.of_int 63));
    sp_0 <- (BArray200.set64 sp_0 16 ((BArray200.get64 sp_0 16) `^` t));
    return sp_0;
  }
  proc _sf_sample_gauss_N_full_at (rp:BArray32768.t, signsp:BArray512.t,
                                   sqsump:BArray16.t, seedp:BArray64.t,
                                   nonce:W64.t, len:W64.t, sampleoff:W64.t,
                                   signoff:W64.t) : BArray32768.t *
                                                    BArray512.t * BArray16.t = {
    var state:BArray200.t;
    var sp_0:BArray200.t;
    var buf:BArray8192.t;
    var bufp:BArray8192.t;
    var coefcnt_buf:BArray8.t;
    var coefcntp:BArray8.t;
    var block:W64.t;
    var off:W64.t;
    var ms:W64.t;
    var signbytes:W64.t;
    var bytecnt:W64.t;
    var counts:W64.t;
    var dont:W64.t;
    var bufoff:W64.t;
    var outoff:W64.t;
    var got:W64.t;
    var total:W64.t;
    var firstflag:W64.t;
    var remaining:W64.t;
    buf <- witness;
    bufp <- witness;
    coefcnt_buf <- witness;
    coefcntp <- witness;
    sp_0 <- witness;
    state <- witness;
    sp_0 <- state;
    bufp <- buf;
    coefcntp <- coefcnt_buf;
    sp_0 <@ _sf_shake256_init_seed64 (sp_0, seedp, nonce);
    block <- (W64.of_int 0);
    off <- (W64.of_int 0);
    while ((block \ult (W64.of_int 49))) {
      (* Erased call to spill *)
      (bufp, sp_0) <@ __sample_full_squeeze256 (bufp, off, sp_0);
      (* Erased call to declassify *)
      (* Erased call to unspill *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      ms <- (init_msf);
      bufp <- (protect_ptr bufp ms);
      sp_0 <- (protect_ptr sp_0 ms);
      rp <- (protect_ptr rp ms);
      signsp <- (protect_ptr signsp ms);
      sqsump <- (protect_ptr sqsump ms);
      block <- (protect_64 block ms);
      off <- (protect_64 off ms);
      len <- (protect_64 len ms);
      sampleoff <- (protect_64 sampleoff ms);
      signoff <- (protect_64 signoff ms);
      off <- (off + (W64.of_int 136));
      block <- (block + (W64.of_int 1));
    }
    signbytes <- len;
    signbytes <- (signbytes `>>` (W8.of_int 3));
    signsp <@ __sample_gauss_N_copy_signs_at (signsp, bufp, signbytes,
    signoff);
    bytecnt <- (W64.of_int 6664);
    bytecnt <- (bytecnt - signbytes);
    counts <- bytecnt;
    counts <- (counts `<<` (W8.of_int 32));
    counts <- (counts `|` len);
    dont <- len;
    while (((W64.of_int 256) \ule dont)) {
      dont <- (dont - (W64.of_int 256));
    }
    bufoff <- signbytes;
    outoff <- sampleoff;
    (* Erased call to spill *)
    (rp, sqsump, coefcntp) <@ __sample_gauss_at (rp, sqsump, coefcntp, 
    bufp, counts, dont, bufoff, outoff);
    (* Erased call to unspill *)
    ms <- (init_msf);
    rp <- (protect_ptr rp ms);
    signsp <- (protect_ptr signsp ms);
    sqsump <- (protect_ptr sqsump ms);
    coefcntp <- (protect_ptr coefcntp ms);
    sp_0 <- (protect_ptr sp_0 ms);
    len <- (protect_64 len ms);
    bytecnt <- (protect_64 bytecnt ms);
    signbytes <- (protect_64 signbytes ms);
    dont <- (protect_64 dont ms);
    sampleoff <- (protect_64 sampleoff ms);
    signoff <- (protect_64 signoff ms);
    got <- (BArray8.get64 coefcntp 0);
    (* Erased call to declassify *)
    got <- (protect_64 got ms);
    total <- got;
    firstflag <- (W64.of_int 1);
    while ((total \ult len)) {
      off <- bytecnt;
      while (((W64.of_int 26) \ule off)) {
        off <- (off - (W64.of_int 26));
      }
      bufp <@ _sample_gauss_N_carry (bufp, bytecnt, signbytes, firstflag,
      off);
      (* Erased call to spill *)
      (bufp, sp_0) <@ __sample_full_squeeze256 (bufp, off, sp_0);
      (* Erased call to declassify *)
      (* Erased call to unspill *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      ms <- (init_msf);
      bufp <- (protect_ptr bufp ms);
      sp_0 <- (protect_ptr sp_0 ms);
      rp <- (protect_ptr rp ms);
      signsp <- (protect_ptr signsp ms);
      sqsump <- (protect_ptr sqsump ms);
      bytecnt <- (protect_64 bytecnt ms);
      signbytes <- (protect_64 signbytes ms);
      firstflag <- (protect_64 firstflag ms);
      len <- (protect_64 len ms);
      total <- (protect_64 total ms);
      dont <- (protect_64 dont ms);
      off <- (protect_64 off ms);
      sampleoff <- (protect_64 sampleoff ms);
      signoff <- (protect_64 signoff ms);
      bytecnt <- (W64.of_int 136);
      bytecnt <- (bytecnt + off);
      remaining <- len;
      remaining <- (remaining - total);
      counts <- bytecnt;
      counts <- (counts `<<` (W8.of_int 32));
      counts <- (counts `|` remaining);
      bufoff <- (W64.of_int 0);
      outoff <- sampleoff;
      outoff <- (outoff + total);
      (* Erased call to spill *)
      (rp, sqsump, coefcntp) <@ __sample_gauss_at (rp, sqsump, coefcntp,
      bufp, counts, dont, bufoff, outoff);
      (* Erased call to unspill *)
      ms <- (init_msf);
      rp <- (protect_ptr rp ms);
      signsp <- (protect_ptr signsp ms);
      sqsump <- (protect_ptr sqsump ms);
      coefcntp <- (protect_ptr coefcntp ms);
      sp_0 <- (protect_ptr sp_0 ms);
      len <- (protect_64 len ms);
      bytecnt <- (protect_64 bytecnt ms);
      signbytes <- (protect_64 signbytes ms);
      firstflag <- (protect_64 firstflag ms);
      total <- (protect_64 total ms);
      dont <- (protect_64 dont ms);
      sampleoff <- (protect_64 sampleoff ms);
      signoff <- (protect_64 signoff ms);
      got <- (BArray8.get64 coefcntp 0);
      (* Erased call to declassify *)
      got <- (protect_64 got ms);
      total <- (total + got);
      firstflag <- (W64.of_int 0);
    }
    return (rp, signsp, sqsump);
  }
  proc _sf_hyperball_b_raw (bp:BArray1.t, seedp:BArray64.t, nonce:W64.t) : 
  BArray1.t = {
    var s:BArray200.t;
    var sp_0:BArray200.t;
    var i:W64.t;
    var b:W8.t;
    var t:W64.t;
    var lane:W64.t;
    var shift:W8.t;
    s <- witness;
    sp_0 <- witness;
    sp_0 <- s;
    sp_0 <@ _keccak_init_state (sp_0);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 64))) {
      b <- (BArray64.get8 seedp (W64.to_uint i));
      t <- (zeroextu64 b);
      lane <- i;
      lane <- (lane `>>` (W8.of_int 3));
      shift <- (truncateu8 i);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      i <- (i + (W64.of_int 1));
    }
    b <- (truncateu8 nonce);
    t <- (zeroextu64 b);
    sp_0 <- (BArray200.set64 sp_0 8 ((BArray200.get64 sp_0 8) `^` t));
    nonce <- (nonce `>>` (W8.of_int 8));
    b <- (truncateu8 nonce);
    t <- (zeroextu64 b);
    t <- (t `<<` (W8.of_int 8));
    sp_0 <- (BArray200.set64 sp_0 8 ((BArray200.get64 sp_0 8) `^` t));
    t <- (W64.of_int 31);
    t <- (t `<<` (W8.of_int 16));
    sp_0 <- (BArray200.set64 sp_0 8 ((BArray200.get64 sp_0 8) `^` t));
    t <- (W64.of_int 1);
    t <- (t `<<` (W8.of_int 63));
    sp_0 <- (BArray200.set64 sp_0 16 ((BArray200.get64 sp_0 16) `^` t));
    sp_0 <@ _keccakf1600 (sp_0);
    t <- (BArray200.get64 sp_0 0);
    b <- (truncateu8 t);
    bp <- (BArray1.set8 bp 0 b);
    return bp;
  }
  proc _sf_scale_and_check (y1p:BArray8192.t, y2p:BArray8192.t,
                            samplesp:BArray32768.t, signsp:BArray512.t,
                            scalep:BArray16.t, lcount:W64.t, total:W64.t,
                            bound:W64.t) : BArray8192.t * BArray8192.t *
                                           W64.t = {
    var accepted:W64.t;
    var ms:W64.t;
    var counts:W64.t;
    var kcount:W64.t;
    var norm:W64.t;
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    lcount <- (protect_64 lcount ms);
    total <- (protect_64 total ms);
    bound <- (protect_64 bound ms);
    counts <- total;
    counts <- (counts `<<` (W8.of_int 32));
    counts <- (counts `|` lcount);
    (y1p, y2p) <@ _polyfixveclk_scale_samples (y1p, y2p, samplesp, signsp,
    scalep, counts);
    kcount <- total;
    kcount <- (kcount - lcount);
    norm <@ _polyfixveclk_sqnorm2_2048 (y1p, lcount, y2p, kcount);
    (* Erased call to declassify *)
    ms <- (init_msf);
    norm <- (protect_64 norm ms);
    bound <- (protect_64 bound ms);
    accepted <- (W64.of_int 0);
    if ((norm \ule bound)) {
      accepted <- (W64.of_int 1);
    } else {
      
    }
    return (y1p, y2p, accepted);
  }
  proc _sf_hyperball_full (y1p:BArray8192.t, y2p:BArray8192.t, bp:BArray1.t,
                           counterp:BArray8.t, seedp:BArray64.t,
                           lcount:W64.t, kcount:W64.t, scale_const:W64.t,
                           bound_const:W64.t, cube0:W64.t, cube1:W64.t,
                           three0:W64.t, three1:W64.t) : BArray8192.t *
                                                         BArray8192.t *
                                                         BArray1.t *
                                                         BArray8.t = {
    var samples:BArray32768.t;
    var samplesp:BArray32768.t;
    var signs:BArray512.t;
    var signsp:BArray512.t;
    var sqsum:BArray16.t;
    var sqsump:BArray16.t;
    var invsqrt:BArray16.t;
    var invsqrtp:BArray16.t;
    var start_cube:BArray16.t;
    var cubep:BArray16.t;
    var start_three:BArray16.t;
    var threep:BArray16.t;
    var ni:W64.t;
    var accepted:W64.t;
    var len:W64.t;
    var sampleoff:W64.t;
    var signoff:W64.t;
    var total:W64.t;
    var idx:W64.t;
    var scale:W64.t;
    var lcoeffs:W64.t;
    var tcoeffs:W64.t;
    var ms:W64.t;
    cubep <- witness;
    invsqrt <- witness;
    invsqrtp <- witness;
    samples <- witness;
    samplesp <- witness;
    signs <- witness;
    signsp <- witness;
    sqsum <- witness;
    sqsump <- witness;
    start_cube <- witness;
    start_three <- witness;
    threep <- witness;
    samplesp <- samples;
    signsp <- signs;
    sqsump <- sqsum;
    invsqrtp <- invsqrt;
    cubep <- start_cube;
    threep <- start_three;
    cubep <- (BArray16.set64 cubep 0 cube0);
    cubep <- (BArray16.set64 cubep 1 cube1);
    threep <- (BArray16.set64 threep 0 three0);
    threep <- (BArray16.set64 threep 1 three1);
    ni <- (BArray8.get64 counterp 0);
    (* Erased call to spill *)
    accepted <- (W64.of_int 0);
    while ((accepted = (W64.of_int 0))) {
      sqsump <- (BArray16.set64 sqsump 0 (W64.of_int 0));
      sqsump <- (BArray16.set64 sqsump 1 (W64.of_int 0));
      len <- (W64.of_int 256);
      len <- (len + (W64.of_int 1));
      sampleoff <- (W64.of_int 0);
      signoff <- (W64.of_int 0);
      (samplesp, signsp, sqsump) <@ _sf_sample_gauss_N_full_at (samplesp,
      signsp, sqsump, seedp, ni, len, sampleoff, signoff);
      ni <- (ni + (W64.of_int 1));
      sampleoff <- (W64.of_int 256);
      signoff <- (W64.of_int 32);
      (samplesp, signsp, sqsump) <@ _sf_sample_gauss_N_full_at (samplesp,
      signsp, sqsump, seedp, ni, len, sampleoff, signoff);
      ni <- (ni + (W64.of_int 1));
      total <- lcount;
      total <- (total + kcount);
      idx <- (W64.of_int 2);
      while ((idx \ult total)) {
        len <- (W64.of_int 256);
        sampleoff <- idx;
        sampleoff <- (sampleoff * (W64.of_int 256));
        signoff <- idx;
        signoff <- (signoff * (W64.of_int 32));
        (samplesp, signsp, sqsump) <@ _sf_sample_gauss_N_full_at (samplesp,
        signsp, sqsump, seedp, ni, len, sampleoff, signoff);
        ni <- (ni + (W64.of_int 1));
        idx <- (idx + (W64.of_int 1));
      }
      sqsump <@ _fixpoint_half_round (sqsump);
      invsqrtp <@ _fixpoint_newton_invsqrt (invsqrtp, sqsump, cubep, threep);
      scale <- scale_const;
      sqsump <@ _fixpoint_mul_high (sqsump, invsqrtp, scale);
      lcoeffs <- lcount;
      lcoeffs <- (lcoeffs `<<` (W8.of_int 8));
      tcoeffs <- total;
      tcoeffs <- (tcoeffs `<<` (W8.of_int 8));
      (y1p, y2p, accepted) <@ _sf_scale_and_check (y1p, y2p, samplesp,
      signsp, sqsump, lcoeffs, tcoeffs, bound_const);
    }
    bp <@ _sf_hyperball_b_raw (bp, seedp, ni);
    (* Erased call to unspill *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    counterp <- (protect_ptr counterp ms);
    counterp <- (BArray8.set64 counterp 0 ni);
    return (y1p, y2p, bp, counterp);
  }
  proc _sf_hyperball_mode2 (y1p:BArray8192.t, y2p:BArray8192.t, bp:BArray1.t,
                            counterp:BArray8.t, seedp:BArray64.t) : BArray8192.t *
                                                                    BArray8192.t *
                                                                    BArray1.t *
                                                                    BArray8.t = {
    var lcount:W64.t;
    var kcount:W64.t;
    var scale:W64.t;
    var bound:W64.t;
    var cube0:W64.t;
    var cube1:W64.t;
    var three0:W64.t;
    var three1:W64.t;
    var ms:W64.t;
    lcount <- (W64.of_int 4);
    kcount <- (W64.of_int 2);
    scale <- (W64.of_int 2643021496320);
    bound <- (W64.of_int 6505809026482176);
    cube0 <- (W64.of_int 130843895063578);
    cube1 <- (W64.of_int 4450);
    three0 <- (W64.of_int 115690877850491);
    three1 <- (W64.of_int 10267222);
    ms <- (init_msf);
    y1p <- (protect_ptr y1p ms);
    y2p <- (protect_ptr y2p ms);
    bp <- (protect_ptr bp ms);
    counterp <- (protect_ptr counterp ms);
    seedp <- (protect_ptr seedp ms);
    lcount <- (protect_64 lcount ms);
    kcount <- (protect_64 kcount ms);
    scale <- (protect_64 scale ms);
    bound <- (protect_64 bound ms);
    cube0 <- (protect_64 cube0 ms);
    cube1 <- (protect_64 cube1 ms);
    three0 <- (protect_64 three0 ms);
    three1 <- (protect_64 three1 ms);
    (y1p, y2p, bp, counterp) <@ _sf_hyperball_full (y1p, y2p, bp, counterp,
    seedp, lcount, kcount, scale, bound, cube0, cube1, three0, three1);
    return (y1p, y2p, bp, counterp);
  }
  proc _sf_hyperball_mode3 (y1p:BArray8192.t, y2p:BArray8192.t, bp:BArray1.t,
                            counterp:BArray8.t, seedp:BArray64.t) : BArray8192.t *
                                                                    BArray8192.t *
                                                                    BArray1.t *
                                                                    BArray8.t = {
    var lcount:W64.t;
    var kcount:W64.t;
    var scale:W64.t;
    var bound:W64.t;
    var cube0:W64.t;
    var cube1:W64.t;
    var three0:W64.t;
    var three1:W64.t;
    var ms:W64.t;
    lcount <- (W64.of_int 6);
    kcount <- (W64.of_int 3);
    scale <- (W64.of_int 4916390789120);
    bound <- (W64.of_int 22510896139993088);
    cube0 <- (W64.of_int 28764298784360);
    cube1 <- (W64.of_int 2424);
    three0 <- (W64.of_int 135042716239155);
    three1 <- (W64.of_int 8384969);
    ms <- (init_msf);
    y1p <- (protect_ptr y1p ms);
    y2p <- (protect_ptr y2p ms);
    bp <- (protect_ptr bp ms);
    counterp <- (protect_ptr counterp ms);
    seedp <- (protect_ptr seedp ms);
    lcount <- (protect_64 lcount ms);
    kcount <- (protect_64 kcount ms);
    scale <- (protect_64 scale ms);
    bound <- (protect_64 bound ms);
    cube0 <- (protect_64 cube0 ms);
    cube1 <- (protect_64 cube1 ms);
    three0 <- (protect_64 three0 ms);
    three1 <- (protect_64 three1 ms);
    (y1p, y2p, bp, counterp) <@ _sf_hyperball_full (y1p, y2p, bp, counterp,
    seedp, lcount, kcount, scale, bound, cube0, cube1, three0, three1);
    return (y1p, y2p, bp, counterp);
  }
  proc _sf_hyperball_mode5 (y1p:BArray8192.t, y2p:BArray8192.t, bp:BArray1.t,
                            counterp:BArray8.t, seedp:BArray64.t) : BArray8192.t *
                                                                    BArray8192.t *
                                                                    BArray1.t *
                                                                    BArray8.t = {
    var lcount:W64.t;
    var kcount:W64.t;
    var scale:W64.t;
    var bound:W64.t;
    var cube0:W64.t;
    var cube1:W64.t;
    var three0:W64.t;
    var three1:W64.t;
    var ms:W64.t;
    lcount <- (W64.of_int 7);
    kcount <- (W64.of_int 4);
    scale <- (W64.of_int 5997831421952);
    bound <- (W64.of_int 33503371683954688);
    cube0 <- (W64.of_int 123213818923277);
    cube1 <- (W64.of_int 1794);
    three0 <- (W64.of_int 96105673977137);
    three1 <- (W64.of_int 7585088);
    ms <- (init_msf);
    y1p <- (protect_ptr y1p ms);
    y2p <- (protect_ptr y2p ms);
    bp <- (protect_ptr bp ms);
    counterp <- (protect_ptr counterp ms);
    seedp <- (protect_ptr seedp ms);
    lcount <- (protect_64 lcount ms);
    kcount <- (protect_64 kcount ms);
    scale <- (protect_64 scale ms);
    bound <- (protect_64 bound ms);
    cube0 <- (protect_64 cube0 ms);
    cube1 <- (protect_64 cube1 ms);
    three0 <- (protect_64 three0 ms);
    three1 <- (protect_64 three1 ms);
    (y1p, y2p, bp, counterp) <@ _sf_hyperball_full (y1p, y2p, bp, counterp,
    seedp, lcount, kcount, scale, bound, cube0, cube1, three0, three1);
    return (y1p, y2p, bp, counterp);
  }
  proc _sf_round_lk_copy0 (z1p:BArray8192.t, z2p:BArray8192.t,
                           z10p:BArray1024.t, y1p:BArray8192.t,
                           y2p:BArray8192.t, lcount:W64.t, kcount:W64.t) : 
  BArray8192.t * BArray8192.t * BArray1024.t = {
    var i:W64.t;
    var a:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult lcount)) {
      a <- (BArray8192.get32 y1p (W64.to_uint i));
      a <- (a + (W32.of_int 4096));
      a <- (a `|>>` (W8.of_int 13));
      z1p <- (BArray8192.set32 z1p (W64.to_uint i) a);
      if ((i \ult (W64.of_int 256))) {
        z10p <- (BArray1024.set32 z10p (W64.to_uint i) a);
      } else {
        
      }
      i <- (i + (W64.of_int 1));
    }
    i <- (W64.of_int 0);
    while ((i \ult kcount)) {
      a <- (BArray8192.get32 y2p (W64.to_uint i));
      a <- (a + (W32.of_int 4096));
      a <- (a `|>>` (W8.of_int 13));
      z2p <- (BArray8192.set32 z2p (W64.to_uint i) a);
      i <- (i + (W64.of_int 1));
    }
    return (z1p, z2p, z10p);
  }
  proc _sf_round_lk (z1p:BArray8192.t, z2p:BArray8192.t, y1p:BArray8192.t,
                     y2p:BArray8192.t, lcount:W64.t, kcount:W64.t) : 
  BArray8192.t * BArray8192.t = {
    var i:W64.t;
    var a:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult lcount)) {
      a <- (BArray8192.get32 y1p (W64.to_uint i));
      a <- (a + (W32.of_int 4096));
      a <- (a `|>>` (W8.of_int 13));
      z1p <- (BArray8192.set32 z1p (W64.to_uint i) a);
      i <- (i + (W64.of_int 1));
    }
    i <- (W64.of_int 0);
    while ((i \ult kcount)) {
      a <- (BArray8192.get32 y2p (W64.to_uint i));
      a <- (a + (W32.of_int 4096));
      a <- (a `|>>` (W8.of_int 13));
      z2p <- (BArray8192.set32 z2p (W64.to_uint i) a);
      i <- (i + (W64.of_int 1));
    }
    return (z1p, z2p);
  }
  proc _sf_polyveck_poly_fromcrt_inplace (wp_0:BArray8192.t, vp:BArray1024.t,
                                          count:W64.t) : BArray8192.t = {
    var j:W64.t;
    var xq:W32.t;
    var x2:W32.t;
    var mask:W32.t;
    var add:W32.t;
    var r:W32.t;
    var k:W64.t;
    var off:W64.t;
    var idx:W64.t;
    j <- (W64.of_int 0);
    while ((j \ult (W64.of_int 256))) {
      xq <- (BArray8192.get32 wp_0 (W64.to_uint j));
      x2 <- (BArray1024.get32 vp (W64.to_uint j));
      mask <- xq;
      mask <- (mask `^` x2);
      mask <- (mask `&` (W32.of_int 1));
      add <- (W32.of_int 0);
      add <- (add - mask);
      add <- (add `&` (W32.of_int 64513));
      r <- (xq + add);
      wp_0 <- (BArray8192.set32 wp_0 (W64.to_uint j) r);
      j <- (j + (W64.of_int 1));
    }
    k <- (W64.of_int 1);
    off <- (W64.of_int 256);
    while ((k \ult count)) {
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int 256))) {
        idx <- off;
        idx <- (idx + j);
        xq <- (BArray8192.get32 wp_0 (W64.to_uint idx));
        mask <- xq;
        mask <- (mask `&` (W32.of_int 1));
        add <- (W32.of_int 0);
        add <- (add - mask);
        add <- (add `&` (W32.of_int 64513));
        r <- (xq + add);
        wp_0 <- (BArray8192.set32 wp_0 (W64.to_uint idx) r);
        j <- (j + (W64.of_int 1));
      }
      off <- (off + (W64.of_int 256));
      k <- (k + (W64.of_int 1));
    }
    return wp_0;
  }
  proc __sign_challenge_zero_highbuf (bp:BArray1152.t, len:W64.t) : BArray1152.t = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult len)) {
      bp <- (BArray1152.set8 bp (W64.to_uint i) (W8.of_int 0));
      i <- (i + (W64.of_int 1));
    }
    return bp;
  }
  proc __sign_challenge_shake256_absorb_buf (sp_0:BArray200.t,
                                             statep:BArray16.t,
                                             inp:BArray1152.t, inlen:W64.t) : 
  BArray200.t * BArray16.t = {
    var ms:W64.t;
    var pos:W64.t;
    var i:W64.t;
    var lane:W64.t;
    var b:W8.t;
    var t:W64.t;
    var shift:W8.t;
    ms <- (init_msf);
    statep <- (protect_ptr statep ms);
    sp_0 <- (protect_ptr sp_0 ms);
    inp <- (protect_ptr inp ms);
    pos <- (BArray16.get64 statep 0);
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    pos <- (protect_64 pos ms);
    inlen <- (protect_64 inlen ms);
    i <- (W64.of_int 0);
    while ((i \ult inlen)) {
      lane <- pos;
      lane <- (lane `>>` (W8.of_int 3));
      b <- (BArray1152.get8 inp (W64.to_uint i));
      t <- (zeroextu64 b);
      shift <- (truncateu8 pos);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      i <- (i + (W64.of_int 1));
      pos <- (pos + (W64.of_int 1));
      if ((pos = (W64.of_int 136))) {
        (* Erased call to spill *)
        sp_0 <@ _keccakf1600 (sp_0);
        (* Erased call to unspill *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        ms <- (init_msf);
        statep <- (protect_ptr statep ms);
        sp_0 <- (protect_ptr sp_0 ms);
        inp <- (protect_ptr inp ms);
        inlen <- (protect_64 inlen ms);
        i <- (protect_64 i ms);
        pos <- (protect_64 pos ms);
        pos <- (W64.of_int 0);
      } else {
        
      }
    }
    ms <- (init_msf);
    statep <- (protect_ptr statep ms);
    statep <- (BArray16.set64 statep 0 pos);
    return (sp_0, statep);
  }
  proc __sign_challenge_shake256_absorb_mu32 (sp_0:BArray200.t,
                                              statep:BArray16.t,
                                              inp:BArray64.t) : BArray200.t *
                                                                BArray16.t = {
    var ms:W64.t;
    var pos:W64.t;
    var i:W64.t;
    var lane:W64.t;
    var b:W8.t;
    var t:W64.t;
    var shift:W8.t;
    ms <- (init_msf);
    statep <- (protect_ptr statep ms);
    sp_0 <- (protect_ptr sp_0 ms);
    inp <- (protect_ptr inp ms);
    pos <- (BArray16.get64 statep 0);
    (* Erased call to declassify *)
    pos <- (protect_64 pos ms);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      lane <- pos;
      lane <- (lane `>>` (W8.of_int 3));
      b <- (BArray64.get8 inp (W64.to_uint i));
      t <- (zeroextu64 b);
      shift <- (truncateu8 pos);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      i <- (i + (W64.of_int 1));
      pos <- (pos + (W64.of_int 1));
      if ((pos = (W64.of_int 136))) {
        (* Erased call to spill *)
        sp_0 <@ _keccakf1600 (sp_0);
        (* Erased call to unspill *)
        (* Erased call to declassify *)
        ms <- (init_msf);
        statep <- (protect_ptr statep ms);
        sp_0 <- (protect_ptr sp_0 ms);
        inp <- (protect_ptr inp ms);
        i <- (protect_64 i ms);
        pos <- (protect_64 pos ms);
        pos <- (W64.of_int 0);
      } else {
        
      }
    }
    ms <- (init_msf);
    statep <- (protect_ptr statep ms);
    statep <- (BArray16.set64 statep 0 pos);
    return (sp_0, statep);
  }
  proc __sign_challenge_shake256_absorb32 (sp_0:BArray200.t,
                                           statep:BArray16.t, inp:BArray32.t) : 
  BArray200.t * BArray16.t = {
    var ms:W64.t;
    var pos:W64.t;
    var i:W64.t;
    var lane:W64.t;
    var b:W8.t;
    var t:W64.t;
    var shift:W8.t;
    ms <- (init_msf);
    statep <- (protect_ptr statep ms);
    sp_0 <- (protect_ptr sp_0 ms);
    inp <- (protect_ptr inp ms);
    pos <- (BArray16.get64 statep 0);
    (* Erased call to declassify *)
    pos <- (protect_64 pos ms);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      lane <- pos;
      lane <- (lane `>>` (W8.of_int 3));
      b <- (BArray32.get8 inp (W64.to_uint i));
      t <- (zeroextu64 b);
      shift <- (truncateu8 pos);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      i <- (i + (W64.of_int 1));
      pos <- (pos + (W64.of_int 1));
      if ((pos = (W64.of_int 136))) {
        (* Erased call to spill *)
        sp_0 <@ _keccakf1600 (sp_0);
        (* Erased call to unspill *)
        (* Erased call to declassify *)
        ms <- (init_msf);
        statep <- (protect_ptr statep ms);
        sp_0 <- (protect_ptr sp_0 ms);
        inp <- (protect_ptr inp ms);
        i <- (protect_64 i ms);
        pos <- (protect_64 pos ms);
        pos <- (W64.of_int 0);
      } else {
        
      }
    }
    ms <- (init_msf);
    statep <- (protect_ptr statep ms);
    statep <- (BArray16.set64 statep 0 pos);
    return (sp_0, statep);
  }
  proc __sign_challenge_absorb (sp_0:BArray200.t, highp:BArray1152.t,
                                highlen:W64.t, lsbp:BArray32.t,
                                mup:BArray64.t) : BArray200.t = {
    var st:BArray16.t;
    var stp:BArray16.t;
    st <- witness;
    stp <- witness;
    stp <- st;
    stp <- (BArray16.set64 stp 0 (W64.of_int 0));
    stp <- (BArray16.set64 stp 1 (W64.of_int 136));
    sp_0 <@ _keccak_init_state (sp_0);
    (* Erased call to spill *)
    (sp_0, stp) <@ __sign_challenge_shake256_absorb_buf (sp_0, stp, highp,
    highlen);
    (* Erased call to unspill *)
    (* Erased call to spill *)
    (sp_0, stp) <@ __sign_challenge_shake256_absorb32 (sp_0, stp, lsbp);
    (* Erased call to unspill *)
    (sp_0, stp) <@ __sign_challenge_shake256_absorb_mu32 (sp_0, stp, mup);
    sp_0 <@ __poly_challenge_shake256_finalize (sp_0, stp);
    return sp_0;
  }
  proc __sign_challenge_m23 (cp:BArray1024.t, highp:BArray1152.t,
                             highlen:W64.t, lsbp:BArray32.t, mup:BArray64.t,
                             tau:W64.t) : BArray1024.t = {
    var state:BArray200.t;
    var sp_0:BArray200.t;
    var buf:BArray136.t;
    var bp:BArray136.t;
    var ms:W64.t;
    var i:W64.t;
    var pos:W64.t;
    var b:W32.t;
    var bidx:W64.t;
    var limit:W64.t;
    var old:W32.t;
    bp <- witness;
    buf <- witness;
    sp_0 <- witness;
    state <- witness;
    sp_0 <- state;
    bp <- buf;
    (* Erased call to spill *)
    sp_0 <@ __sign_challenge_absorb (sp_0, highp, highlen, lsbp, mup);
    (* Erased call to unspill *)
    (* Erased call to spill *)
    (bp, sp_0) <@ __poly_challenge_squeeze256_136 (bp, sp_0);
    (* Erased call to unspill *)
    ms <- (init_msf);
    cp <- (protect_ptr cp ms);
    cp <@ _poly_challenge_m23_init (cp);
    i <- (W64.of_int 256);
    i <- (i - tau);
    pos <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      if (((W64.of_int 136) \ule pos)) {
        (* Erased call to spill *)
        (bp, sp_0) <@ __poly_challenge_squeeze256_136 (bp, sp_0);
        (* Erased call to unspill *)
        ms <- (init_msf);
        cp <- (protect_ptr cp ms);
        pos <- (W64.of_int 0);
      } else {
        
      }
      b <- (zeroextu32 (BArray136.get8 bp (W64.to_uint pos)));
      pos <- (pos + (W64.of_int 1));
      bidx <- (zeroextu64 b);
      (* Erased call to declassify *)
      ms <- (init_msf);
      bidx <- (protect_64 bidx ms);
      limit <- i;
      limit <- (limit + (W64.of_int 1));
      if ((bidx \ult limit)) {
        old <- (BArray1024.get32 cp (W64.to_uint bidx));
        cp <- (BArray1024.set32 cp (W64.to_uint i) old);
        cp <- (BArray1024.set32 cp (W64.to_uint bidx) (W32.of_int 1));
        i <- (i + (W64.of_int 1));
      } else {
        
      }
    }
    return cp;
  }
  proc __sign_challenge_m5 (cp:BArray1024.t, highp:BArray1152.t,
                            highlen:W64.t, lsbp:BArray32.t, mup:BArray64.t) : 
  BArray1024.t = {
    var state:BArray200.t;
    var sp_0:BArray200.t;
    var buf:BArray32.t;
    var bp:BArray32.t;
    var ms:W64.t;
    bp <- witness;
    buf <- witness;
    sp_0 <- witness;
    state <- witness;
    sp_0 <- state;
    bp <- buf;
    (* Erased call to spill *)
    sp_0 <@ __sign_challenge_absorb (sp_0, highp, highlen, lsbp, mup);
    (* Erased call to unspill *)
    (* Erased call to spill *)
    (bp, sp_0) <@ __poly_challenge_squeeze256_32 (bp, sp_0);
    (* Erased call to unspill *)
    ms <- (init_msf);
    cp <- (protect_ptr cp ms);
    cp <@ _poly_challenge_m5_frombytes (cp, bp);
    return cp;
  }
  proc _sf_challenge_mode2 (cp:BArray1024.t, highp:BArray8192.t,
                            ayp:BArray8192.t, y0p:BArray1024.t,
                            mup:BArray64.t) : BArray1024.t * BArray8192.t = {
    var coeffs:W64.t;
    var highlen:W64.t;
    var k:W64.t;
    var tau:W64.t;
    var highbuf:BArray1152.t;
    var highbufp:BArray1152.t;
    var lsb:BArray32.t;
    var lsbp:BArray32.t;
    var ms:W64.t;
    highbuf <- witness;
    highbufp <- witness;
    lsb <- witness;
    lsbp <- witness;
    coeffs <- (W64.of_int 512);
    highlen <- (W64.of_int 576);
    k <- (W64.of_int 2);
    tau <- (W64.of_int 58);
    highbufp <- highbuf;
    lsbp <- lsb;
    (* Erased call to spill *)
    highp <@ _polyvec_highbits_hint_m23 (highp, ayp, coeffs);
    (* Erased call to unspill *)
    highbufp <@ __sign_challenge_zero_highbuf (highbufp, highlen);
    (* Erased call to spill *)
    ms <- (init_msf);
    highbufp <- (protect_ptr highbufp ms);
    highp <- (protect_ptr highp ms);
    k <- (protect_64 k ms);
    highbufp <@ _pack_vec_highbits_m23 (highbufp, highp, k);
    (* Erased call to unspill *)
    (* Erased call to spill *)
    ms <- (init_msf);
    lsbp <- (protect_ptr lsbp ms);
    y0p <- (protect_ptr y0p ms);
    lsbp <@ _pack_poly_lsb (lsbp, y0p);
    (* Erased call to unspill *)
    ms <- (init_msf);
    cp <- (protect_ptr cp ms);
    highbufp <- (protect_ptr highbufp ms);
    lsbp <- (protect_ptr lsbp ms);
    mup <- (protect_ptr mup ms);
    highlen <- (protect_64 highlen ms);
    tau <- (protect_64 tau ms);
    cp <@ __sign_challenge_m23 (cp, highbufp, highlen, lsbp, mup, tau);
    return (cp, highp);
  }
  proc _sf_challenge_mode3 (cp:BArray1024.t, highp:BArray8192.t,
                            ayp:BArray8192.t, y0p:BArray1024.t,
                            mup:BArray64.t) : BArray1024.t * BArray8192.t = {
    var coeffs:W64.t;
    var highlen:W64.t;
    var k:W64.t;
    var tau:W64.t;
    var highbuf:BArray1152.t;
    var highbufp:BArray1152.t;
    var lsb:BArray32.t;
    var lsbp:BArray32.t;
    var ms:W64.t;
    highbuf <- witness;
    highbufp <- witness;
    lsb <- witness;
    lsbp <- witness;
    coeffs <- (W64.of_int 768);
    highlen <- (W64.of_int 864);
    k <- (W64.of_int 3);
    tau <- (W64.of_int 80);
    highbufp <- highbuf;
    lsbp <- lsb;
    (* Erased call to spill *)
    highp <@ _polyvec_highbits_hint_m23 (highp, ayp, coeffs);
    (* Erased call to unspill *)
    highbufp <@ __sign_challenge_zero_highbuf (highbufp, highlen);
    (* Erased call to spill *)
    ms <- (init_msf);
    highbufp <- (protect_ptr highbufp ms);
    highp <- (protect_ptr highp ms);
    k <- (protect_64 k ms);
    highbufp <@ _pack_vec_highbits_m23 (highbufp, highp, k);
    (* Erased call to unspill *)
    (* Erased call to spill *)
    ms <- (init_msf);
    lsbp <- (protect_ptr lsbp ms);
    y0p <- (protect_ptr y0p ms);
    lsbp <@ _pack_poly_lsb (lsbp, y0p);
    (* Erased call to unspill *)
    ms <- (init_msf);
    cp <- (protect_ptr cp ms);
    highbufp <- (protect_ptr highbufp ms);
    lsbp <- (protect_ptr lsbp ms);
    mup <- (protect_ptr mup ms);
    highlen <- (protect_64 highlen ms);
    tau <- (protect_64 tau ms);
    cp <@ __sign_challenge_m23 (cp, highbufp, highlen, lsbp, mup, tau);
    return (cp, highp);
  }
  proc _sf_challenge_mode5 (cp:BArray1024.t, highp:BArray8192.t,
                            ayp:BArray8192.t, y0p:BArray1024.t,
                            mup:BArray64.t) : BArray1024.t * BArray8192.t = {
    var coeffs:W64.t;
    var highlen:W64.t;
    var k:W64.t;
    var highbuf:BArray1152.t;
    var highbufp:BArray1152.t;
    var lsb:BArray32.t;
    var lsbp:BArray32.t;
    var ms:W64.t;
    highbuf <- witness;
    highbufp <- witness;
    lsb <- witness;
    lsbp <- witness;
    coeffs <- (W64.of_int 1024);
    highlen <- (W64.of_int 1152);
    k <- (W64.of_int 4);
    highbufp <- highbuf;
    lsbp <- lsb;
    (* Erased call to spill *)
    highp <@ _polyvec_highbits_hint_m5 (highp, ayp, coeffs);
    (* Erased call to unspill *)
    highbufp <@ __sign_challenge_zero_highbuf (highbufp, highlen);
    (* Erased call to spill *)
    ms <- (init_msf);
    highbufp <- (protect_ptr highbufp ms);
    highp <- (protect_ptr highp ms);
    k <- (protect_64 k ms);
    highbufp <@ _pack_vec_highbits_m5 (highbufp, highp, k);
    (* Erased call to unspill *)
    (* Erased call to spill *)
    ms <- (init_msf);
    lsbp <- (protect_ptr lsbp ms);
    y0p <- (protect_ptr y0p ms);
    lsbp <@ _pack_poly_lsb (lsbp, y0p);
    (* Erased call to unspill *)
    ms <- (init_msf);
    cp <- (protect_ptr cp ms);
    highbufp <- (protect_ptr highbufp ms);
    lsbp <- (protect_ptr lsbp ms);
    mup <- (protect_ptr mup ms);
    highlen <- (protect_64 highlen ms);
    cp <@ __sign_challenge_m5 (cp, highbufp, highlen, lsbp, mup);
    return (cp, highp);
  }
  proc _sf_round_challenge_mode2 (cp:BArray1024.t, highp:BArray8192.t,
                                  ayp:BArray8192.t, z1rndp:BArray8192.t,
                                  z2rndp:BArray8192.t, z10p:BArray1024.t,
                                  y1p:BArray8192.t, y2p:BArray8192.t,
                                  a1p:BArray32768.t, mup:BArray64.t) : 
  BArray1024.t * BArray8192.t * BArray8192.t * BArray8192.t * BArray8192.t *
  BArray1024.t = {
    var lr:W64.t;
    var kr:W64.t;
    var kcount:W64.t;
    var ms:W64.t;
    lr <- (W64.of_int 4);
    kr <- (W64.of_int 2);
    kcount <- (W64.of_int 512);
    (z1rndp, z2rndp, z10p) <@ _sf_round_lk_copy0 (z1rndp, z2rndp, z10p, 
    y1p, y2p, (W64.of_int 1024), (W64.of_int 512));
    (* Erased call to spill *)
    z1rndp <@ _polyvec_ntt (z1rndp, lr);
    (* Erased call to unspill *)
    ayp <@ _polymat_pointwise_acc (ayp, a1p, z1rndp, kr, lr);
    ayp <@ _polyvec_invntt (ayp, kr);
    ms <- (init_msf);
    ayp <- (protect_ptr ayp ms);
    z2rndp <- (protect_ptr z2rndp ms);
    kcount <- (protect_64 kcount ms);
    (ayp, z2rndp) <@ _sign_add_double_z2rnd (ayp, z2rndp, kcount);
    ms <- (init_msf);
    ayp <- (protect_ptr ayp ms);
    z10p <- (protect_ptr z10p ms);
    kr <- (protect_64 kr ms);
    ayp <@ _sf_polyveck_poly_fromcrt_inplace (ayp, z10p, kr);
    ms <- (init_msf);
    ayp <- (protect_ptr ayp ms);
    kcount <- (protect_64 kcount ms);
    ayp <@ _polyvec_freeze2q (ayp, kcount);
    ms <- (init_msf);
    cp <- (protect_ptr cp ms);
    highp <- (protect_ptr highp ms);
    ayp <- (protect_ptr ayp ms);
    z10p <- (protect_ptr z10p ms);
    mup <- (protect_ptr mup ms);
    (cp, highp) <@ _sf_challenge_mode2 (cp, highp, ayp, z10p, mup);
    return (cp, highp, ayp, z1rndp, z2rndp, z10p);
  }
  proc _sf_round_challenge_mode3 (cp:BArray1024.t, highp:BArray8192.t,
                                  ayp:BArray8192.t, z1rndp:BArray8192.t,
                                  z2rndp:BArray8192.t, z10p:BArray1024.t,
                                  y1p:BArray8192.t, y2p:BArray8192.t,
                                  a1p:BArray32768.t, mup:BArray64.t) : 
  BArray1024.t * BArray8192.t * BArray8192.t * BArray8192.t * BArray8192.t *
  BArray1024.t = {
    var lr:W64.t;
    var kr:W64.t;
    var kcount:W64.t;
    var ms:W64.t;
    lr <- (W64.of_int 6);
    kr <- (W64.of_int 3);
    kcount <- (W64.of_int 768);
    (z1rndp, z2rndp, z10p) <@ _sf_round_lk_copy0 (z1rndp, z2rndp, z10p, 
    y1p, y2p, (W64.of_int 1536), (W64.of_int 768));
    (* Erased call to spill *)
    z1rndp <@ _polyvec_ntt (z1rndp, lr);
    (* Erased call to unspill *)
    ayp <@ _polymat_pointwise_acc (ayp, a1p, z1rndp, kr, lr);
    ayp <@ _polyvec_invntt (ayp, kr);
    ms <- (init_msf);
    ayp <- (protect_ptr ayp ms);
    z2rndp <- (protect_ptr z2rndp ms);
    kcount <- (protect_64 kcount ms);
    (ayp, z2rndp) <@ _sign_add_double_z2rnd (ayp, z2rndp, kcount);
    ms <- (init_msf);
    ayp <- (protect_ptr ayp ms);
    z10p <- (protect_ptr z10p ms);
    kr <- (protect_64 kr ms);
    ayp <@ _sf_polyveck_poly_fromcrt_inplace (ayp, z10p, kr);
    ms <- (init_msf);
    ayp <- (protect_ptr ayp ms);
    kcount <- (protect_64 kcount ms);
    ayp <@ _polyvec_freeze2q (ayp, kcount);
    ms <- (init_msf);
    cp <- (protect_ptr cp ms);
    highp <- (protect_ptr highp ms);
    ayp <- (protect_ptr ayp ms);
    z10p <- (protect_ptr z10p ms);
    mup <- (protect_ptr mup ms);
    (cp, highp) <@ _sf_challenge_mode3 (cp, highp, ayp, z10p, mup);
    return (cp, highp, ayp, z1rndp, z2rndp, z10p);
  }
  proc _sf_round_challenge_mode5 (cp:BArray1024.t, highp:BArray8192.t,
                                  ayp:BArray8192.t, z1rndp:BArray8192.t,
                                  z2rndp:BArray8192.t, z10p:BArray1024.t,
                                  y1p:BArray8192.t, y2p:BArray8192.t,
                                  a1p:BArray32768.t, mup:BArray64.t) : 
  BArray1024.t * BArray8192.t * BArray8192.t * BArray8192.t * BArray8192.t *
  BArray1024.t = {
    var lr:W64.t;
    var kr:W64.t;
    var kcount:W64.t;
    var ms:W64.t;
    lr <- (W64.of_int 7);
    kr <- (W64.of_int 4);
    kcount <- (W64.of_int 1024);
    (z1rndp, z2rndp, z10p) <@ _sf_round_lk_copy0 (z1rndp, z2rndp, z10p, 
    y1p, y2p, (W64.of_int 1792), (W64.of_int 1024));
    (* Erased call to spill *)
    z1rndp <@ _polyvec_ntt (z1rndp, lr);
    (* Erased call to unspill *)
    ayp <@ _polymat_pointwise_acc (ayp, a1p, z1rndp, kr, lr);
    ayp <@ _polyvec_invntt (ayp, kr);
    ms <- (init_msf);
    ayp <- (protect_ptr ayp ms);
    z2rndp <- (protect_ptr z2rndp ms);
    kcount <- (protect_64 kcount ms);
    (ayp, z2rndp) <@ _sign_add_double_z2rnd (ayp, z2rndp, kcount);
    ms <- (init_msf);
    ayp <- (protect_ptr ayp ms);
    z10p <- (protect_ptr z10p ms);
    kr <- (protect_64 kr ms);
    ayp <@ _sf_polyveck_poly_fromcrt_inplace (ayp, z10p, kr);
    ms <- (init_msf);
    ayp <- (protect_ptr ayp ms);
    kcount <- (protect_64 kcount ms);
    ayp <@ _polyvec_freeze2q (ayp, kcount);
    ms <- (init_msf);
    cp <- (protect_ptr cp ms);
    highp <- (protect_ptr highp ms);
    ayp <- (protect_ptr ayp ms);
    z10p <- (protect_ptr z10p ms);
    mup <- (protect_ptr mup ms);
    (cp, highp) <@ _sf_challenge_mode5 (cp, highp, ayp, z10p, mup);
    return (cp, highp, ayp, z1rndp, z2rndp, z10p);
  }
  proc _sf_add_cs_and_check (z1p:BArray8192.t, z2p:BArray8192.t,
                             z1tmpp:BArray8192.t, z2tmpp:BArray8192.t,
                             y1p:BArray8192.t, y2p:BArray8192.t,
                             cs1p:BArray8192.t, cs2p:BArray8192.t, b:W8.t,
                             lcount:W64.t, kcount:W64.t, reject1_bound:W64.t,
                             reject2_bound:W64.t) : BArray8192.t *
                                                    BArray8192.t *
                                                    BArray8192.t *
                                                    BArray8192.t * W64.t = {
    var reject1:W64.t;
    var sreject1_bound:W64.t;
    var sreject2_bound:W64.t;
    var total:W64.t;
    var sgate:W64.t;
    var twice:W32.t;
    var factor:W32.t;
    var stotal1:W64.t;
    var stotal2:W64.t;
    var i:W64.t;
    var y:W32.t;
    var cs:W32.t;
    var z:W32.t;
    var coeff:W64.t;
    var prod:W64.t;
    var tmp:W32.t;
    var reject2:W64.t;
    sreject1_bound <- reject1_bound;
    sreject2_bound <- reject2_bound;
    total <- (zeroextu64 b);
    total <- (total `&` (W64.of_int 2));
    total <- (total `>>` (W8.of_int 1));
    sgate <- total;
    twice <- (zeroextu32 b);
    twice <- (twice `&` (W32.of_int 1));
    twice <- (twice `<<` (W8.of_int 1));
    factor <- (W32.of_int 1);
    factor <- (factor - twice);
    stotal1 <- (W64.of_int 0);
    stotal2 <- (W64.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult lcount)) {
      y <- (BArray8192.get32 y1p (W64.to_uint i));
      cs <- (BArray8192.get32 cs1p (W64.to_uint i));
      cs <- (cs * factor);
      cs <- (cs * (W32.of_int 8192));
      z <- y;
      z <- (z + cs);
      z1p <- (BArray8192.set32 z1p (W64.to_uint i) z);
      coeff <- (sigextu64 z);
      prod <- (coeff * coeff);
      total <- stotal1;
      total <- (total + prod);
      stotal1 <- total;
      tmp <- z;
      tmp <- (tmp `<<` (W8.of_int 1));
      tmp <- (tmp - y);
      z1tmpp <- (BArray8192.set32 z1tmpp (W64.to_uint i) tmp);
      coeff <- (sigextu64 tmp);
      prod <- (coeff * coeff);
      total <- stotal2;
      total <- (total + prod);
      stotal2 <- total;
      i <- (i + (W64.of_int 1));
    }
    i <- (W64.of_int 0);
    while ((i \ult kcount)) {
      y <- (BArray8192.get32 y2p (W64.to_uint i));
      cs <- (BArray8192.get32 cs2p (W64.to_uint i));
      cs <- (cs * factor);
      cs <- (cs * (W32.of_int 8192));
      z <- y;
      z <- (z + cs);
      z2p <- (BArray8192.set32 z2p (W64.to_uint i) z);
      coeff <- (sigextu64 z);
      prod <- (coeff * coeff);
      total <- stotal1;
      total <- (total + prod);
      stotal1 <- total;
      tmp <- z;
      tmp <- (tmp `<<` (W8.of_int 1));
      tmp <- (tmp - y);
      z2tmpp <- (BArray8192.set32 z2tmpp (W64.to_uint i) tmp);
      coeff <- (sigextu64 tmp);
      prod <- (coeff * coeff);
      total <- stotal2;
      total <- (total + prod);
      stotal2 <- total;
      i <- (i + (W64.of_int 1));
    }
    reject1 <- sreject1_bound;
    total <- stotal1;
    reject1 <- (reject1 - total);
    reject1 <- (reject1 `>>` (W8.of_int 63));
    reject1 <- (reject1 `&` (W64.of_int 1));
    reject2 <- stotal2;
    total <- sreject2_bound;
    reject2 <- (reject2 - total);
    reject2 <- (reject2 `>>` (W8.of_int 63));
    reject2 <- (reject2 `&` (W64.of_int 1));
    total <- sgate;
    reject2 <- (reject2 `&` total);
    reject1 <- (reject1 `|` reject2);
    return (z1p, z2p, z1tmpp, z2tmpp, reject1);
  }
  proc _sf_z_check (z1p:BArray8192.t, z2p:BArray8192.t, z1tmpp:BArray8192.t,
                    z2tmpp:BArray8192.t, y1p:BArray8192.t, y2p:BArray8192.t,
                    cp:BArray1024.t, s1p:BArray8192.t, s2p:BArray8192.t,
                    b:W8.t, lcount:W64.t, kcount:W64.t, reject1_bound:W64.t,
                    reject2_bound:W64.t) : BArray8192.t * BArray8192.t *
                                           BArray8192.t * BArray8192.t *
                                           W64.t = {
    var reject:W64.t;
    var cs1:BArray8192.t;
    var cs1p:BArray8192.t;
    var cs2:BArray8192.t;
    var cs2p:BArray8192.t;
    var chat:BArray1024.t;
    var chatp:BArray1024.t;
    var lpolys:W64.t;
    var kpolys:W64.t;
    chat <- witness;
    chatp <- witness;
    cs1 <- witness;
    cs1p <- witness;
    cs2 <- witness;
    cs2p <- witness;
    cs1p <- cs1;
    cs2p <- cs2;
    chatp <- chat;
    (cs1p, chatp) <@ _sign_prepare_cs (cs1p, chatp, cp);
    lpolys <- lcount;
    lpolys <- (lpolys `>>` (W8.of_int 8));
    kpolys <- kcount;
    kpolys <- (kpolys `>>` (W8.of_int 8));
    cs1p <@ _sign_compute_cs1_tail (cs1p, chatp, s1p, lpolys);
    cs2p <@ _polyvec_poly_pointwise (cs2p, s2p, chatp, kpolys);
    cs2p <@ _polyvec_invntt (cs2p, kpolys);
    (z1p, z2p, z1tmpp, z2tmpp, reject) <@ _sf_add_cs_and_check (z1p, 
    z2p, z1tmpp, z2tmpp, y1p, y2p, cs1p, cs2p, b, lcount, kcount,
    reject1_bound, reject2_bound);
    return (z1p, z2p, z1tmpp, z2tmpp, reject);
  }
  proc _sf_hint_mode2 (hp:BArray8192.t, z1rndp:BArray8192.t,
                       z2rndp:BArray8192.t, highp:BArray8192.t,
                       ayp:BArray8192.t, z1p:BArray8192.t, z2p:BArray8192.t) : 
  BArray8192.t * BArray8192.t * BArray8192.t = {
    
    (z1rndp, z2rndp) <@ _sf_round_lk (z1rndp, z2rndp, z1p, z2p,
    (W64.of_int 1024), (W64.of_int 512));
    hp <@ _sign_make_hint (hp, highp, ayp, z2rndp, (W64.of_int 512), 256, 9,
    252);
    return (hp, z1rndp, z2rndp);
  }
  proc _sf_hint_mode3 (hp:BArray8192.t, z1rndp:BArray8192.t,
                       z2rndp:BArray8192.t, highp:BArray8192.t,
                       ayp:BArray8192.t, z1p:BArray8192.t, z2p:BArray8192.t) : 
  BArray8192.t * BArray8192.t * BArray8192.t = {
    
    (z1rndp, z2rndp) <@ _sf_round_lk (z1rndp, z2rndp, z1p, z2p,
    (W64.of_int 1536), (W64.of_int 768));
    hp <@ _sign_make_hint (hp, highp, ayp, z2rndp, (W64.of_int 768), 256, 9,
    252);
    return (hp, z1rndp, z2rndp);
  }
  proc _sf_hint_mode5 (hp:BArray8192.t, z1rndp:BArray8192.t,
                       z2rndp:BArray8192.t, highp:BArray8192.t,
                       ayp:BArray8192.t, z1p:BArray8192.t, z2p:BArray8192.t) : 
  BArray8192.t * BArray8192.t * BArray8192.t = {
    
    (z1rndp, z2rndp) <@ _sf_round_lk (z1rndp, z2rndp, z1p, z2p,
    (W64.of_int 1792), (W64.of_int 1024));
    hp <@ _sign_make_hint (hp, highp, ayp, z2rndp, (W64.of_int 1024), 128, 8,
    504);
    return (hp, z1rndp, z2rndp);
  }
  proc _sf_pack_mode2 (sigp:BArray2948.t, cp:BArray1024.t,
                       z1rndp:BArray8192.t, hp:BArray8192.t) : BArray2948.t *
                                                               W64.t = {
    var reject:W64.t;
    var count:W64.t;
    var lowz:BArray8192.t;
    var lowp:BArray8192.t;
    var highz:BArray8192.t;
    var highp:BArray8192.t;
    var bad:BArray8.t;
    var badp:BArray8.t;
    var hb_esymsp:BArray528.t;
    var h_esymsp:BArray528.t;
    bad <- witness;
    badp <- witness;
    h_esymsp <- witness;
    hb_esymsp <- witness;
    highp <- witness;
    highz <- witness;
    lowp <- witness;
    lowz <- witness;
    count <- (W64.of_int 1024);
    lowp <- lowz;
    highp <- highz;
    badp <- bad;
    badp <- (BArray8.set64 badp 0 (W64.of_int 0));
    (lowp, highp) <@ _polyvec_decompose_z1 (lowp, highp, z1rndp, count);
    hb_esymsp <- jmode2_hb_z1_esyms;
    h_esymsp <- jmode2_h_esyms;
    (sigp, badp) <@ _pack_sig_full (sigp, badp, cp, lowp, highp, hp,
    hb_esymsp, h_esymsp, 1474, 4, 1024, 13, 6, 512, 13, 239, 132, 7, 416);
    reject <- (BArray8.get64 badp 0);
    return (sigp, reject);
  }
  proc _sf_pack_mode3 (sigp:BArray2948.t, cp:BArray1024.t,
                       z1rndp:BArray8192.t, hp:BArray8192.t) : BArray2948.t *
                                                               W64.t = {
    var reject:W64.t;
    var count:W64.t;
    var lowz:BArray8192.t;
    var lowp:BArray8192.t;
    var highz:BArray8192.t;
    var highp:BArray8192.t;
    var bad:BArray8.t;
    var badp:BArray8.t;
    var hb_esymsp:BArray528.t;
    var h_esymsp:BArray528.t;
    bad <- witness;
    badp <- witness;
    h_esymsp <- witness;
    hb_esymsp <- witness;
    highp <- witness;
    highz <- witness;
    lowp <- witness;
    lowz <- witness;
    count <- (W64.of_int 1536);
    lowp <- lowz;
    highp <- highz;
    badp <- bad;
    badp <- (BArray8.set64 badp 0 (W64.of_int 0));
    (lowp, highp) <@ _polyvec_decompose_z1 (lowp, highp, z1rndp, count);
    hb_esymsp <- jmode3_hb_z1_esyms;
    h_esymsp <- jmode3_h_esyms;
    (sigp, badp) <@ _pack_sig_full (sigp, badp, cp, lowp, highp, hp,
    hb_esymsp, h_esymsp, 2349, 6, 1536, 17, 8, 768, 17, 235, 376, 127, 779);
    reject <- (BArray8.get64 badp 0);
    return (sigp, reject);
  }
  proc _sf_pack_mode5 (sigp:BArray2948.t, cp:BArray1024.t,
                       z1rndp:BArray8192.t, hp:BArray8192.t) : BArray2948.t *
                                                               W64.t = {
    var reject:W64.t;
    var count:W64.t;
    var lowz:BArray8192.t;
    var lowp:BArray8192.t;
    var highz:BArray8192.t;
    var highp:BArray8192.t;
    var bad:BArray8.t;
    var badp:BArray8.t;
    var hb_esymsp:BArray528.t;
    var h_esymsp:BArray528.t;
    bad <- witness;
    badp <- witness;
    h_esymsp <- witness;
    hb_esymsp <- witness;
    highp <- witness;
    highz <- witness;
    lowp <- witness;
    lowz <- witness;
    count <- (W64.of_int 1792);
    lowp <- lowz;
    highp <- highz;
    badp <- bad;
    badp <- (BArray8.set64 badp 0 (W64.of_int 0));
    (lowp, highp) <@ _polyvec_decompose_z1 (lowp, highp, z1rndp, count);
    hb_esymsp <- jmode5_hb_z1_esyms;
    h_esymsp <- jmode5_h_esyms;
    (sigp, badp) <@ _pack_sig_full (sigp, badp, cp, lowp, highp, hp,
    hb_esymsp, h_esymsp, 2948, 7, 1792, 19, 9, 1024, 33, 471, 501, 358,
    1122);
    reject <- (BArray8.get64 badp 0);
    return (sigp, reject);
  }
  proc _sf_signature_core_mode2 (sigp:BArray2948.t, skp:BArray2752.t,
                                 rndp:BArray32.t, mup:BArray64.t) : BArray2948.t = {
    var seedbuf:BArray64.t;
    var seedbufp:BArray64.t;
    var key:BArray32.t;
    var keyp:BArray32.t;
    var b:BArray1.t;
    var bp:BArray1.t;
    var counter:BArray8.t;
    var counterp:BArray8.t;
    var a1:BArray32768.t;
    var a1p:BArray32768.t;
    var s1:BArray8192.t;
    var s1p:BArray8192.t;
    var s2:BArray8192.t;
    var s2p:BArray8192.t;
    var y1:BArray8192.t;
    var y1p:BArray8192.t;
    var y2:BArray8192.t;
    var y2p:BArray8192.t;
    var z1:BArray8192.t;
    var z1p:BArray8192.t;
    var z2:BArray8192.t;
    var z2p:BArray8192.t;
    var z1tmp:BArray8192.t;
    var z1tmpp:BArray8192.t;
    var z2tmp:BArray8192.t;
    var z2tmpp:BArray8192.t;
    var z1rnd:BArray8192.t;
    var z1rndp:BArray8192.t;
    var z2rnd:BArray8192.t;
    var z2rndp:BArray8192.t;
    var highbits:BArray8192.t;
    var highp:BArray8192.t;
    var ay:BArray8192.t;
    var ayp:BArray8192.t;
    var h:BArray8192.t;
    var hp:BArray8192.t;
    var c:BArray1024.t;
    var cp:BArray1024.t;
    var z10:BArray1024.t;
    var z10p:BArray1024.t;
    var s1polys:W64.t;
    var s2polys:W64.t;
    var lcount:W64.t;
    var kcount:W64.t;
    var b1bound:W64.t;
    var b0bound:W64.t;
    var bad:W64.t;
    var bv:W8.t;
    var reject:W64.t;
    var ms:W64.t;
    a1 <- witness;
    a1p <- witness;
    ay <- witness;
    ayp <- witness;
    b <- witness;
    bp <- witness;
    c <- witness;
    counter <- witness;
    counterp <- witness;
    cp <- witness;
    h <- witness;
    highbits <- witness;
    highp <- witness;
    hp <- witness;
    key <- witness;
    keyp <- witness;
    s1 <- witness;
    s1p <- witness;
    s2 <- witness;
    s2p <- witness;
    seedbuf <- witness;
    seedbufp <- witness;
    y1 <- witness;
    y1p <- witness;
    y2 <- witness;
    y2p <- witness;
    z1 <- witness;
    z10 <- witness;
    z10p <- witness;
    z1p <- witness;
    z1rnd <- witness;
    z1rndp <- witness;
    z1tmp <- witness;
    z1tmpp <- witness;
    z2 <- witness;
    z2p <- witness;
    z2rnd <- witness;
    z2rndp <- witness;
    z2tmp <- witness;
    z2tmpp <- witness;
    seedbufp <- seedbuf;
    keyp <- key;
    bp <- b;
    counterp <- counter;
    a1p <- a1;
    s1p <- s1;
    s2p <- s2;
    y1p <- y1;
    y2p <- y2;
    z1p <- z1;
    z2p <- z2;
    z1tmpp <- z1tmp;
    z2tmpp <- z2tmp;
    z1rndp <- z1rnd;
    z2rndp <- z2rnd;
    highp <- highbits;
    ayp <- ay;
    hp <- h;
    cp <- c;
    z10p <- z10;
    s1polys <- (W64.of_int 3);
    s2polys <- (W64.of_int 2);
    lcount <- (W64.of_int 1024);
    kcount <- (W64.of_int 512);
    b1bound <- (W64.of_int 6496508945891328);
    b0bound <- (W64.of_int 6505809026482176);
    (a1p, s1p, s2p, keyp) <@ _sf_unpack_sk_mode2 (a1p, s1p, s2p, keyp, skp);
    seedbufp <@ _sf_sign_expand_seedbuf (seedbufp, keyp, rndp, mup);
    s1p <@ _polyvec_ntt (s1p, s1polys);
    s2p <@ _polyvec_ntt (s2p, s2polys);
    counterp <- (BArray8.set64 counterp 0 (W64.of_int 0));
    bad <- (W64.of_int 1);
    while ((bad <> (W64.of_int 0))) {
      (y1p, y2p, bp, counterp) <@ _sf_hyperball_mode2 (y1p, y2p, bp,
      counterp, seedbufp);
      (cp, highp, ayp, z1rndp, z2rndp, z10p) <@ _sf_round_challenge_mode2 (
      cp, highp, ayp, z1rndp, z2rndp, z10p, y1p, y2p, a1p, mup);
      bv <- (BArray1.get8 bp 0);
      (z1p, z2p, z1tmpp, z2tmpp, reject) <@ _sf_z_check (z1p, z2p, z1tmpp,
      z2tmpp, y1p, y2p, cp, s1p, s2p, bv, lcount, kcount, b1bound, b0bound);
      (* Erased call to declassify *)
      ms <- (init_msf);
      reject <- (protect_64 reject ms);
      bad <- (W64.of_int 1);
      if ((reject = (W64.of_int 0))) {
        (hp, z1rndp, z2rndp) <@ _sf_hint_mode2 (hp, z1rndp, z2rndp, highp,
        ayp, z1p, z2p);
        (sigp, bad) <@ _sf_pack_mode2 (sigp, cp, z1rndp, hp);
      } else {
        
      }
      (* Erased call to declassify *)
      ms <- (init_msf);
      bad <- (protect_64 bad ms);
    }
    return sigp;
  }
  proc _sf_signature_core_mode3 (sigp:BArray2948.t, skp:BArray2752.t,
                                 rndp:BArray32.t, mup:BArray64.t) : BArray2948.t = {
    var seedbuf:BArray64.t;
    var seedbufp:BArray64.t;
    var key:BArray32.t;
    var keyp:BArray32.t;
    var b:BArray1.t;
    var bp:BArray1.t;
    var counter:BArray8.t;
    var counterp:BArray8.t;
    var a1:BArray32768.t;
    var a1p:BArray32768.t;
    var s1:BArray8192.t;
    var s1p:BArray8192.t;
    var s2:BArray8192.t;
    var s2p:BArray8192.t;
    var y1:BArray8192.t;
    var y1p:BArray8192.t;
    var y2:BArray8192.t;
    var y2p:BArray8192.t;
    var z1:BArray8192.t;
    var z1p:BArray8192.t;
    var z2:BArray8192.t;
    var z2p:BArray8192.t;
    var z1tmp:BArray8192.t;
    var z1tmpp:BArray8192.t;
    var z2tmp:BArray8192.t;
    var z2tmpp:BArray8192.t;
    var z1rnd:BArray8192.t;
    var z1rndp:BArray8192.t;
    var z2rnd:BArray8192.t;
    var z2rndp:BArray8192.t;
    var highbits:BArray8192.t;
    var highp:BArray8192.t;
    var ay:BArray8192.t;
    var ayp:BArray8192.t;
    var h:BArray8192.t;
    var hp:BArray8192.t;
    var c:BArray1024.t;
    var cp:BArray1024.t;
    var z10:BArray1024.t;
    var z10p:BArray1024.t;
    var s1polys:W64.t;
    var s2polys:W64.t;
    var lcount:W64.t;
    var kcount:W64.t;
    var b1bound:W64.t;
    var b0bound:W64.t;
    var bad:W64.t;
    var bv:W8.t;
    var reject:W64.t;
    var ms:W64.t;
    a1 <- witness;
    a1p <- witness;
    ay <- witness;
    ayp <- witness;
    b <- witness;
    bp <- witness;
    c <- witness;
    counter <- witness;
    counterp <- witness;
    cp <- witness;
    h <- witness;
    highbits <- witness;
    highp <- witness;
    hp <- witness;
    key <- witness;
    keyp <- witness;
    s1 <- witness;
    s1p <- witness;
    s2 <- witness;
    s2p <- witness;
    seedbuf <- witness;
    seedbufp <- witness;
    y1 <- witness;
    y1p <- witness;
    y2 <- witness;
    y2p <- witness;
    z1 <- witness;
    z10 <- witness;
    z10p <- witness;
    z1p <- witness;
    z1rnd <- witness;
    z1rndp <- witness;
    z1tmp <- witness;
    z1tmpp <- witness;
    z2 <- witness;
    z2p <- witness;
    z2rnd <- witness;
    z2rndp <- witness;
    z2tmp <- witness;
    z2tmpp <- witness;
    seedbufp <- seedbuf;
    keyp <- key;
    bp <- b;
    counterp <- counter;
    a1p <- a1;
    s1p <- s1;
    s2p <- s2;
    y1p <- y1;
    y2p <- y2;
    z1p <- z1;
    z2p <- z2;
    z1tmpp <- z1tmp;
    z2tmpp <- z2tmp;
    z1rndp <- z1rnd;
    z2rndp <- z2rnd;
    highp <- highbits;
    ayp <- ay;
    hp <- h;
    cp <- c;
    z10p <- z10;
    s1polys <- (W64.of_int 5);
    s2polys <- (W64.of_int 3);
    lcount <- (W64.of_int 1536);
    kcount <- (W64.of_int 768);
    b1bound <- (W64.of_int 22493004044435456);
    b0bound <- (W64.of_int 22510896139993088);
    (a1p, s1p, s2p, keyp) <@ _sf_unpack_sk_mode3 (a1p, s1p, s2p, keyp, skp);
    seedbufp <@ _sf_sign_expand_seedbuf (seedbufp, keyp, rndp, mup);
    s1p <@ _polyvec_ntt (s1p, s1polys);
    s2p <@ _polyvec_ntt (s2p, s2polys);
    counterp <- (BArray8.set64 counterp 0 (W64.of_int 0));
    bad <- (W64.of_int 1);
    while ((bad <> (W64.of_int 0))) {
      (y1p, y2p, bp, counterp) <@ _sf_hyperball_mode3 (y1p, y2p, bp,
      counterp, seedbufp);
      (cp, highp, ayp, z1rndp, z2rndp, z10p) <@ _sf_round_challenge_mode3 (
      cp, highp, ayp, z1rndp, z2rndp, z10p, y1p, y2p, a1p, mup);
      bv <- (BArray1.get8 bp 0);
      (z1p, z2p, z1tmpp, z2tmpp, reject) <@ _sf_z_check (z1p, z2p, z1tmpp,
      z2tmpp, y1p, y2p, cp, s1p, s2p, bv, lcount, kcount, b1bound, b0bound);
      (* Erased call to declassify *)
      ms <- (init_msf);
      reject <- (protect_64 reject ms);
      bad <- (W64.of_int 1);
      if ((reject = (W64.of_int 0))) {
        (hp, z1rndp, z2rndp) <@ _sf_hint_mode3 (hp, z1rndp, z2rndp, highp,
        ayp, z1p, z2p);
        (sigp, bad) <@ _sf_pack_mode3 (sigp, cp, z1rndp, hp);
      } else {
        
      }
      (* Erased call to declassify *)
      ms <- (init_msf);
      bad <- (protect_64 bad ms);
    }
    return sigp;
  }
  proc _sf_signature_core_mode5 (sigp:BArray2948.t, skp:BArray2752.t,
                                 rndp:BArray32.t, mup:BArray64.t) : BArray2948.t = {
    var seedbuf:BArray64.t;
    var seedbufp:BArray64.t;
    var key:BArray32.t;
    var keyp:BArray32.t;
    var b:BArray1.t;
    var bp:BArray1.t;
    var counter:BArray8.t;
    var counterp:BArray8.t;
    var a1:BArray32768.t;
    var a1p:BArray32768.t;
    var s1:BArray8192.t;
    var s1p:BArray8192.t;
    var s2:BArray8192.t;
    var s2p:BArray8192.t;
    var y1:BArray8192.t;
    var y1p:BArray8192.t;
    var y2:BArray8192.t;
    var y2p:BArray8192.t;
    var z1:BArray8192.t;
    var z1p:BArray8192.t;
    var z2:BArray8192.t;
    var z2p:BArray8192.t;
    var z1tmp:BArray8192.t;
    var z1tmpp:BArray8192.t;
    var z2tmp:BArray8192.t;
    var z2tmpp:BArray8192.t;
    var z1rnd:BArray8192.t;
    var z1rndp:BArray8192.t;
    var z2rnd:BArray8192.t;
    var z2rndp:BArray8192.t;
    var highbits:BArray8192.t;
    var highp:BArray8192.t;
    var ay:BArray8192.t;
    var ayp:BArray8192.t;
    var h:BArray8192.t;
    var hp:BArray8192.t;
    var c:BArray1024.t;
    var cp:BArray1024.t;
    var z10:BArray1024.t;
    var z10p:BArray1024.t;
    var s1polys:W64.t;
    var s2polys:W64.t;
    var lcount:W64.t;
    var kcount:W64.t;
    var b1bound:W64.t;
    var b0bound:W64.t;
    var bad:W64.t;
    var bv:W8.t;
    var reject:W64.t;
    var ms:W64.t;
    a1 <- witness;
    a1p <- witness;
    ay <- witness;
    ayp <- witness;
    b <- witness;
    bp <- witness;
    c <- witness;
    counter <- witness;
    counterp <- witness;
    cp <- witness;
    h <- witness;
    highbits <- witness;
    highp <- witness;
    hp <- witness;
    key <- witness;
    keyp <- witness;
    s1 <- witness;
    s1p <- witness;
    s2 <- witness;
    s2p <- witness;
    seedbuf <- witness;
    seedbufp <- witness;
    y1 <- witness;
    y1p <- witness;
    y2 <- witness;
    y2p <- witness;
    z1 <- witness;
    z10 <- witness;
    z10p <- witness;
    z1p <- witness;
    z1rnd <- witness;
    z1rndp <- witness;
    z1tmp <- witness;
    z1tmpp <- witness;
    z2 <- witness;
    z2p <- witness;
    z2rnd <- witness;
    z2rndp <- witness;
    z2tmp <- witness;
    z2tmpp <- witness;
    seedbufp <- seedbuf;
    keyp <- key;
    bp <- b;
    counterp <- counter;
    a1p <- a1;
    s1p <- s1;
    s2p <- s2;
    y1p <- y1;
    y2p <- y2;
    z1p <- z1;
    z2p <- z2;
    z1tmpp <- z1tmp;
    z2tmpp <- z2tmp;
    z1rndp <- z1rnd;
    z2rndp <- z2rnd;
    highp <- highbits;
    ayp <- ay;
    hp <- h;
    cp <- c;
    z10p <- z10;
    s1polys <- (W64.of_int 6);
    s2polys <- (W64.of_int 4);
    lcount <- (W64.of_int 1792);
    kcount <- (W64.of_int 1024);
    b1bound <- (W64.of_int 33477256202420224);
    b0bound <- (W64.of_int 33503371683954688);
    (a1p, s1p, s2p, keyp) <@ _sf_unpack_sk_mode5 (a1p, s1p, s2p, keyp, skp);
    seedbufp <@ _sf_sign_expand_seedbuf (seedbufp, keyp, rndp, mup);
    s1p <@ _polyvec_ntt (s1p, s1polys);
    s2p <@ _polyvec_ntt (s2p, s2polys);
    counterp <- (BArray8.set64 counterp 0 (W64.of_int 0));
    bad <- (W64.of_int 1);
    while ((bad <> (W64.of_int 0))) {
      (y1p, y2p, bp, counterp) <@ _sf_hyperball_mode5 (y1p, y2p, bp,
      counterp, seedbufp);
      (cp, highp, ayp, z1rndp, z2rndp, z10p) <@ _sf_round_challenge_mode5 (
      cp, highp, ayp, z1rndp, z2rndp, z10p, y1p, y2p, a1p, mup);
      bv <- (BArray1.get8 bp 0);
      (z1p, z2p, z1tmpp, z2tmpp, reject) <@ _sf_z_check (z1p, z2p, z1tmpp,
      z2tmpp, y1p, y2p, cp, s1p, s2p, bv, lcount, kcount, b1bound, b0bound);
      (* Erased call to declassify *)
      ms <- (init_msf);
      reject <- (protect_64 reject ms);
      bad <- (W64.of_int 1);
      if ((reject = (W64.of_int 0))) {
        (hp, z1rndp, z2rndp) <@ _sf_hint_mode5 (hp, z1rndp, z2rndp, highp,
        ayp, z1p, z2p);
        (sigp, bad) <@ _sf_pack_mode5 (sigp, cp, z1rndp, hp);
      } else {
        
      }
      (* Erased call to declassify *)
      ms <- (init_msf);
      bad <- (protect_64 bad ms);
    }
    return sigp;
  }
  proc crypto_sign_signature_internal_mode2_jazz (sigp:BArray2948.t,
                                                  skp:BArray2752.t,
                                                  rndp:BArray32.t,
                                                  descp:BArray32.t) : 
  BArray2948.t = {
    var ms:W64.t;
    var mu:BArray64.t;
    var mup:BArray64.t;
    var vkbytes:W64.t;
    var preaddr:W64.t;
    var prelen:W64.t;
    var maddr:W64.t;
    var mlen:W64.t;
    mu <- witness;
    mup <- witness;
    ms <- (init_msf);
    descp <- (protect_ptr descp ms);
    mup <- mu;
    vkbytes <- (W64.of_int 992);
    preaddr <- (BArray32.get64 descp 0);
    prelen <- (BArray32.get64 descp 1);
    maddr <- (BArray32.get64 descp 2);
    mlen <- (BArray32.get64 descp 3);
    mup <@ _sf_mu_rawpre (mup, skp, vkbytes, preaddr, prelen, maddr, mlen);
    (* Erased call to declassify *)
    sigp <@ _sf_signature_core_mode2 (sigp, skp, rndp, mup);
    return sigp;
  }
  proc crypto_sign_signature_internal_mode3_jazz (sigp:BArray2948.t,
                                                  skp:BArray2752.t,
                                                  rndp:BArray32.t,
                                                  descp:BArray32.t) : 
  BArray2948.t = {
    var ms:W64.t;
    var mu:BArray64.t;
    var mup:BArray64.t;
    var vkbytes:W64.t;
    var preaddr:W64.t;
    var prelen:W64.t;
    var maddr:W64.t;
    var mlen:W64.t;
    mu <- witness;
    mup <- witness;
    ms <- (init_msf);
    descp <- (protect_ptr descp ms);
    mup <- mu;
    vkbytes <- (W64.of_int 1472);
    preaddr <- (BArray32.get64 descp 0);
    prelen <- (BArray32.get64 descp 1);
    maddr <- (BArray32.get64 descp 2);
    mlen <- (BArray32.get64 descp 3);
    mup <@ _sf_mu_rawpre (mup, skp, vkbytes, preaddr, prelen, maddr, mlen);
    (* Erased call to declassify *)
    sigp <@ _sf_signature_core_mode3 (sigp, skp, rndp, mup);
    return sigp;
  }
  proc crypto_sign_signature_internal_mode5_jazz (sigp:BArray2948.t,
                                                  skp:BArray2752.t,
                                                  rndp:BArray32.t,
                                                  descp:BArray32.t) : 
  BArray2948.t = {
    var ms:W64.t;
    var mu:BArray64.t;
    var mup:BArray64.t;
    var vkbytes:W64.t;
    var preaddr:W64.t;
    var prelen:W64.t;
    var maddr:W64.t;
    var mlen:W64.t;
    mu <- witness;
    mup <- witness;
    ms <- (init_msf);
    descp <- (protect_ptr descp ms);
    mup <- mu;
    vkbytes <- (W64.of_int 2080);
    preaddr <- (BArray32.get64 descp 0);
    prelen <- (BArray32.get64 descp 1);
    maddr <- (BArray32.get64 descp 2);
    mlen <- (BArray32.get64 descp 3);
    mup <@ _sf_mu_rawpre (mup, skp, vkbytes, preaddr, prelen, maddr, mlen);
    (* Erased call to declassify *)
    sigp <@ _sf_signature_core_mode5 (sigp, skp, rndp, mup);
    return sigp;
  }
  proc crypto_sign_signature_mode2_jazz (sigp:BArray2948.t, skp:BArray2752.t,
                                         descp:BArray32.t) : BArray2948.t = {
    var ms:W64.t;
    var descq:BArray32.t;
    var pre:BArray257.t;
    var prep:BArray257.t;
    var rnd_0:BArray32.t;
    var rndp:BArray32.t;
    var mu:BArray64.t;
    var mup:BArray64.t;
    var vkbytes:W64.t;
    var maddr:W64.t;
    var mlen:W64.t;
    var ctxaddr:W64.t;
    var ctxlen:W64.t;
    var prelen:W64.t;
    descq <- witness;
    mu <- witness;
    mup <- witness;
    pre <- witness;
    prep <- witness;
    rnd_0 <- witness;
    rndp <- witness;
    ms <- (init_msf);
    descq <- descp;
    descq <- (protect_ptr descq ms);
    prep <- pre;
    rndp <- rnd_0;
    mup <- mu;
    vkbytes <- (W64.of_int 992);
    maddr <- (BArray32.get64 descq 0);
    mlen <- (BArray32.get64 descq 1);
    ctxaddr <- (BArray32.get64 descq 2);
    ctxlen <- (BArray32.get64 descq 3);
    prep <@ _sf_prepare_pre_raw (prep, ctxaddr, ctxlen);
    (* Erased call to declassify *)
    rndp <@ SC.randombytes_32 (rndp);
    (* Erased call to declassify *)
    prelen <- ctxlen;
    prelen <- (prelen + (W64.of_int 1));
    mup <@ _sf_mu_preptr (mup, skp, vkbytes, prep, prelen, maddr, mlen);
    (* Erased call to declassify *)
    sigp <@ _sf_signature_core_mode2 (sigp, skp, rndp, mup);
    return sigp;
  }
  proc crypto_sign_signature_mode3_jazz (sigp:BArray2948.t, skp:BArray2752.t,
                                         descp:BArray32.t) : BArray2948.t = {
    var ms:W64.t;
    var pre:BArray257.t;
    var prep:BArray257.t;
    var rnd_0:BArray32.t;
    var rndp:BArray32.t;
    var mu:BArray64.t;
    var mup:BArray64.t;
    var vkbytes:W64.t;
    var maddr:W64.t;
    var mlen:W64.t;
    var ctxaddr:W64.t;
    var ctxlen:W64.t;
    var prelen:W64.t;
    mu <- witness;
    mup <- witness;
    pre <- witness;
    prep <- witness;
    rnd_0 <- witness;
    rndp <- witness;
    ms <- (init_msf);
    descp <- (protect_ptr descp ms);
    prep <- pre;
    rndp <- rnd_0;
    mup <- mu;
    vkbytes <- (W64.of_int 1472);
    maddr <- (BArray32.get64 descp 0);
    mlen <- (BArray32.get64 descp 1);
    ctxaddr <- (BArray32.get64 descp 2);
    ctxlen <- (BArray32.get64 descp 3);
    prep <@ _sf_prepare_pre_raw (prep, ctxaddr, ctxlen);
    (* Erased call to declassify *)
    rndp <@ SC.randombytes_32 (rndp);
    (* Erased call to declassify *)
    prelen <- ctxlen;
    prelen <- (prelen + (W64.of_int 1));
    mup <@ _sf_mu_preptr (mup, skp, vkbytes, prep, prelen, maddr, mlen);
    (* Erased call to declassify *)
    sigp <@ _sf_signature_core_mode3 (sigp, skp, rndp, mup);
    return sigp;
  }
  proc crypto_sign_signature_mode5_jazz (sigp:BArray2948.t, skp:BArray2752.t,
                                         descp:BArray32.t) : BArray2948.t = {
    var ms:W64.t;
    var pre:BArray257.t;
    var prep:BArray257.t;
    var rnd_0:BArray32.t;
    var rndp:BArray32.t;
    var mu:BArray64.t;
    var mup:BArray64.t;
    var vkbytes:W64.t;
    var maddr:W64.t;
    var mlen:W64.t;
    var ctxaddr:W64.t;
    var ctxlen:W64.t;
    var prelen:W64.t;
    mu <- witness;
    mup <- witness;
    pre <- witness;
    prep <- witness;
    rnd_0 <- witness;
    rndp <- witness;
    ms <- (init_msf);
    descp <- (protect_ptr descp ms);
    prep <- pre;
    rndp <- rnd_0;
    mup <- mu;
    vkbytes <- (W64.of_int 2080);
    maddr <- (BArray32.get64 descp 0);
    mlen <- (BArray32.get64 descp 1);
    ctxaddr <- (BArray32.get64 descp 2);
    ctxlen <- (BArray32.get64 descp 3);
    prep <@ _sf_prepare_pre_raw (prep, ctxaddr, ctxlen);
    (* Erased call to declassify *)
    rndp <@ SC.randombytes_32 (rndp);
    (* Erased call to declassify *)
    prelen <- ctxlen;
    prelen <- (prelen + (W64.of_int 1));
    mup <@ _sf_mu_preptr (mup, skp, vkbytes, prep, prelen, maddr, mlen);
    (* Erased call to declassify *)
    sigp <@ _sf_signature_core_mode5 (sigp, skp, rndp, mup);
    return sigp;
  }
  proc cryptolab_haetae_mode2_signature_internal_desc (sigu:int, siglenu:int,
                                                       rndu:int, sku:int,
                                                       apip:BArray32.t) : 
  W64.t = {
    var r:W64.t;
    var sig:BArray2948.t;
    var sigp:BArray2948.t;
    var sk:BArray2752.t;
    var skp:BArray2752.t;
    var rnd_0:BArray32.t;
    var rndp:BArray32.t;
    var desc:BArray32.t;
    var descp:BArray32.t;
    var skaddr:W64.t;
    var rndaddr:W64.t;
    var ms:W64.t;
    desc <- witness;
    descp <- witness;
    rnd_0 <- witness;
    rndp <- witness;
    sig <- witness;
    sigp <- witness;
    sk <- witness;
    skp <- witness;
    sigp <- sig;
    skp <- sk;
    rndp <- rnd_0;
    descp <- desc;
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    skaddr <- (W64.of_int sku);
    rndaddr <- (W64.of_int rndu);
    ms <- (init_msf);
    skaddr <- (protect_64 skaddr ms);
    rndaddr <- (protect_64 rndaddr ms);
    skp <@ _api_copy_addr_to_2752_prefix (skp, skaddr, (W64.of_int 1408));
    (* Erased call to declassify *)
    rndp <@ _api_copy_addr_to_32 (rndp, rndaddr);
    (* Erased call to declassify *)
    ms <- (init_msf);
    apip <- (protect_ptr apip ms);
    descp <- (BArray32.set64 descp 0 (BArray32.get64 apip 0));
    descp <- (BArray32.set64 descp 1 (BArray32.get64 apip 1));
    descp <- (BArray32.set64 descp 2 (BArray32.get64 apip 2));
    descp <- (BArray32.set64 descp 3 (BArray32.get64 apip 3));
    (* Erased call to declassify *)
    descp <- (protect_ptr descp ms);
    sigp <@ crypto_sign_signature_internal_mode2_jazz (sigp, skp, rndp,
    descp);
    sigu <@ _api_copy_2948_to_raw (sigu, sigp, 1474);
    Glob.mem <- (storeW64 Glob.mem siglenu (W64.of_int 1474));
    r <- (W64.of_int 0);
    return r;
  }
  proc cryptolab_haetae_mode3_signature_internal_desc (sigu:int, siglenu:int,
                                                       rndu:int, sku:int,
                                                       apip:BArray32.t) : 
  W64.t = {
    var r:W64.t;
    var sig:BArray2948.t;
    var sigp:BArray2948.t;
    var sk:BArray2752.t;
    var skp:BArray2752.t;
    var rnd_0:BArray32.t;
    var rndp:BArray32.t;
    var desc:BArray32.t;
    var descp:BArray32.t;
    var skaddr:W64.t;
    var rndaddr:W64.t;
    var ms:W64.t;
    desc <- witness;
    descp <- witness;
    rnd_0 <- witness;
    rndp <- witness;
    sig <- witness;
    sigp <- witness;
    sk <- witness;
    skp <- witness;
    sigp <- sig;
    skp <- sk;
    rndp <- rnd_0;
    descp <- desc;
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    skaddr <- (W64.of_int sku);
    rndaddr <- (W64.of_int rndu);
    ms <- (init_msf);
    skaddr <- (protect_64 skaddr ms);
    rndaddr <- (protect_64 rndaddr ms);
    skp <@ _api_copy_addr_to_2752_prefix (skp, skaddr, (W64.of_int 2112));
    (* Erased call to declassify *)
    rndp <@ _api_copy_addr_to_32 (rndp, rndaddr);
    (* Erased call to declassify *)
    ms <- (init_msf);
    apip <- (protect_ptr apip ms);
    descp <- (BArray32.set64 descp 0 (BArray32.get64 apip 0));
    descp <- (BArray32.set64 descp 1 (BArray32.get64 apip 1));
    descp <- (BArray32.set64 descp 2 (BArray32.get64 apip 2));
    descp <- (BArray32.set64 descp 3 (BArray32.get64 apip 3));
    (* Erased call to declassify *)
    descp <- (protect_ptr descp ms);
    sigp <@ crypto_sign_signature_internal_mode3_jazz (sigp, skp, rndp,
    descp);
    sigu <@ _api_copy_2948_to_raw (sigu, sigp, 2349);
    Glob.mem <- (storeW64 Glob.mem siglenu (W64.of_int 2349));
    r <- (W64.of_int 0);
    return r;
  }
  proc cryptolab_haetae_mode5_signature_internal_desc (sigu:int, siglenu:int,
                                                       rndu:int, sku:int,
                                                       apip:BArray32.t) : 
  W64.t = {
    var r:W64.t;
    var sig:BArray2948.t;
    var sigp:BArray2948.t;
    var sk:BArray2752.t;
    var skp:BArray2752.t;
    var rnd_0:BArray32.t;
    var rndp:BArray32.t;
    var desc:BArray32.t;
    var descp:BArray32.t;
    var skaddr:W64.t;
    var rndaddr:W64.t;
    var ms:W64.t;
    desc <- witness;
    descp <- witness;
    rnd_0 <- witness;
    rndp <- witness;
    sig <- witness;
    sigp <- witness;
    sk <- witness;
    skp <- witness;
    sigp <- sig;
    skp <- sk;
    rndp <- rnd_0;
    descp <- desc;
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    skaddr <- (W64.of_int sku);
    rndaddr <- (W64.of_int rndu);
    ms <- (init_msf);
    skaddr <- (protect_64 skaddr ms);
    rndaddr <- (protect_64 rndaddr ms);
    skp <@ _api_copy_addr_to_2752_prefix (skp, skaddr, (W64.of_int 2752));
    (* Erased call to declassify *)
    rndp <@ _api_copy_addr_to_32 (rndp, rndaddr);
    (* Erased call to declassify *)
    ms <- (init_msf);
    apip <- (protect_ptr apip ms);
    descp <- (BArray32.set64 descp 0 (BArray32.get64 apip 0));
    descp <- (BArray32.set64 descp 1 (BArray32.get64 apip 1));
    descp <- (BArray32.set64 descp 2 (BArray32.get64 apip 2));
    descp <- (BArray32.set64 descp 3 (BArray32.get64 apip 3));
    (* Erased call to declassify *)
    descp <- (protect_ptr descp ms);
    sigp <@ crypto_sign_signature_internal_mode5_jazz (sigp, skp, rndp,
    descp);
    sigu <@ _api_copy_2948_to_raw (sigu, sigp, 2948);
    Glob.mem <- (storeW64 Glob.mem siglenu (W64.of_int 2948));
    r <- (W64.of_int 0);
    return r;
  }
  proc cryptolab_haetae_mode2_signature_desc (sigu:int, siglenu:int, sku:int,
                                              apip:BArray32.t) : W64.t = {
    var r:W64.t;
    var ms:W64.t;
    var ctxlen:W64.t;
    var sig:BArray2948.t;
    var sigp:BArray2948.t;
    var sk:BArray2752.t;
    var skp:BArray2752.t;
    var desc:BArray32.t;
    var descp:BArray32.t;
    var skaddr:W64.t;
    desc <- witness;
    descp <- witness;
    sig <- witness;
    sigp <- witness;
    sk <- witness;
    skp <- witness;
    ms <- (init_msf);
    apip <- (protect_ptr apip ms);
    ctxlen <- (BArray32.get64 apip 3);
    (* Erased call to declassify *)
    if (((W64.of_int 255) \ult ctxlen)) {
      r <@ _api_reject ();
    } else {
      sigp <- sig;
      skp <- sk;
      descp <- desc;
      (* Erased call to declassify *)
      skaddr <- (W64.of_int sku);
      ms <- (init_msf);
      skaddr <- (protect_64 skaddr ms);
      skp <@ _api_copy_addr_to_2752_prefix (skp, skaddr, (W64.of_int 1408));
      (* Erased call to declassify *)
      ms <- (init_msf);
      apip <- (protect_ptr apip ms);
      descp <- (BArray32.set64 descp 0 (BArray32.get64 apip 0));
      descp <- (BArray32.set64 descp 1 (BArray32.get64 apip 1));
      descp <- (BArray32.set64 descp 2 (BArray32.get64 apip 2));
      descp <- (BArray32.set64 descp 3 ctxlen);
      (* Erased call to declassify *)
      descp <- (protect_ptr descp ms);
      sigp <@ crypto_sign_signature_mode2_jazz (sigp, skp, descp);
      sigu <@ _api_copy_2948_to_raw (sigu, sigp, 1474);
      Glob.mem <- (storeW64 Glob.mem siglenu (W64.of_int 1474));
      r <- (W64.of_int 0);
    }
    return r;
  }
  proc cryptolab_haetae_mode3_signature_desc (sigu:int, siglenu:int, sku:int,
                                              apip:BArray32.t) : W64.t = {
    var r:W64.t;
    var ms:W64.t;
    var ctxlen:W64.t;
    var sig:BArray2948.t;
    var sigp:BArray2948.t;
    var sk:BArray2752.t;
    var skp:BArray2752.t;
    var desc:BArray32.t;
    var descp:BArray32.t;
    var skaddr:W64.t;
    desc <- witness;
    descp <- witness;
    sig <- witness;
    sigp <- witness;
    sk <- witness;
    skp <- witness;
    ms <- (init_msf);
    apip <- (protect_ptr apip ms);
    ctxlen <- (BArray32.get64 apip 3);
    (* Erased call to declassify *)
    if (((W64.of_int 255) \ult ctxlen)) {
      r <@ _api_reject ();
    } else {
      sigp <- sig;
      skp <- sk;
      descp <- desc;
      (* Erased call to declassify *)
      skaddr <- (W64.of_int sku);
      ms <- (init_msf);
      skaddr <- (protect_64 skaddr ms);
      skp <@ _api_copy_addr_to_2752_prefix (skp, skaddr, (W64.of_int 2112));
      (* Erased call to declassify *)
      ms <- (init_msf);
      apip <- (protect_ptr apip ms);
      descp <- (BArray32.set64 descp 0 (BArray32.get64 apip 0));
      descp <- (BArray32.set64 descp 1 (BArray32.get64 apip 1));
      descp <- (BArray32.set64 descp 2 (BArray32.get64 apip 2));
      descp <- (BArray32.set64 descp 3 ctxlen);
      (* Erased call to declassify *)
      descp <- (protect_ptr descp ms);
      sigp <@ crypto_sign_signature_mode3_jazz (sigp, skp, descp);
      sigu <@ _api_copy_2948_to_raw (sigu, sigp, 2349);
      Glob.mem <- (storeW64 Glob.mem siglenu (W64.of_int 2349));
      r <- (W64.of_int 0);
    }
    return r;
  }
  proc cryptolab_haetae_mode5_signature_desc (sigu:int, siglenu:int, sku:int,
                                              apip:BArray32.t) : W64.t = {
    var r:W64.t;
    var ms:W64.t;
    var ctxlen:W64.t;
    var sig:BArray2948.t;
    var sigp:BArray2948.t;
    var sk:BArray2752.t;
    var skp:BArray2752.t;
    var desc:BArray32.t;
    var descp:BArray32.t;
    var skaddr:W64.t;
    desc <- witness;
    descp <- witness;
    sig <- witness;
    sigp <- witness;
    sk <- witness;
    skp <- witness;
    ms <- (init_msf);
    apip <- (protect_ptr apip ms);
    ctxlen <- (BArray32.get64 apip 3);
    (* Erased call to declassify *)
    if (((W64.of_int 255) \ult ctxlen)) {
      r <@ _api_reject ();
    } else {
      sigp <- sig;
      skp <- sk;
      descp <- desc;
      (* Erased call to declassify *)
      skaddr <- (W64.of_int sku);
      ms <- (init_msf);
      skaddr <- (protect_64 skaddr ms);
      skp <@ _api_copy_addr_to_2752_prefix (skp, skaddr, (W64.of_int 2752));
      (* Erased call to declassify *)
      ms <- (init_msf);
      apip <- (protect_ptr apip ms);
      descp <- (BArray32.set64 descp 0 (BArray32.get64 apip 0));
      descp <- (BArray32.set64 descp 1 (BArray32.get64 apip 1));
      descp <- (BArray32.set64 descp 2 (BArray32.get64 apip 2));
      descp <- (BArray32.set64 descp 3 ctxlen);
      (* Erased call to declassify *)
      descp <- (protect_ptr descp ms);
      sigp <@ crypto_sign_signature_mode5_jazz (sigp, skp, descp);
      sigu <@ _api_copy_2948_to_raw (sigu, sigp, 2948);
      Glob.mem <- (storeW64 Glob.mem siglenu (W64.of_int 2948));
      r <- (W64.of_int 0);
    }
    return r;
  }
  proc cryptolab_haetae_mode2_sign_desc (smu:int, smlenu:int, sku:int,
                                         apip:BArray32.t) : W64.t = {
    var r:W64.t;
    var ms:W64.t;
    var maddr:W64.t;
    var mlen:W64.t;
    var ctxlen:W64.t;
    var daddr:W64.t;
    var sig:BArray2948.t;
    var sigp:BArray2948.t;
    var sk:BArray2752.t;
    var skp:BArray2752.t;
    var desc:BArray32.t;
    var descp:BArray32.t;
    var skaddr:W64.t;
    var total:W64.t;
    var dst:int;
    desc <- witness;
    descp <- witness;
    sig <- witness;
    sigp <- witness;
    sk <- witness;
    skp <- witness;
    ms <- (init_msf);
    apip <- (protect_ptr apip ms);
    maddr <- (BArray32.get64 apip 0);
    mlen <- (BArray32.get64 apip 1);
    ctxlen <- (BArray32.get64 apip 3);
    (* Erased call to declassify *)
    dst <- smu;
    dst <- (dst + 1474);
    daddr <- (W64.of_int dst);
    daddr <@ _api_copy_addr_to_addr_backward (daddr, maddr, mlen);
    if (((W64.of_int 255) \ult ctxlen)) {
      total <- (loadW64 Glob.mem smlenu);
      total <- (total + mlen);
      Glob.mem <- (storeW64 Glob.mem smlenu total);
      r <@ _api_reject ();
    } else {
      sigp <- sig;
      skp <- sk;
      descp <- desc;
      (* Erased call to declassify *)
      skaddr <- (W64.of_int sku);
      ms <- (init_msf);
      skaddr <- (protect_64 skaddr ms);
      skp <@ _api_copy_addr_to_2752_prefix (skp, skaddr, (W64.of_int 1408));
      (* Erased call to declassify *)
      ms <- (init_msf);
      apip <- (protect_ptr apip ms);
      descp <- (BArray32.set64 descp 0 daddr);
      descp <- (BArray32.set64 descp 1 mlen);
      descp <- (BArray32.set64 descp 2 (BArray32.get64 apip 2));
      descp <- (BArray32.set64 descp 3 ctxlen);
      (* Erased call to declassify *)
      descp <- (protect_ptr descp ms);
      sigp <@ crypto_sign_signature_mode2_jazz (sigp, skp, descp);
      smu <@ _api_copy_2948_to_raw (smu, sigp, 1474);
      total <- (W64.of_int 1474);
      total <- (total + mlen);
      Glob.mem <- (storeW64 Glob.mem smlenu total);
      r <- (W64.of_int 0);
    }
    return r;
  }
  proc cryptolab_haetae_mode3_sign_desc (smu:int, smlenu:int, sku:int,
                                         apip:BArray32.t) : W64.t = {
    var r:W64.t;
    var ms:W64.t;
    var maddr:W64.t;
    var mlen:W64.t;
    var ctxlen:W64.t;
    var daddr:W64.t;
    var sig:BArray2948.t;
    var sigp:BArray2948.t;
    var sk:BArray2752.t;
    var skp:BArray2752.t;
    var desc:BArray32.t;
    var descp:BArray32.t;
    var skaddr:W64.t;
    var total:W64.t;
    var dst:int;
    desc <- witness;
    descp <- witness;
    sig <- witness;
    sigp <- witness;
    sk <- witness;
    skp <- witness;
    ms <- (init_msf);
    apip <- (protect_ptr apip ms);
    maddr <- (BArray32.get64 apip 0);
    mlen <- (BArray32.get64 apip 1);
    ctxlen <- (BArray32.get64 apip 3);
    (* Erased call to declassify *)
    dst <- smu;
    dst <- (dst + 2349);
    daddr <- (W64.of_int dst);
    daddr <@ _api_copy_addr_to_addr_backward (daddr, maddr, mlen);
    if (((W64.of_int 255) \ult ctxlen)) {
      total <- (loadW64 Glob.mem smlenu);
      total <- (total + mlen);
      Glob.mem <- (storeW64 Glob.mem smlenu total);
      r <@ _api_reject ();
    } else {
      sigp <- sig;
      skp <- sk;
      descp <- desc;
      (* Erased call to declassify *)
      skaddr <- (W64.of_int sku);
      ms <- (init_msf);
      skaddr <- (protect_64 skaddr ms);
      skp <@ _api_copy_addr_to_2752_prefix (skp, skaddr, (W64.of_int 2112));
      (* Erased call to declassify *)
      ms <- (init_msf);
      apip <- (protect_ptr apip ms);
      descp <- (BArray32.set64 descp 0 daddr);
      descp <- (BArray32.set64 descp 1 mlen);
      descp <- (BArray32.set64 descp 2 (BArray32.get64 apip 2));
      descp <- (BArray32.set64 descp 3 ctxlen);
      (* Erased call to declassify *)
      descp <- (protect_ptr descp ms);
      sigp <@ crypto_sign_signature_mode3_jazz (sigp, skp, descp);
      smu <@ _api_copy_2948_to_raw (smu, sigp, 2349);
      total <- (W64.of_int 2349);
      total <- (total + mlen);
      Glob.mem <- (storeW64 Glob.mem smlenu total);
      r <- (W64.of_int 0);
    }
    return r;
  }
  proc cryptolab_haetae_mode5_sign_desc (smu:int, smlenu:int, sku:int,
                                         apip:BArray32.t) : W64.t = {
    var r:W64.t;
    var ms:W64.t;
    var maddr:W64.t;
    var mlen:W64.t;
    var ctxlen:W64.t;
    var daddr:W64.t;
    var sig:BArray2948.t;
    var sigp:BArray2948.t;
    var sk:BArray2752.t;
    var skp:BArray2752.t;
    var desc:BArray32.t;
    var descp:BArray32.t;
    var skaddr:W64.t;
    var total:W64.t;
    var dst:int;
    desc <- witness;
    descp <- witness;
    sig <- witness;
    sigp <- witness;
    sk <- witness;
    skp <- witness;
    ms <- (init_msf);
    apip <- (protect_ptr apip ms);
    maddr <- (BArray32.get64 apip 0);
    mlen <- (BArray32.get64 apip 1);
    ctxlen <- (BArray32.get64 apip 3);
    (* Erased call to declassify *)
    dst <- smu;
    dst <- (dst + 2948);
    daddr <- (W64.of_int dst);
    daddr <@ _api_copy_addr_to_addr_backward (daddr, maddr, mlen);
    if (((W64.of_int 255) \ult ctxlen)) {
      total <- (loadW64 Glob.mem smlenu);
      total <- (total + mlen);
      Glob.mem <- (storeW64 Glob.mem smlenu total);
      r <@ _api_reject ();
    } else {
      sigp <- sig;
      skp <- sk;
      descp <- desc;
      (* Erased call to declassify *)
      skaddr <- (W64.of_int sku);
      ms <- (init_msf);
      skaddr <- (protect_64 skaddr ms);
      skp <@ _api_copy_addr_to_2752_prefix (skp, skaddr, (W64.of_int 2752));
      (* Erased call to declassify *)
      ms <- (init_msf);
      apip <- (protect_ptr apip ms);
      descp <- (BArray32.set64 descp 0 daddr);
      descp <- (BArray32.set64 descp 1 mlen);
      descp <- (BArray32.set64 descp 2 (BArray32.get64 apip 2));
      descp <- (BArray32.set64 descp 3 ctxlen);
      (* Erased call to declassify *)
      descp <- (protect_ptr descp ms);
      sigp <@ crypto_sign_signature_mode5_jazz (sigp, skp, descp);
      smu <@ _api_copy_2948_to_raw (smu, sigp, 2948);
      total <- (W64.of_int 2948);
      total <- (total + mlen);
      Glob.mem <- (storeW64 Glob.mem smlenu total);
      r <- (W64.of_int 0);
    }
    return r;
  }
}.
