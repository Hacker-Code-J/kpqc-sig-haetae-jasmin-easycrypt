require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import
Array1 Array2 Array3 Array4 Array5 Array24 Array25 Array32 Array132 Array136
Array256 Array512 Array1024 Array1152 Array2048 Array2752 Array2948 Array8192
WArray192 WArray528 WArray1024 WArray2048 BArray8 BArray16 BArray24 BArray32
BArray40 BArray136 BArray192 BArray200 BArray528 BArray1024 BArray1152
BArray2048 BArray2752 BArray2948 BArray8192 BArray32768.

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

module M = {
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
  proc __reduce32_2q (a:W32.t) : W32.t = {
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
    mask64 <- x;
    mask64 <- (mask64 - (W64.of_int 64513));
    mask64 <- (mask64 `|>>` (W8.of_int 31));
    mask32 <- (truncateu32 mask64);
    mask32 <- (mask32 + (W32.of_int 1));
    mask32 <- (mask32 * (W32.of_int 129026));
    mask64 <- (zeroextu64 mask32);
    x <- (x - mask64);
    mask32 <- (truncateu32 x);
    return mask32;
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
  proc _keccak_init_state (sp_0:BArray200.t) : BArray200.t = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 25))) {
      sp_0 <- (BArray200.set64 sp_0 (W64.to_uint i) (W64.of_int 0));
      i <- (i + (W64.of_int 1));
    }
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
  proc _unpack_sig_prefix (cp:BArray1024.t, lowp:BArray8192.t,
                           sigp:BArray2948.t, lcount:W64.t) : BArray1024.t *
                                                              BArray8192.t = {
    var i:W64.t;
    var b:W32.t;
    var idx:W64.t;
    var j:int;
    var bit:W32.t;
    var off:W64.t;
    var total:W64.t;
    var a:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      b <- (zeroextu32 (BArray2948.get8 sigp (W64.to_uint i)));
      j <- 0;
      while ((j < 8)) {
        idx <- ((W64.of_int 8) * i);
        idx <- (idx + (W64.of_int j));
        bit <- b;
        bit <- (bit `>>` (W8.of_int j));
        bit <- (bit `&` (W32.of_int 1));
        cp <- (BArray1024.set32 cp (W64.to_uint idx) bit);
        j <- (j + 1);
      }
      i <- (i + (W64.of_int 1));
    }
    off <- (W64.of_int 32);
    total <- lcount;
    total <- (total * (W64.of_int 256));
    i <- (W64.of_int 0);
    while ((i \ult total)) {
      idx <- off;
      idx <- (idx + i);
      a <- (zeroextu32 (BArray2948.get8 sigp (W64.to_uint idx)));
      a <- (a `<<` (W8.of_int 24));
      a <- (a `|>>` (W8.of_int 24));
      lowp <- (BArray8192.set32 lowp (W64.to_uint i) a);
      i <- (i + (W64.of_int 1));
    }
    return (cp, lowp);
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
  proc _rans_decode (symsp:BArray2048.t, statep:BArray24.t,
                     bufp:BArray2048.t, symbolwp:BArray2048.t,
                     dsymswp:BArray528.t) : BArray2048.t * BArray24.t = {
    var count:W64.t;
    var size_in:W64.t;
    var m:W64.t;
    var ms:W64.t;
    var upper:W64.t;
    var bad:W64.t;
    var off:W64.t;
    var x:W32.t;
    var tmp:W32.t;
    var x64:W64.t;
    var b:bool;
    var i:W64.t;
    var cond:bool;
    var idx:W64.t;
    var tmp64:W64.t;
    var word:W32.t;
    var s32:W32.t;
    var s:W8.t;
    var packed:W32.t;
    var start:W32.t;
    var freq:W32.t;
    var q:W32.t;
    var low:W32.t;
    var again:W64.t;
    var byte:W8.t;
    count <- (BArray24.get64 statep 0);
    size_in <- (BArray24.get64 statep 1);
    m <- (BArray24.get64 statep 2);
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    count <- (protect_64 count ms);
    size_in <- (protect_64 size_in ms);
    m <- (protect_64 m ms);
    (* Erased call to spill *)
    upper <- (W64.of_int 1);
    upper <- (upper `<<` (W8.of_int 31));
    bad <- (W64.of_int 0);
    off <- (W64.of_int 4);
    x <- (zeroextu32 (BArray2048.get8 bufp 0));
    tmp <- (zeroextu32 (BArray2048.get8 bufp 1));
    tmp <- (tmp `<<` (W8.of_int 8));
    x <- (x `|` tmp);
    tmp <- (zeroextu32 (BArray2048.get8 bufp 2));
    tmp <- (tmp `<<` (W8.of_int 16));
    x <- (x `|` tmp);
    tmp <- (zeroextu32 (BArray2048.get8 bufp 3));
    tmp <- (tmp `<<` (W8.of_int 24));
    x <- (x `|` tmp);
    x64 <- (zeroextu64 x);
    (* Erased call to declassify *)
    ms <- (init_msf);
    x64 <- (protect_64 x64 ms);
    x <- (truncateu32 x64);
    b <- (x64 \ult (W64.of_int 8388608));
    if (b) {
      ms <- (update_msf b ms);
      bad <- (W64.of_int 1);
    } else {
      ms <- (update_msf (! b) ms);
    }
    b <- (upper \ule x64);
    if (b) {
      ms <- (update_msf b ms);
      bad <- (W64.of_int 1);
    } else {
      ms <- (update_msf (! b) ms);
    }
    i <- (W64.of_int 0);
    cond <- (i \ult count);
    while (cond) {
      ms <- (update_msf cond ms);
      b <- (bad <> (W64.of_int 0));
      if (b) {
        ms <- (update_msf b ms);
        i <- count;
      } else {
        ms <- (update_msf (! b) ms);
        idx <- (zeroextu64 x);
        idx <- (idx `&` (W64.of_int 1023));
        tmp64 <- idx;
        tmp64 <- (tmp64 `&` (W64.of_int 1));
        idx <- (idx `>>` (W8.of_int 1));
        word <- (BArray2048.get32 symbolwp (W64.to_uint idx));
        (* Erased call to declassify *)
        tmp64 <- (protect_64 tmp64 ms);
        b <- (tmp64 <> (W64.of_int 0));
        if (b) {
          ms <- (update_msf b ms);
          word <- (word `>>` (W8.of_int 16));
        } else {
          ms <- (update_msf (! b) ms);
        }
        s32 <- word;
        s32 <- (s32 `&` (W32.of_int 65535));
        tmp64 <- (zeroextu64 s32);
        (* Erased call to declassify *)
        tmp64 <- (protect_64 tmp64 ms);
        b <- (m \ule tmp64);
        if (b) {
          ms <- (update_msf b ms);
          bad <- (W64.of_int 1);
        } else {
          ms <- (update_msf (! b) ms);
          s <- (truncateu8 tmp64);
          symsp <- (BArray2048.set8 symsp (W64.to_uint i) s);
          idx <- tmp64;
          packed <- (BArray528.get32 dsymswp (W64.to_uint idx));
          start <- packed;
          start <- (start `&` (W32.of_int 65535));
          freq <- packed;
          freq <- (freq `>>` (W8.of_int 16));
          q <- x;
          q <- (q `>>` (W8.of_int 10));
          low <- x;
          low <- (low `&` (W32.of_int 1023));
          q <- (q * freq);
          q <- (q + low);
          q <- (q - start);
          x <- q;
          again <- (W64.of_int 1);
          ms <- (mov_msf ms);
          cond <- (again <> (W64.of_int 0));
          while (cond) {
            ms <- (update_msf cond ms);
            x64 <- (zeroextu64 x);
            (* Erased call to declassify *)
            x64 <- (protect_64 x64 ms);
            b <- (x64 \ult (W64.of_int 8388608));
            if (b) {
              ms <- (update_msf b ms);
              b <- (off \ult size_in);
              if (b) {
                ms <- (update_msf b ms);
                byte <- (BArray2048.get8 bufp (W64.to_uint off));
                (* Erased call to declassify *)
                byte <- (protect_8 byte ms);
                off <- (off + (W64.of_int 1));
                x <- (x `<<` (W8.of_int 8));
                tmp <- (zeroextu32 byte);
                x <- (x `|` tmp);
              } else {
                ms <- (update_msf (! b) ms);
                again <- (W64.of_int 0);
              }
            } else {
              ms <- (update_msf (! b) ms);
              again <- (W64.of_int 0);
            }
            (* Erased call to declassify *)
            cond <- (again <> (W64.of_int 0));
          }
          ms <- (update_msf (! cond) ms);
          i <- (i + (W64.of_int 1));
        }
      }
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      x64 <- (zeroextu64 x);
      (* Erased call to declassify *)
      ms <- (init_msf);
      i <- (protect_64 i ms);
      off <- (protect_64 off ms);
      bad <- (protect_64 bad ms);
      x64 <- (protect_64 x64 ms);
      x <- (truncateu32 x64);
      cond <- (i \ult count);
    }
    ms <- (update_msf (! cond) ms);
    if ((bad = (W64.of_int 0))) {
      if ((x <> (W32.of_int 8388608))) {
        bad <- (W64.of_int 1);
      } else {
        
      }
      if ((off <> size_in)) {
        bad <- (W64.of_int 1);
      } else {
        
      }
    } else {
      
    }
    (* Erased call to unspill *)
    statep <- (BArray24.set64 statep 0 off);
    statep <- (BArray24.set64 statep 1 bad);
    return (symsp, statep);
  }
  proc _decode_h_apply (hp:BArray8192.t, symsp:BArray2048.t, count:W64.t,
                        hcut:W64.t, offset:W64.t) : BArray8192.t = {
    var off32:W32.t;
    var i:W64.t;
    var s:W8.t;
    var tmp:W32.t;
    var tmp64:W64.t;
    var ms:W64.t;
    var b:bool;
    off32 <- (truncateu32 offset);
    i <- (W64.of_int 0);
    while ((i \ult count)) {
      s <- (BArray2048.get8 symsp (W64.to_uint i));
      tmp <- (zeroextu32 s);
      tmp64 <- (zeroextu64 tmp);
      (* Erased call to declassify *)
      ms <- (init_msf);
      tmp64 <- (protect_64 tmp64 ms);
      b <- (hcut \ult tmp64);
      if (b) {
        ms <- (update_msf b ms);
        tmp <- (tmp + off32);
      } else {
        ms <- (update_msf (! b) ms);
      }
      hp <- (BArray8192.set32 hp (W64.to_uint i) tmp);
      i <- (i + (W64.of_int 1));
    }
    return hp;
  }
  proc _decode_hb_z1_apply (hp:BArray8192.t, symsp:BArray2048.t, count:W64.t,
                            offset:W64.t) : BArray8192.t = {
    var off32:W32.t;
    var i:W64.t;
    var s:W8.t;
    var tmp:W32.t;
    off32 <- (truncateu32 offset);
    i <- (W64.of_int 0);
    while ((i \ult count)) {
      s <- (BArray2048.get8 symsp (W64.to_uint i));
      tmp <- (zeroextu32 s);
      tmp <- (tmp - off32);
      hp <- (BArray8192.set32 hp (W64.to_uint i) tmp);
      i <- (i + (W64.of_int 1));
    }
    return hp;
  }
  proc _decode_h_full (hp:BArray8192.t, badp:BArray8.t, bufp:BArray2048.t,
                       size_in:W64.t, symbolwp:BArray2048.t,
                       dsymswp:BArray528.t, count:W64.t, mh:W64.t,
                       offset:W64.t) : BArray8192.t * BArray8.t = {
    var symbols:BArray2048.t;
    var symsp:BArray2048.t;
    var state:BArray24.t;
    var statep:BArray24.t;
    var bad:W64.t;
    var ms:W64.t;
    var b:bool;
    var hcut:W64.t;
    state <- witness;
    statep <- witness;
    symbols <- witness;
    symsp <- witness;
    symsp <- symbols;
    statep <- state;
    statep <- (BArray24.set64 statep 0 count);
    statep <- (BArray24.set64 statep 1 size_in);
    statep <- (BArray24.set64 statep 2 mh);
    (* Erased call to spill *)
    (symsp, statep) <@ _rans_decode (symsp, statep, bufp, symbolwp, dsymswp);
    (* Erased call to unspill *)
    bad <- (BArray24.get64 statep 1);
    (* Erased call to declassify *)
    ms <- (init_msf);
    bad <- (protect_64 bad ms);
    b <- (bad = (W64.of_int 0));
    if (b) {
      ms <- (update_msf b ms);
      hcut <- mh;
      hcut <- (hcut - (W64.of_int 1));
      hcut <- (hcut `>>` (W8.of_int 1));
      hp <@ _decode_h_apply (hp, symsp, count, hcut, offset);
    } else {
      ms <- (update_msf (! b) ms);
    }
    badp <- (BArray8.set64 badp 0 bad);
    return (hp, badp);
  }
  proc _decode_hb_z1_full (hp:BArray8192.t, badp:BArray8.t,
                           bufp:BArray2048.t, size_in:W64.t,
                           symbolwp:BArray2048.t, dsymswp:BArray528.t,
                           count:W64.t, mhb:W64.t, offset:W64.t) : BArray8192.t *
                                                                   BArray8.t = {
    var symbols:BArray2048.t;
    var symsp:BArray2048.t;
    var state:BArray24.t;
    var statep:BArray24.t;
    var bad:W64.t;
    var ms:W64.t;
    var b:bool;
    state <- witness;
    statep <- witness;
    symbols <- witness;
    symsp <- witness;
    symsp <- symbols;
    statep <- state;
    statep <- (BArray24.set64 statep 0 count);
    statep <- (BArray24.set64 statep 1 size_in);
    statep <- (BArray24.set64 statep 2 mhb);
    (* Erased call to spill *)
    (symsp, statep) <@ _rans_decode (symsp, statep, bufp, symbolwp, dsymswp);
    (* Erased call to unspill *)
    bad <- (BArray24.get64 statep 1);
    (* Erased call to declassify *)
    ms <- (init_msf);
    bad <- (protect_64 bad ms);
    b <- (bad = (W64.of_int 0));
    if (b) {
      ms <- (update_msf b ms);
      hp <@ _decode_hb_z1_apply (hp, symsp, count, offset);
    } else {
      ms <- (update_msf (! b) ms);
    }
    badp <- (BArray8.set64 badp 0 bad);
    return (hp, badp);
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
  proc _poly_mismatch (ap:BArray1024.t, bp:BArray1024.t) : W64.t = {
    var acc:W64.t;
    var i:W64.t;
    var a:W32.t;
    var b:W32.t;
    var diff:W32.t;
    var t:W64.t;
    var neg:W64.t;
    i <- (W64.of_int 0);
    acc <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      a <- (BArray1024.get32 ap (W64.to_uint i));
      b <- (BArray1024.get32 bp (W64.to_uint i));
      diff <- a;
      diff <- (diff `^` b);
      t <- (zeroextu64 diff);
      acc <- (acc `|` t);
      i <- (i + (W64.of_int 1));
    }
    neg <- (W64.of_int 0);
    neg <- (neg - acc);
    acc <- (acc `|` neg);
    acc <- (acc `>>` (W8.of_int 63));
    return acc;
  }
  proc _polyveck_poly_fromcrt (wp_0:BArray8192.t, up:BArray8192.t,
                               vp:BArray1024.t, count:W64.t) : BArray8192.t = {
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
      xq <- (BArray8192.get32 up (W64.to_uint j));
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
        xq <- (BArray8192.get32 up (W64.to_uint idx));
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
  proc _polyvec_sqnorm2 (ap:BArray8192.t, count:W64.t) : W64.t = {
    var total:W64.t;
    var i:W64.t;
    var a:W32.t;
    var coeff:W64.t;
    var prod:W64.t;
    total <- (W64.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult count)) {
      a <- (BArray8192.get32 ap (W64.to_uint i));
      coeff <- (sigextu64 a);
      prod <- (coeff * coeff);
      total <- (total + prod);
      i <- (i + (W64.of_int 1));
    }
    return total;
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
  proc __poly_sample_shake128_init (sp_0:BArray200.t, seedp:int, nonce:W64.t) : 
  BArray200.t = {
    var n:W64.t;
    var pos:W64.t;
    var lane:W64.t;
    var b:W8.t;
    var t:W64.t;
    var shift:W8.t;
    var k:int;
    var src:int;
    sp_0 <@ _keccak_init_state (sp_0);
    src <- seedp;
    n <- nonce;
    pos <- (W64.of_int 0);
    while ((pos \ult (W64.of_int 32))) {
      lane <- pos;
      lane <- (lane `>>` (W8.of_int 3));
      b <- (loadW8 Glob.mem src);
      t <- (zeroextu64 b);
      shift <- (truncateu8 pos);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      src <- (src + 1);
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
  proc _poly_uniform_at (ap:BArray32768.t, base:W64.t, seedp:int, nonce:W64.t) : 
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
    sp_0 <@ __poly_sample_shake128_init (sp_0, seedp, nonce);
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
    ms <- (init_msf);
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
      (* Erased call to declassify *)
      ms <- (init_msf);
      ctr <- (protect_64 ctr ms);
      buflen <- (W64.of_int 168);
      buflen <- (buflen + off);
      (ap, ctr) <@ __poly_uniform_consume (ap, base, ctr, bufp, buflen);
      (* Erased call to declassify *)
      ms <- (init_msf);
      ctr <- (protect_64 ctr ms);
    }
    return ap;
  }
  proc _polymatkl_expand_matA (matp:BArray32768.t, seedp:int, rows:W64.t,
                               cols:W64.t) : BArray32768.t = {
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
        matp <@ _poly_uniform_at (matp, base, seedp, nonce);
        (* Erased call to unspill *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        ms <- (init_msf);
        matp <- (protect_ptr matp ms);
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
  proc __copy_sig_slice (outp:BArray2048.t, sigp:BArray2948.t, off:W64.t,
                         size:W64.t) : BArray2048.t = {
    var i:W64.t;
    var src:W64.t;
    var b:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult size)) {
      src <- off;
      src <- (src + i);
      b <- (zeroextu32 (BArray2948.get8 sigp (W64.to_uint src)));
      outp <- (BArray2048.set8 outp (W64.to_uint i) (truncateu8 b));
      i <- (i + (W64.of_int 1));
    }
    return outp;
  }
  proc __unpack_sig_finish_at (statep:BArray32.t, sigp:BArray2948.t,
                               off:W64.t) : BArray32.t = {
    var base_hb:W64.t;
    var base_h:W64.t;
    var payload_limit:W64.t;
    var b:W32.t;
    var hbsize:W64.t;
    var hsize:W64.t;
    var ms:W64.t;
    var bad:W64.t;
    var padlen:W64.t;
    var total:W64.t;
    var i:W64.t;
    var idx:W64.t;
    var bb:W64.t;
    base_hb <- (BArray32.get64 statep 0);
    base_h <- (BArray32.get64 statep 1);
    payload_limit <- (BArray32.get64 statep 2);
    b <- (zeroextu32 (BArray2948.get8 sigp (W64.to_uint off)));
    hbsize <- (zeroextu64 b);
    hbsize <- (hbsize + base_hb);
    b <-
    (zeroextu32 (BArray2948.get8 sigp (W64.to_uint (off + (W64.of_int 1)))));
    hsize <- (zeroextu64 b);
    hsize <- (hsize + base_h);
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    hbsize <- (protect_64 hbsize ms);
    hsize <- (protect_64 hsize ms);
    payload_limit <- (protect_64 payload_limit ms);
    bad <- (W64.of_int 0);
    padlen <- (W64.of_int 0);
    total <- hbsize;
    total <- (total + hsize);
    (* Erased call to declassify *)
    ms <- (init_msf);
    total <- (protect_64 total ms);
    payload_limit <- (protect_64 payload_limit ms);
    if ((payload_limit \ult total)) {
      bad <- (W64.of_int 1);
    } else {
      padlen <- payload_limit;
      padlen <- (padlen - total);
    }
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    bad <- (protect_64 bad ms);
    padlen <- (protect_64 padlen ms);
    if ((bad = (W64.of_int 0))) {
      i <- (W64.of_int 0);
      while ((i \ult padlen)) {
        idx <- off;
        idx <- (idx + (W64.of_int 2));
        idx <- (idx + hbsize);
        idx <- (idx + hsize);
        idx <- (idx + i);
        b <- (zeroextu32 (BArray2948.get8 sigp (W64.to_uint idx)));
        bb <- (zeroextu64 b);
        bad <- (bad `|` bb);
        i <- (i + (W64.of_int 1));
      }
      (* Erased call to declassify *)
      ms <- (init_msf);
      bad <- (protect_64 bad ms);
      if ((bad <> (W64.of_int 0))) {
        bad <- (W64.of_int 1);
      } else {
        
      }
    } else {
      
    }
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    statep <- (protect_ptr statep ms);
    hbsize <- (protect_64 hbsize ms);
    hsize <- (protect_64 hsize ms);
    padlen <- (protect_64 padlen ms);
    bad <- (protect_64 bad ms);
    statep <- (BArray32.set64 statep 0 hbsize);
    statep <- (BArray32.set64 statep 1 hsize);
    statep <- (BArray32.set64 statep 2 padlen);
    statep <- (BArray32.set64 statep 3 bad);
    return statep;
  }
  proc _unpack_sig_full (cp:BArray1024.t, lowp:BArray8192.t,
                         hbzp:BArray8192.t, hp:BArray8192.t, badp:BArray8.t,
                         sigp:BArray2948.t, h_symbolwp:BArray2048.t,
                         h_dsymswp:BArray528.t, hb_symbolwp:BArray2048.t,
                         hb_dsymswp:BArray528.t, lcount_i:int,
                         hb_count_i:int, hb_m_i:int, hb_offset_i:int,
                         h_count_i:int, h_m_i:int, h_offset_i:int,
                         base_hb_i:int, base_h_i:int, payload_limit_i:int) : 
  BArray1024.t * BArray8192.t * BArray8192.t * BArray8192.t * BArray8.t = {
    var hbenc:BArray2048.t;
    var hbencp:BArray2048.t;
    var henc:BArray2048.t;
    var hencp:BArray2048.t;
    var state:BArray32.t;
    var statep:BArray32.t;
    var lcount:W64.t;
    var suffix_off:W64.t;
    var base_hb:W64.t;
    var base_h:W64.t;
    var payload_limit:W64.t;
    var ms:W64.t;
    var hbsize:W64.t;
    var hsize:W64.t;
    var bad:W64.t;
    var enc_off:W64.t;
    var hb_count:W64.t;
    var hb_m:W64.t;
    var hb_offset:W64.t;
    var h_count:W64.t;
    var h_m:W64.t;
    var h_offset:W64.t;
    hbenc <- witness;
    hbencp <- witness;
    henc <- witness;
    hencp <- witness;
    state <- witness;
    statep <- witness;
    hbencp <- hbenc;
    hencp <- henc;
    statep <- state;
    lcount <- (W64.of_int lcount_i);
    (* Erased call to spill *)
    (cp, lowp) <@ _unpack_sig_prefix (cp, lowp, sigp, lcount);
    (* Erased call to unspill *)
    suffix_off <- lcount;
    suffix_off <- (suffix_off * (W64.of_int 256));
    suffix_off <- (suffix_off + (W64.of_int 32));
    base_hb <- (W64.of_int base_hb_i);
    base_h <- (W64.of_int base_h_i);
    payload_limit <- (W64.of_int payload_limit_i);
    (* Erased call to spill *)
    ms <- (init_msf);
    statep <- (protect_ptr statep ms);
    base_hb <- (protect_64 base_hb ms);
    base_h <- (protect_64 base_h ms);
    payload_limit <- (protect_64 payload_limit ms);
    statep <- (BArray32.set64 statep 0 base_hb);
    statep <- (BArray32.set64 statep 1 base_h);
    statep <- (BArray32.set64 statep 2 payload_limit);
    statep <- (BArray32.set64 statep 3 (W64.of_int 0));
    (* Erased call to unspill *)
    (* Erased call to spill *)
    statep <@ __unpack_sig_finish_at (statep, sigp, suffix_off);
    (* Erased call to unspill *)
    ms <- (init_msf);
    statep <- (protect_ptr statep ms);
    hbsize <- (BArray32.get64 statep 0);
    hsize <- (BArray32.get64 statep 1);
    bad <- (BArray32.get64 statep 3);
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    hbsize <- (protect_64 hbsize ms);
    hsize <- (protect_64 hsize ms);
    bad <- (protect_64 bad ms);
    if ((bad = (W64.of_int 0))) {
      enc_off <- suffix_off;
      enc_off <- (enc_off + (W64.of_int 2));
      hbencp <@ __copy_sig_slice (hbencp, sigp, enc_off, hbsize);
      enc_off <- (enc_off + hbsize);
      hencp <@ __copy_sig_slice (hencp, sigp, enc_off, hsize);
      hb_count <- (W64.of_int hb_count_i);
      hb_m <- (W64.of_int hb_m_i);
      hb_offset <- (W64.of_int hb_offset_i);
      (* Erased call to spill *)
      (hbzp, badp) <@ _decode_hb_z1_full (hbzp, badp, hbencp, hbsize,
      hb_symbolwp, hb_dsymswp, hb_count, hb_m, hb_offset);
      (* Erased call to unspill *)
      bad <- (BArray8.get64 badp 0);
      (* Erased call to declassify *)
      ms <- (init_msf);
      bad <- (protect_64 bad ms);
      if ((bad = (W64.of_int 0))) {
        h_count <- (W64.of_int h_count_i);
        h_m <- (W64.of_int h_m_i);
        h_offset <- (W64.of_int h_offset_i);
        (hp, badp) <@ _decode_h_full (hp, badp, hencp, hsize, h_symbolwp,
        h_dsymswp, h_count, h_m, h_offset);
        bad <- (BArray8.get64 badp 0);
        (* Erased call to declassify *)
        ms <- (init_msf);
        bad <- (protect_64 bad ms);
      } else {
        
      }
    } else {
      
    }
    ms <- (init_msf);
    badp <- (protect_ptr badp ms);
    bad <- (protect_64 bad ms);
    badp <- (BArray8.set64 badp 0 bad);
    return (cp, lowp, hbzp, hp, badp);
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
  proc __polymatkl_expand_matA_with_vecA (matp:BArray32768.t, seedp:int,
                                          rows:W64.t, cols:W64.t, m:W64.t) : 
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
      matp <@ _poly_uniform_at (matp, base, seedp, nonce);
      (* Erased call to unspill *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      ms <- (init_msf);
      matp <- (protect_ptr matp ms);
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
        matp <@ _poly_uniform_at (matp, base, seedp, nonce);
        (* Erased call to unspill *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        ms <- (init_msf);
        matp <- (protect_ptr matp ms);
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
  proc _unpack_vk_m23_full (matp:BArray32768.t, vkp:BArray2752.t, seedu:int,
                            k:W64.t, l:W64.t, m:W64.t) : BArray32768.t = {
    var b:BArray8192.t;
    var bp:BArray8192.t;
    var ms:W64.t;
    var count:W64.t;
    b <- witness;
    bp <- witness;
    bp <- b;
    bp <@ __unpack_vk_m23_coeffs (bp, vkp, k);
    (* Erased call to spill *)
    matp <@ __polymatkl_expand_matA_with_vecA (matp, seedu, k, l, m);
    (* Erased call to unspill *)
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    matp <- (protect_ptr matp ms);
    bp <- (protect_ptr bp ms);
    k <- (protect_64 k ms);
    l <- (protect_64 l ms);
    m <- (protect_64 m ms);
    matp <@ _polymatkl_double (matp, k, l);
    ms <- (init_msf);
    matp <- (protect_ptr matp ms);
    bp <- (protect_ptr bp ms);
    k <- (protect_64 k ms);
    l <- (protect_64 l ms);
    count <- k;
    count <- (count * (W64.of_int 256));
    count <- (protect_64 count ms);
    bp <@ _polyvec_double (bp, count);
    ms <- (init_msf);
    bp <- (protect_ptr bp ms);
    matp <- (protect_ptr matp ms);
    k <- (protect_64 k ms);
    l <- (protect_64 l ms);
    bp <@ __polyvec_sub_left_inplace (bp, matp, l, k);
    ms <- (init_msf);
    bp <- (protect_ptr bp ms);
    count <- (protect_64 count ms);
    bp <@ _polyvec_double (bp, count);
    (* Erased call to spill *)
    bp <@ _polyvec_ntt (bp, k);
    (* Erased call to unspill *)
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    matp <- (protect_ptr matp ms);
    bp <- (protect_ptr bp ms);
    k <- (protect_64 k ms);
    l <- (protect_64 l ms);
    matp <@ _polymat_set_first_column (matp, bp, k, l);
    return matp;
  }
  proc _unpack_vk_m5_full (matp:BArray32768.t, vkp:BArray2752.t, seedu:int,
                           k:W64.t, l:W64.t) : BArray32768.t = {
    var b:BArray8192.t;
    var bp:BArray8192.t;
    var ms:W64.t;
    b <- witness;
    bp <- witness;
    bp <- b;
    bp <@ __unpack_vk_m5_coeffs (bp, vkp, k);
    (* Erased call to spill *)
    matp <@ _polymatkl_expand_matA (matp, seedu, k, l);
    (* Erased call to unspill *)
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    matp <- (protect_ptr matp ms);
    bp <- (protect_ptr bp ms);
    k <- (protect_64 k ms);
    l <- (protect_64 l ms);
    matp <@ _polymatkl_double (matp, k, l);
    ms <- (init_msf);
    matp <- (protect_ptr matp ms);
    bp <- (protect_ptr bp ms);
    k <- (protect_64 k ms);
    l <- (protect_64 l ms);
    matp <@ _polymat_set_first_column (matp, bp, k, l);
    return matp;
  }
  proc _sign_verify_recover_w_z2 (wp_0:BArray8192.t, z2p:BArray8192.t,
                                  highp:BArray8192.t, hp:BArray8192.t,
                                  wprimep:BArray1024.t, count:W64.t,
                                  half_alpha:int, log_alpha:int, bound:int,
                                  alpha:int) : BArray8192.t * BArray8192.t = {
    var i:W64.t;
    var high:W32.t;
    var w:W32.t;
    var edge:W32.t;
    var sub:W32.t;
    var add:W32.t;
    var mask:W32.t;
    var z:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult count)) {
      high <- (BArray8192.get32 highp (W64.to_uint i));
      w <- high;
      w <- (w + (W32.of_int half_alpha));
      w <- (w `|>>` (W8.of_int log_alpha));
      edge <- (W32.of_int bound);
      edge <- (edge - w);
      edge <- (edge - (W32.of_int 1));
      edge <- (edge `|>>` (W8.of_int 31));
      sub <- edge;
      sub <- (sub `&` (W32.of_int bound));
      w <- (w - sub);
      add <- (BArray8192.get32 hp (W64.to_uint i));
      w <- (w + add);
      sub <- w;
      sub <- (sub - (W32.of_int bound));
      sub <- (sub `|>>` (W8.of_int 31));
      mask <- (W32.of_int 0);
      mask <- (mask - (W32.of_int 1));
      sub <- (sub `^` mask);
      sub <- (sub `&` (W32.of_int bound));
      w <- (w - sub);
      wp_0 <- (BArray8192.set32 wp_0 (W64.to_uint i) w);
      z <- w;
      z <- (z * (W32.of_int alpha));
      z <- (z - high);
      if ((i \ult (W64.of_int 256))) {
        add <- (BArray1024.get32 wprimep (W64.to_uint i));
        z <- (z + add);
      } else {
        
      }
      z <@ __reduce32_2q (z);
      z <- (z `|>>` (W8.of_int 1));
      z2p <- (BArray8192.set32 z2p (W64.to_uint i) z);
      i <- (i + (W64.of_int 1));
    }
    return (wp_0, z2p);
  }
  proc _sign_verify_norm_reject (z2p:BArray8192.t, z1norm:W64.t,
                                 kcount:W64.t, bound:W64.t) : W64.t = {
    var reject:W64.t;
    var z2norm:W64.t;
    var total:W64.t;
    var ms:W64.t;
    z2norm <@ _polyvec_sqnorm2 (z2p, kcount);
    total <- z1norm;
    total <- (total + z2norm);
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    total <- (protect_64 total ms);
    bound <- (protect_64 bound ms);
    reject <- (W64.of_int 0);
    if ((bound \ult total)) {
      reject <- (W64.of_int 1);
    } else {
      
    }
    return reject;
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
  proc __verify_shake256_absorb_raw (sp_0:BArray200.t, statep:BArray16.t,
                                     inp:W64.t, inlen:W64.t) : BArray200.t *
                                                               BArray16.t = {
    var ms:W64.t;
    var pos:W64.t;
    var lane:W64.t;
    var b:W8.t;
    var t:W64.t;
    var shift:W8.t;
    ms <- (init_msf);
    sp_0 <- (protect_ptr sp_0 ms);
    statep <- (protect_ptr statep ms);
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
        sp_0 <- (protect_ptr sp_0 ms);
        statep <- (protect_ptr statep ms);
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
  proc __verify_shake256_absorb_byte (sp_0:BArray200.t, statep:BArray16.t,
                                      b:W8.t) : BArray200.t * BArray16.t = {
    var ms:W64.t;
    var pos:W64.t;
    var lane:W64.t;
    var t:W64.t;
    var shift:W8.t;
    ms <- (init_msf);
    sp_0 <- (protect_ptr sp_0 ms);
    statep <- (protect_ptr statep ms);
    pos <- (BArray16.get64 statep 0);
    (* Erased call to declassify *)
    pos <- (protect_64 pos ms);
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
    if ((pos = (W64.of_int 136))) {
      (* Erased call to spill *)
      sp_0 <@ _keccakf1600 (sp_0);
      (* Erased call to unspill *)
      (* Erased call to declassify *)
      ms <- (init_msf);
      sp_0 <- (protect_ptr sp_0 ms);
      statep <- (protect_ptr statep ms);
      pos <- (protect_64 pos ms);
      pos <- (W64.of_int 0);
    } else {
      
    }
    ms <- (init_msf);
    statep <- (protect_ptr statep ms);
    statep <- (BArray16.set64 statep 0 pos);
    return (sp_0, statep);
  }
  proc __verify_shake256_absorb_buf (sp_0:BArray200.t, statep:BArray16.t,
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
    sp_0 <- (protect_ptr sp_0 ms);
    statep <- (protect_ptr statep ms);
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
        sp_0 <- (protect_ptr sp_0 ms);
        statep <- (protect_ptr statep ms);
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
  proc __verify_shake256_absorb_mu32 (sp_0:BArray200.t, statep:BArray16.t,
                                      inp:BArray32.t) : BArray200.t *
                                                        BArray16.t = {
    var ms:W64.t;
    var pos:W64.t;
    var i:W64.t;
    var lane:W64.t;
    var b:W8.t;
    var t:W64.t;
    var shift:W8.t;
    ms <- (init_msf);
    sp_0 <- (protect_ptr sp_0 ms);
    statep <- (protect_ptr statep ms);
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
    }
    ms <- (init_msf);
    statep <- (protect_ptr statep ms);
    statep <- (BArray16.set64 statep 0 pos);
    return (sp_0, statep);
  }
  proc __verify_zero_highbuf (bp:BArray1152.t, len:W64.t) : BArray1152.t = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult len)) {
      bp <- (BArray1152.set8 bp (W64.to_uint i) (W8.of_int 0));
      i <- (i + (W64.of_int 1));
    }
    return bp;
  }
  proc __verify_hash_mu (mup:BArray32.t, vkp:W64.t, prep:W64.t, prelen:W64.t,
                         mp:W64.t, mlen:W64.t, vklen:W64.t) : BArray32.t = {
    var state:BArray200.t;
    var sp_0:BArray200.t;
    var st:BArray16.t;
    var stp:BArray16.t;
    var inlen:W64.t;
    var ms:W64.t;
    var ctxflag:W64.t;
    var ctxlen:W64.t;
    var b:W8.t;
    sp_0 <- witness;
    st <- witness;
    state <- witness;
    stp <- witness;
    sp_0 <- state;
    stp <- st;
    stp <- (BArray16.set64 stp 0 (W64.of_int 0));
    stp <- (BArray16.set64 stp 1 (W64.of_int 136));
    sp_0 <@ _keccak_init_state (sp_0);
    inlen <- vklen;
    (* Erased call to spill *)
    (sp_0, stp) <@ __verify_shake256_absorb_raw (sp_0, stp, vkp, inlen);
    (* Erased call to unspill *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    prelen <- (protect_64 prelen ms);
    ctxflag <- prelen;
    ctxflag <- (ctxflag `>>` (W8.of_int 63));
    (* Erased call to declassify *)
    ms <- (init_msf);
    ctxflag <- (protect_64 ctxflag ms);
    if ((ctxflag = (W64.of_int 0))) {
      (* Erased call to spill *)
      (sp_0, stp) <@ __verify_shake256_absorb_raw (sp_0, stp, prep, prelen);
      (* Erased call to unspill *)
    } else {
      ctxlen <- prelen;
      ctxlen <- (ctxlen `<<` (W8.of_int 1));
      ctxlen <- (ctxlen `>>` (W8.of_int 1));
      (* Erased call to declassify *)
      ms <- (init_msf);
      ctxlen <- (protect_64 ctxlen ms);
      b <- (truncateu8 ctxlen);
      (* Erased call to spill *)
      (sp_0, stp) <@ __verify_shake256_absorb_byte (sp_0, stp, b);
      (* Erased call to unspill *)
      (* Erased call to spill *)
      (sp_0, stp) <@ __verify_shake256_absorb_raw (sp_0, stp, prep, ctxlen);
      (* Erased call to unspill *)
    }
    (sp_0, stp) <@ __verify_shake256_absorb_raw (sp_0, stp, mp, mlen);
    sp_0 <@ __poly_challenge_shake256_finalize (sp_0, stp);
    (mup, sp_0) <@ __poly_challenge_squeeze256_32 (mup, sp_0);
    return mup;
  }
  proc __verify_challenge_absorb (sp_0:BArray200.t, highp:BArray1152.t,
                                  highlen:W64.t, lsbp:BArray32.t,
                                  mup:BArray32.t) : BArray200.t = {
    var st:BArray16.t;
    var stp:BArray16.t;
    st <- witness;
    stp <- witness;
    stp <- st;
    stp <- (BArray16.set64 stp 0 (W64.of_int 0));
    stp <- (BArray16.set64 stp 1 (W64.of_int 136));
    sp_0 <@ _keccak_init_state (sp_0);
    (* Erased call to spill *)
    (sp_0, stp) <@ __verify_shake256_absorb_buf (sp_0, stp, highp, highlen);
    (* Erased call to unspill *)
    (* Erased call to spill *)
    (sp_0, stp) <@ __verify_shake256_absorb_mu32 (sp_0, stp, lsbp);
    (* Erased call to unspill *)
    (sp_0, stp) <@ __verify_shake256_absorb_mu32 (sp_0, stp, mup);
    sp_0 <@ __poly_challenge_shake256_finalize (sp_0, stp);
    return sp_0;
  }
  proc __verify_challenge_m23 (cp:BArray1024.t, highp:BArray1152.t,
                               highlen:W64.t, lsbp:BArray32.t,
                               mup:BArray32.t, tau:W64.t) : BArray1024.t = {
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
    sp_0 <@ __verify_challenge_absorb (sp_0, highp, highlen, lsbp, mup);
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
  proc __verify_challenge_m5 (cp:BArray1024.t, highp:BArray1152.t,
                              highlen:W64.t, lsbp:BArray32.t, mup:BArray32.t) : 
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
    sp_0 <@ __verify_challenge_absorb (sp_0, highp, highlen, lsbp, mup);
    (* Erased call to unspill *)
    (* Erased call to spill *)
    (bp, sp_0) <@ __poly_challenge_squeeze256_32 (bp, sp_0);
    (* Erased call to unspill *)
    ms <- (init_msf);
    cp <- (protect_ptr cp ms);
    cp <@ _poly_challenge_m5_frombytes (cp, bp);
    return cp;
  }
  proc _sign_verify_tail_m23 (wp_0:BArray8192.t, wprimep:BArray1024.t,
                              cp:BArray1024.t, descp:BArray40.t, k_i:int,
                              highbits_len_i:int, vklen_i:int, tau_i:int) : 
  W64.t = {
    var reject:W64.t;
    var ms:W64.t;
    var highbuf:BArray1152.t;
    var highp:BArray1152.t;
    var lsb:BArray32.t;
    var lsbp:BArray32.t;
    var mu:BArray32.t;
    var mup:BArray32.t;
    var cprime:BArray1024.t;
    var cprimep:BArray1024.t;
    var vkp:W64.t;
    var prep:W64.t;
    var prelen:W64.t;
    var mp:W64.t;
    var mlen:W64.t;
    var highlen:W64.t;
    var count:W64.t;
    var vklen:W64.t;
    var tau:W64.t;
    cprime <- witness;
    cprimep <- witness;
    highbuf <- witness;
    highp <- witness;
    lsb <- witness;
    lsbp <- witness;
    mu <- witness;
    mup <- witness;
    ms <- (init_msf);
    descp <- (protect_ptr descp ms);
    highp <- highbuf;
    lsbp <- lsb;
    mup <- mu;
    cprimep <- cprime;
    vkp <- (BArray40.get64 descp 0);
    prep <- (BArray40.get64 descp 1);
    prelen <- (BArray40.get64 descp 2);
    mp <- (BArray40.get64 descp 3);
    mlen <- (BArray40.get64 descp 4);
    highlen <- (W64.of_int highbits_len_i);
    (* Erased call to spill *)
    ms <- (init_msf);
    highp <- (protect_ptr highp ms);
    highlen <- (protect_64 highlen ms);
    highp <@ __verify_zero_highbuf (highp, highlen);
    (* Erased call to unspill *)
    count <- (W64.of_int k_i);
    (* Erased call to spill *)
    ms <- (init_msf);
    highp <- (protect_ptr highp ms);
    wp_0 <- (protect_ptr wp_0 ms);
    count <- (protect_64 count ms);
    highp <@ _pack_vec_highbits_m23 (highp, wp_0, count);
    (* Erased call to unspill *)
    (* Erased call to spill *)
    ms <- (init_msf);
    lsbp <- (protect_ptr lsbp ms);
    wprimep <- (protect_ptr wprimep ms);
    lsbp <@ _pack_poly_lsb (lsbp, wprimep);
    (* Erased call to unspill *)
    vklen <- (W64.of_int vklen_i);
    (* Erased call to spill *)
    ms <- (init_msf);
    mup <- (protect_ptr mup ms);
    mup <@ __verify_hash_mu (mup, vkp, prep, prelen, mp, mlen, vklen);
    (* Erased call to unspill *)
    tau <- (W64.of_int tau_i);
    (* Erased call to spill *)
    ms <- (init_msf);
    cprimep <- (protect_ptr cprimep ms);
    highp <- (protect_ptr highp ms);
    lsbp <- (protect_ptr lsbp ms);
    mup <- (protect_ptr mup ms);
    highlen <- (protect_64 highlen ms);
    tau <- (protect_64 tau ms);
    cprimep <@ __verify_challenge_m23 (cprimep, highp, highlen, lsbp, 
    mup, tau);
    (* Erased call to unspill *)
    ms <- (init_msf);
    cp <- (protect_ptr cp ms);
    cprimep <- (protect_ptr cprimep ms);
    reject <@ _poly_mismatch (cp, cprimep);
    return reject;
  }
  proc _sign_verify_tail_m5 (wp_0:BArray8192.t, wprimep:BArray1024.t,
                             cp:BArray1024.t, descp:BArray40.t) : W64.t = {
    var reject:W64.t;
    var ms:W64.t;
    var highbuf:BArray1152.t;
    var highp:BArray1152.t;
    var lsb:BArray32.t;
    var lsbp:BArray32.t;
    var mu:BArray32.t;
    var mup:BArray32.t;
    var cprime:BArray1024.t;
    var cprimep:BArray1024.t;
    var vkp:W64.t;
    var prep:W64.t;
    var prelen:W64.t;
    var mp:W64.t;
    var mlen:W64.t;
    var highlen:W64.t;
    var count:W64.t;
    var vklen:W64.t;
    cprime <- witness;
    cprimep <- witness;
    highbuf <- witness;
    highp <- witness;
    lsb <- witness;
    lsbp <- witness;
    mu <- witness;
    mup <- witness;
    ms <- (init_msf);
    descp <- (protect_ptr descp ms);
    highp <- highbuf;
    lsbp <- lsb;
    mup <- mu;
    cprimep <- cprime;
    vkp <- (BArray40.get64 descp 0);
    prep <- (BArray40.get64 descp 1);
    prelen <- (BArray40.get64 descp 2);
    mp <- (BArray40.get64 descp 3);
    mlen <- (BArray40.get64 descp 4);
    highlen <- (W64.of_int 1152);
    (* Erased call to spill *)
    ms <- (init_msf);
    highp <- (protect_ptr highp ms);
    highlen <- (protect_64 highlen ms);
    highp <@ __verify_zero_highbuf (highp, highlen);
    (* Erased call to unspill *)
    count <- (W64.of_int 4);
    (* Erased call to spill *)
    ms <- (init_msf);
    highp <- (protect_ptr highp ms);
    wp_0 <- (protect_ptr wp_0 ms);
    count <- (protect_64 count ms);
    highp <@ _pack_vec_highbits_m5 (highp, wp_0, count);
    (* Erased call to unspill *)
    (* Erased call to spill *)
    ms <- (init_msf);
    lsbp <- (protect_ptr lsbp ms);
    wprimep <- (protect_ptr wprimep ms);
    lsbp <@ _pack_poly_lsb (lsbp, wprimep);
    (* Erased call to unspill *)
    vklen <- (W64.of_int 2080);
    (* Erased call to spill *)
    ms <- (init_msf);
    mup <- (protect_ptr mup ms);
    mup <@ __verify_hash_mu (mup, vkp, prep, prelen, mp, mlen, vklen);
    (* Erased call to unspill *)
    (* Erased call to spill *)
    ms <- (init_msf);
    cprimep <- (protect_ptr cprimep ms);
    highp <- (protect_ptr highp ms);
    lsbp <- (protect_ptr lsbp ms);
    mup <- (protect_ptr mup ms);
    highlen <- (protect_64 highlen ms);
    cprimep <@ __verify_challenge_m5 (cprimep, highp, highlen, lsbp, mup);
    (* Erased call to unspill *)
    ms <- (init_msf);
    cp <- (protect_ptr cp ms);
    cprimep <- (protect_ptr cprimep ms);
    reject <@ _poly_mismatch (cp, cprimep);
    return reject;
  }
  proc _api_copy_raw_to_2752_prefix (dstp:BArray2752.t, srcp:int, len:int) : 
  BArray2752.t = {
    var b:W8.t;
    var i:int;
    var addr:int;
    i <- 0;
    while ((i < len)) {
      addr <- srcp;
      addr <- (addr + i);
      b <- (loadW8 Glob.mem addr);
      dstp <- (BArray2752.set8 dstp (W64.to_uint (W64.of_int i)) b);
      i <- (i + 1);
    }
    while ((i < 2752)) {
      dstp <-
      (BArray2752.set8 dstp (W64.to_uint (W64.of_int i)) (W8.of_int 0));
      i <- (i + 1);
    }
    return dstp;
  }
  proc _api_copy_raw_to_2948_prefix (dstp:BArray2948.t, srcp:int, len:int) : 
  BArray2948.t = {
    var b:W8.t;
    var i:int;
    var addr:int;
    i <- 0;
    while ((i < len)) {
      addr <- srcp;
      addr <- (addr + i);
      b <- (loadW8 Glob.mem addr);
      dstp <- (BArray2948.set8 dstp (W64.to_uint (W64.of_int i)) b);
      i <- (i + 1);
    }
    while ((i < 2948)) {
      dstp <-
      (BArray2948.set8 dstp (W64.to_uint (W64.of_int i)) (W8.of_int 0));
      i <- (i + 1);
    }
    return dstp;
  }
  proc _api_copy_raw_to_raw_len64 (dstp:int, srcp:int, len:W64.t) : int = {
    var srcbase:W64.t;
    var dstbase:W64.t;
    var i:W64.t;
    var src:W64.t;
    var dst:W64.t;
    var b:W8.t;
    srcbase <- (W64.of_int srcp);
    dstbase <- (W64.of_int dstp);
    i <- (W64.of_int 0);
    while ((i \ult len)) {
      src <- srcbase;
      src <- (src + i);
      dst <- dstbase;
      dst <- (dst + i);
      b <- (loadW8 Glob.mem (W64.to_uint src));
      Glob.mem <- (storeW8 Glob.mem (W64.to_uint dst) b);
      i <- (i + (W64.of_int 1));
    }
    return dstp;
  }
  proc _api_zero_raw_len64 (dstp:int, len:W64.t) : int = {
    var dstbase:W64.t;
    var i:W64.t;
    var dst:W64.t;
    dstbase <- (W64.of_int dstp);
    i <- (W64.of_int 0);
    while ((i \ult len)) {
      dst <- dstbase;
      dst <- (dst + i);
      Glob.mem <- (storeW8 Glob.mem (W64.to_uint dst) (W8.of_int 0));
      i <- (i + (W64.of_int 1));
    }
    return dstp;
  }
  proc _api_reject () : W64.t = {
    var r:W64.t;
    r <- (W64.of_int 0);
    r <- (r - (W64.of_int 1));
    return r;
  }
  proc _verify_prepare_z1_wprime (z1p:BArray8192.t, wprimep:BArray1024.t,
                                  highzp:BArray8192.t, lowzp:BArray8192.t,
                                  cp:BArray1024.t, lcount:W64.t) : BArray8192.t *
                                                                   BArray1024.t *
                                                                   W64.t = {
    var total:W64.t;
    var i:W64.t;
    var high:W32.t;
    var low:W32.t;
    var z:W32.t;
    var coeff:W64.t;
    var prod:W64.t;
    var c:W32.t;
    var w:W32.t;
    total <- (W64.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult lcount)) {
      high <- (BArray8192.get32 highzp (W64.to_uint i));
      low <- (BArray8192.get32 lowzp (W64.to_uint i));
      high <- (high `<<` (W8.of_int 8));
      z <- high;
      z <- (z + low);
      z1p <- (BArray8192.set32 z1p (W64.to_uint i) z);
      coeff <- (sigextu64 z);
      prod <- (coeff * coeff);
      total <- (total + prod);
      if ((i \ult (W64.of_int 256))) {
        c <- (BArray1024.get32 cp (W64.to_uint i));
        w <- z;
        w <- (w - c);
        w <- (w `&` (W32.of_int 1));
        wprimep <- (BArray1024.set32 wprimep (W64.to_uint i) w);
      } else {
        
      }
      i <- (i + (W64.of_int 1));
    }
    return (z1p, wprimep, total);
  }
  proc _verify_publish_reject (reject:W64.t) : W64.t = {
    var ms:W64.t;
    (* Erased call to declassify *)
    ms <- (init_msf);
    reject <- (protect_64 reject ms);
    return reject;
  }
  proc _verify_matrix_crt (z1p:BArray8192.t, highp:BArray8192.t,
                           a1p:BArray32768.t, wprimep:BArray1024.t,
                           rows:W64.t, cols:W64.t) : BArray8192.t *
                                                     BArray8192.t = {
    var ms:W64.t;
    var count:W64.t;
    (* Erased call to spill *)
    z1p <@ _polyvec_ntt (z1p, cols);
    (* Erased call to unspill *)
    ms <- (init_msf);
    highp <- (protect_ptr highp ms);
    a1p <- (protect_ptr a1p ms);
    z1p <- (protect_ptr z1p ms);
    rows <- (protect_64 rows ms);
    cols <- (protect_64 cols ms);
    highp <@ _polymat_pointwise_acc (highp, a1p, z1p, rows, cols);
    ms <- (init_msf);
    highp <- (protect_ptr highp ms);
    rows <- (protect_64 rows ms);
    highp <@ _polyvec_invntt (highp, rows);
    ms <- (init_msf);
    z1p <- (protect_ptr z1p ms);
    highp <- (protect_ptr highp ms);
    wprimep <- (protect_ptr wprimep ms);
    rows <- (protect_64 rows ms);
    z1p <@ _polyveck_poly_fromcrt (z1p, highp, wprimep, rows);
    count <- rows;
    count <- (count * (W64.of_int 256));
    ms <- (init_msf);
    z1p <- (protect_ptr z1p ms);
    count <- (protect_64 count ms);
    z1p <@ _polyvec_freeze2q (z1p, count);
    return (z1p, highp);
  }
  proc _verify_full_m23 (sigp:BArray2948.t, siglen:W64.t, vkp:BArray2752.t,
                         vku:int, descp:BArray40.t, k_i:int, l_i:int,
                         m_i:int, sigbytes_i:int, vkbytes_i:int,
                         highbits_len_i:int, tau_i:int, b2sq_i:int,
                         hb_count_i:int, hb_m_i:int, hb_offset_i:int,
                         h_count_i:int, h_m_i:int, h_offset_i:int,
                         base_hb_i:int, base_h_i:int, payload_limit_i:int) : 
  W64.t = {
    var reject:W64.t;
    var k:W64.t;
    var l:W64.t;
    var m:W64.t;
    var desc:BArray40.t;
    var copydescp:BArray40.t;
    var a1:BArray32768.t;
    var a1p:BArray32768.t;
    var h_symbolwp:BArray2048.t;
    var h_dsymswp:BArray528.t;
    var hb_symbolwp:BArray2048.t;
    var hb_dsymswp:BArray528.t;
    var c:BArray1024.t;
    var cp:BArray1024.t;
    var lowz:BArray8192.t;
    var lowzp:BArray8192.t;
    var highz:BArray8192.t;
    var highzp:BArray8192.t;
    var h:BArray8192.t;
    var hp:BArray8192.t;
    var bad:BArray8.t;
    var badp:BArray8.t;
    var ms:W64.t;
    var badv:W64.t;
    var z1:BArray8192.t;
    var z1p:BArray8192.t;
    var wprime:BArray1024.t;
    var wprimep:BArray1024.t;
    var lcount:W64.t;
    var sqnorm2:W64.t;
    var highbits:BArray8192.t;
    var highbitsp:BArray8192.t;
    var w:BArray8192.t;
    var wp_0:BArray8192.t;
    var z2:BArray8192.t;
    var z2p:BArray8192.t;
    var kcount:W64.t;
    var bound:W64.t;
    var taildescp:BArray40.t;
    a1 <- witness;
    a1p <- witness;
    bad <- witness;
    badp <- witness;
    c <- witness;
    copydescp <- witness;
    cp <- witness;
    desc <- witness;
    h <- witness;
    h_dsymswp <- witness;
    h_symbolwp <- witness;
    hb_dsymswp <- witness;
    hb_symbolwp <- witness;
    highbits <- witness;
    highbitsp <- witness;
    highz <- witness;
    highzp <- witness;
    hp <- witness;
    lowz <- witness;
    lowzp <- witness;
    taildescp <- witness;
    w <- witness;
    wp_0 <- witness;
    wprime <- witness;
    wprimep <- witness;
    z1 <- witness;
    z1p <- witness;
    z2 <- witness;
    z2p <- witness;
    if ((siglen <> (W64.of_int sigbytes_i))) {
      reject <- (W64.of_int 1);
    } else {
      k <- (W64.of_int k_i);
      l <- (W64.of_int l_i);
      m <- (W64.of_int m_i);
      copydescp <- desc;
      copydescp <- (BArray40.set64 copydescp 0 (BArray40.get64 descp 0));
      copydescp <- (BArray40.set64 copydescp 1 (BArray40.get64 descp 1));
      copydescp <- (BArray40.set64 copydescp 2 (BArray40.get64 descp 2));
      copydescp <- (BArray40.set64 copydescp 3 (BArray40.get64 descp 3));
      copydescp <- (BArray40.set64 copydescp 4 (BArray40.get64 descp 4));
      a1p <- a1;
      (* Erased call to spill *)
      a1p <@ _unpack_vk_m23_full (a1p, vkp, vku, k, l, m);
      (* Erased call to unspill *)
      h_symbolwp <- jmode2_h_symbol_words;
      h_dsymswp <- jmode2_h_dsyms_words;
      hb_symbolwp <- jmode2_hb_z1_symbol_words;
      hb_dsymswp <- jmode2_hb_z1_dsyms_words;
      if ((k_i = 3)) {
        h_symbolwp <- jmode3_h_symbol_words;
        h_dsymswp <- jmode3_h_dsyms_words;
        hb_symbolwp <- jmode3_hb_z1_symbol_words;
        hb_dsymswp <- jmode3_hb_z1_dsyms_words;
      } else {
        
      }
      cp <- c;
      lowzp <- lowz;
      highzp <- highz;
      hp <- h;
      badp <- bad;
      ms <- (init_msf);
      badp <- (protect_ptr badp ms);
      badp <- (BArray8.set64 badp 0 (W64.of_int 0));
      (* Erased call to spill *)
      ms <- (init_msf);
      cp <- (protect_ptr cp ms);
      lowzp <- (protect_ptr lowzp ms);
      highzp <- (protect_ptr highzp ms);
      hp <- (protect_ptr hp ms);
      badp <- (protect_ptr badp ms);
      sigp <- (protect_ptr sigp ms);
      (cp, lowzp, highzp, hp, badp) <@ _unpack_sig_full (cp, lowzp, highzp,
      hp, badp, sigp, h_symbolwp, h_dsymswp, hb_symbolwp, hb_dsymswp, 
      l_i, hb_count_i, hb_m_i, hb_offset_i, h_count_i, h_m_i, h_offset_i,
      base_hb_i, base_h_i, payload_limit_i);
      (* Erased call to unspill *)
      ms <- (init_msf);
      badp <- (protect_ptr badp ms);
      badv <- (BArray8.get64 badp 0);
      (* Erased call to declassify *)
      ms <- (init_msf);
      badv <- (protect_64 badv ms);
      if ((badv <> (W64.of_int 0))) {
        reject <- (W64.of_int 1);
      } else {
        z1p <- z1;
        wprimep <- wprime;
        lcount <- l;
        lcount <- (lcount * (W64.of_int 256));
        (* Erased call to spill *)
        ms <- (init_msf);
        z1p <- (protect_ptr z1p ms);
        wprimep <- (protect_ptr wprimep ms);
        highzp <- (protect_ptr highzp ms);
        lowzp <- (protect_ptr lowzp ms);
        cp <- (protect_ptr cp ms);
        lcount <- (protect_64 lcount ms);
        (z1p, wprimep, sqnorm2) <@ _verify_prepare_z1_wprime (z1p, wprimep,
        highzp, lowzp, cp, lcount);
        (* Erased call to unspill *)
        highbitsp <- highbits;
        ms <- (init_msf);
        z1p <- (protect_ptr z1p ms);
        highbitsp <- (protect_ptr highbitsp ms);
        a1p <- (protect_ptr a1p ms);
        wprimep <- (protect_ptr wprimep ms);
        k <- (protect_64 k ms);
        l <- (protect_64 l ms);
        (* Erased call to spill *)
        (z1p, highbitsp) <@ _verify_matrix_crt (z1p, highbitsp, a1p, 
        wprimep, k, l);
        (* Erased call to unspill *)
        wp_0 <- w;
        z2p <- z2;
        kcount <- k;
        kcount <- (kcount * (W64.of_int 256));
        ms <- (init_msf);
        wp_0 <- (protect_ptr wp_0 ms);
        z2p <- (protect_ptr z2p ms);
        z1p <- (protect_ptr z1p ms);
        hp <- (protect_ptr hp ms);
        wprimep <- (protect_ptr wprimep ms);
        kcount <- (protect_64 kcount ms);
        (* Erased call to spill *)
        (wp_0, z2p) <@ _sign_verify_recover_w_z2 (wp_0, z2p, z1p, hp,
        wprimep, kcount, 256, 9, 252, 512);
        (* Erased call to unspill *)
        bound <- (W64.of_int b2sq_i);
        ms <- (init_msf);
        z2p <- (protect_ptr z2p ms);
        sqnorm2 <- (protect_64 sqnorm2 ms);
        kcount <- (protect_64 kcount ms);
        bound <- (protect_64 bound ms);
        reject <@ _sign_verify_norm_reject (z2p, sqnorm2, kcount, bound);
        (* Erased call to declassify *)
        ms <- (init_msf);
        reject <- (protect_64 reject ms);
        if ((reject = (W64.of_int 0))) {
          taildescp <- copydescp;
          ms <- (init_msf);
          wp_0 <- (protect_ptr wp_0 ms);
          wprimep <- (protect_ptr wprimep ms);
          cp <- (protect_ptr cp ms);
          taildescp <- (protect_ptr taildescp ms);
          reject <@ _sign_verify_tail_m23 (wp_0, wprimep, cp, taildescp, 
          k_i, highbits_len_i, vkbytes_i, tau_i);
        } else {
          
        }
      }
    }
    return reject;
  }
  proc _verify_full_m5 (sigp:BArray2948.t, siglen:W64.t, vkp:BArray2752.t,
                        vku:int, descp:BArray40.t) : W64.t = {
    var reject:W64.t;
    var k:W64.t;
    var l:W64.t;
    var desc:BArray40.t;
    var copydescp:BArray40.t;
    var a1:BArray32768.t;
    var a1p:BArray32768.t;
    var h_symbolwp:BArray2048.t;
    var h_dsymswp:BArray528.t;
    var hb_symbolwp:BArray2048.t;
    var hb_dsymswp:BArray528.t;
    var c:BArray1024.t;
    var cp:BArray1024.t;
    var lowz:BArray8192.t;
    var lowzp:BArray8192.t;
    var highz:BArray8192.t;
    var highzp:BArray8192.t;
    var h:BArray8192.t;
    var hp:BArray8192.t;
    var bad:BArray8.t;
    var badp:BArray8.t;
    var ms:W64.t;
    var badv:W64.t;
    var z1:BArray8192.t;
    var z1p:BArray8192.t;
    var wprime:BArray1024.t;
    var wprimep:BArray1024.t;
    var lcount:W64.t;
    var sqnorm2:W64.t;
    var highbits:BArray8192.t;
    var highbitsp:BArray8192.t;
    var w:BArray8192.t;
    var wp_0:BArray8192.t;
    var z2:BArray8192.t;
    var z2p:BArray8192.t;
    var kcount:W64.t;
    var bound:W64.t;
    var taildescp:BArray40.t;
    a1 <- witness;
    a1p <- witness;
    bad <- witness;
    badp <- witness;
    c <- witness;
    copydescp <- witness;
    cp <- witness;
    desc <- witness;
    h <- witness;
    h_dsymswp <- witness;
    h_symbolwp <- witness;
    hb_dsymswp <- witness;
    hb_symbolwp <- witness;
    highbits <- witness;
    highbitsp <- witness;
    highz <- witness;
    highzp <- witness;
    hp <- witness;
    lowz <- witness;
    lowzp <- witness;
    taildescp <- witness;
    w <- witness;
    wp_0 <- witness;
    wprime <- witness;
    wprimep <- witness;
    z1 <- witness;
    z1p <- witness;
    z2 <- witness;
    z2p <- witness;
    if ((siglen <> (W64.of_int 2948))) {
      reject <- (W64.of_int 1);
    } else {
      k <- (W64.of_int 4);
      l <- (W64.of_int 7);
      copydescp <- desc;
      copydescp <- (BArray40.set64 copydescp 0 (BArray40.get64 descp 0));
      copydescp <- (BArray40.set64 copydescp 1 (BArray40.get64 descp 1));
      copydescp <- (BArray40.set64 copydescp 2 (BArray40.get64 descp 2));
      copydescp <- (BArray40.set64 copydescp 3 (BArray40.get64 descp 3));
      copydescp <- (BArray40.set64 copydescp 4 (BArray40.get64 descp 4));
      a1p <- a1;
      (* Erased call to spill *)
      a1p <@ _unpack_vk_m5_full (a1p, vkp, vku, k, l);
      (* Erased call to unspill *)
      h_symbolwp <- jmode5_h_symbol_words;
      h_dsymswp <- jmode5_h_dsyms_words;
      hb_symbolwp <- jmode5_hb_z1_symbol_words;
      hb_dsymswp <- jmode5_hb_z1_dsyms_words;
      cp <- c;
      lowzp <- lowz;
      highzp <- highz;
      hp <- h;
      badp <- bad;
      ms <- (init_msf);
      badp <- (protect_ptr badp ms);
      badp <- (BArray8.set64 badp 0 (W64.of_int 0));
      (* Erased call to spill *)
      ms <- (init_msf);
      cp <- (protect_ptr cp ms);
      lowzp <- (protect_ptr lowzp ms);
      highzp <- (protect_ptr highzp ms);
      hp <- (protect_ptr hp ms);
      badp <- (protect_ptr badp ms);
      sigp <- (protect_ptr sigp ms);
      (cp, lowzp, highzp, hp, badp) <@ _unpack_sig_full (cp, lowzp, highzp,
      hp, badp, sigp, h_symbolwp, h_dsymswp, hb_symbolwp, hb_dsymswp, 7,
      1792, 19, 9, 1024, 33, 471, 501, 358, 1122);
      (* Erased call to unspill *)
      ms <- (init_msf);
      badp <- (protect_ptr badp ms);
      badv <- (BArray8.get64 badp 0);
      (* Erased call to declassify *)
      ms <- (init_msf);
      badv <- (protect_64 badv ms);
      if ((badv <> (W64.of_int 0))) {
        reject <- (W64.of_int 1);
      } else {
        z1p <- z1;
        wprimep <- wprime;
        lcount <- l;
        lcount <- (lcount * (W64.of_int 256));
        (* Erased call to spill *)
        ms <- (init_msf);
        z1p <- (protect_ptr z1p ms);
        wprimep <- (protect_ptr wprimep ms);
        highzp <- (protect_ptr highzp ms);
        lowzp <- (protect_ptr lowzp ms);
        cp <- (protect_ptr cp ms);
        lcount <- (protect_64 lcount ms);
        (z1p, wprimep, sqnorm2) <@ _verify_prepare_z1_wprime (z1p, wprimep,
        highzp, lowzp, cp, lcount);
        (* Erased call to unspill *)
        highbitsp <- highbits;
        ms <- (init_msf);
        z1p <- (protect_ptr z1p ms);
        highbitsp <- (protect_ptr highbitsp ms);
        a1p <- (protect_ptr a1p ms);
        wprimep <- (protect_ptr wprimep ms);
        k <- (protect_64 k ms);
        l <- (protect_64 l ms);
        (* Erased call to spill *)
        (z1p, highbitsp) <@ _verify_matrix_crt (z1p, highbitsp, a1p, 
        wprimep, k, l);
        (* Erased call to unspill *)
        wp_0 <- w;
        z2p <- z2;
        kcount <- k;
        kcount <- (kcount * (W64.of_int 256));
        ms <- (init_msf);
        wp_0 <- (protect_ptr wp_0 ms);
        z2p <- (protect_ptr z2p ms);
        z1p <- (protect_ptr z1p ms);
        hp <- (protect_ptr hp ms);
        wprimep <- (protect_ptr wprimep ms);
        kcount <- (protect_64 kcount ms);
        (* Erased call to spill *)
        (wp_0, z2p) <@ _sign_verify_recover_w_z2 (wp_0, z2p, z1p, hp,
        wprimep, kcount, 128, 8, 504, 256);
        (* Erased call to unspill *)
        bound <- (W64.of_int 597386433);
        ms <- (init_msf);
        z2p <- (protect_ptr z2p ms);
        sqnorm2 <- (protect_64 sqnorm2 ms);
        kcount <- (protect_64 kcount ms);
        bound <- (protect_64 bound ms);
        reject <@ _sign_verify_norm_reject (z2p, sqnorm2, kcount, bound);
        (* Erased call to declassify *)
        ms <- (init_msf);
        reject <- (protect_64 reject ms);
        if ((reject = (W64.of_int 0))) {
          taildescp <- copydescp;
          ms <- (init_msf);
          wp_0 <- (protect_ptr wp_0 ms);
          wprimep <- (protect_ptr wprimep ms);
          cp <- (protect_ptr cp ms);
          taildescp <- (protect_ptr taildescp ms);
          reject <@ _sign_verify_tail_m5 (wp_0, wprimep, cp, taildescp);
        } else {
          
        }
      }
    }
    return reject;
  }
  proc _verify_full_mode2 (sigp:BArray2948.t, siglen:W64.t, vkp:BArray2752.t,
                           vku:int, descp:BArray40.t) : W64.t = {
    var reject:W64.t;
    reject <@ _verify_full_m23 (sigp, siglen, vkp, vku, descp, 2, 4, 3, 1474,
    992, 576, 58, 163265017, 1024, 13, 6, 512, 13, 239, 132, 7, 416);
    return reject;
  }
  proc _verify_full_mode3 (sigp:BArray2948.t, siglen:W64.t, vkp:BArray2752.t,
                           vku:int, descp:BArray40.t) : W64.t = {
    var reject:W64.t;
    reject <@ _verify_full_m23 (sigp, siglen, vkp, vku, descp, 3, 6, 5, 2349,
    1472, 864, 80, 479901314, 1536, 17, 8, 768, 17, 235, 376, 127, 779);
    return reject;
  }
  proc _verify_full_mode5 (sigp:BArray2948.t, siglen:W64.t, vkp:BArray2752.t,
                           vku:int, descp:BArray40.t) : W64.t = {
    var reject:W64.t;
    reject <@ _verify_full_m5 (sigp, siglen, vkp, vku, descp);
    return reject;
  }
  proc sign_verify_internal_mode2_jazz (sigp:BArray2948.t, siglen:W64.t,
                                        vkp:BArray2752.t, vku:int,
                                        descp:BArray40.t) : W64.t = {
    var reject:W64.t;
    var ms:W64.t;
    (* Erased call to declassify *)
    ms <- (init_msf);
    siglen <- (protect_64 siglen ms);
    reject <@ _verify_full_mode2 (sigp, siglen, vkp, vku, descp);
    return reject;
  }
  proc sign_verify_internal_mode3_jazz (sigp:BArray2948.t, siglen:W64.t,
                                        vkp:BArray2752.t, vku:int,
                                        descp:BArray40.t) : W64.t = {
    var reject:W64.t;
    var ms:W64.t;
    (* Erased call to declassify *)
    ms <- (init_msf);
    siglen <- (protect_64 siglen ms);
    reject <@ _verify_full_mode3 (sigp, siglen, vkp, vku, descp);
    return reject;
  }
  proc sign_verify_internal_mode5_jazz (sigp:BArray2948.t, siglen:W64.t,
                                        vkp:BArray2752.t, vku:int,
                                        descp:BArray40.t) : W64.t = {
    var reject:W64.t;
    var ms:W64.t;
    (* Erased call to declassify *)
    ms <- (init_msf);
    siglen <- (protect_64 siglen ms);
    reject <@ _verify_full_mode5 (sigp, siglen, vkp, vku, descp);
    return reject;
  }
  proc _api_verify_mode2_raw (sigu:int, siglen:W64.t, mu:W64.t, mlen:W64.t,
                              preu:W64.t, prelen:W64.t, vku:int) : W64.t = {
    var reject:W64.t;
    var sig:BArray2948.t;
    var sigp:BArray2948.t;
    var vk:BArray2752.t;
    var vkp:BArray2752.t;
    var desc:BArray40.t;
    var descp:BArray40.t;
    desc <- witness;
    descp <- witness;
    sig <- witness;
    sigp <- witness;
    vk <- witness;
    vkp <- witness;
    if ((siglen <> (W64.of_int 1474))) {
      reject <- (W64.of_int 1);
    } else {
      sigp <- sig;
      vkp <- vk;
      descp <- desc;
      sigp <@ _api_copy_raw_to_2948_prefix (sigp, sigu, 1474);
      (* Erased call to declassify *)
      vkp <@ _api_copy_raw_to_2752_prefix (vkp, vku, 992);
      (* Erased call to declassify *)
      descp <- (BArray40.set64 descp 0 (W64.of_int vku));
      descp <- (BArray40.set64 descp 1 preu);
      descp <- (BArray40.set64 descp 2 prelen);
      descp <- (BArray40.set64 descp 3 mu);
      descp <- (BArray40.set64 descp 4 mlen);
      reject <@ sign_verify_internal_mode2_jazz (sigp, (W64.of_int 1474),
      vkp, vku, descp);
    }
    return reject;
  }
  proc _api_verify_mode3_raw (sigu:int, siglen:W64.t, mu:W64.t, mlen:W64.t,
                              preu:W64.t, prelen:W64.t, vku:int) : W64.t = {
    var reject:W64.t;
    var sig:BArray2948.t;
    var sigp:BArray2948.t;
    var vk:BArray2752.t;
    var vkp:BArray2752.t;
    var desc:BArray40.t;
    var descp:BArray40.t;
    desc <- witness;
    descp <- witness;
    sig <- witness;
    sigp <- witness;
    vk <- witness;
    vkp <- witness;
    if ((siglen <> (W64.of_int 2349))) {
      reject <- (W64.of_int 1);
    } else {
      sigp <- sig;
      vkp <- vk;
      descp <- desc;
      sigp <@ _api_copy_raw_to_2948_prefix (sigp, sigu, 2349);
      (* Erased call to declassify *)
      vkp <@ _api_copy_raw_to_2752_prefix (vkp, vku, 1472);
      (* Erased call to declassify *)
      descp <- (BArray40.set64 descp 0 (W64.of_int vku));
      descp <- (BArray40.set64 descp 1 preu);
      descp <- (BArray40.set64 descp 2 prelen);
      descp <- (BArray40.set64 descp 3 mu);
      descp <- (BArray40.set64 descp 4 mlen);
      reject <@ sign_verify_internal_mode3_jazz (sigp, (W64.of_int 2349),
      vkp, vku, descp);
    }
    return reject;
  }
  proc _api_verify_mode5_raw (sigu:int, siglen:W64.t, mu:W64.t, mlen:W64.t,
                              preu:W64.t, prelen:W64.t, vku:int) : W64.t = {
    var reject:W64.t;
    var sig:BArray2948.t;
    var sigp:BArray2948.t;
    var vk:BArray2752.t;
    var vkp:BArray2752.t;
    var desc:BArray40.t;
    var descp:BArray40.t;
    desc <- witness;
    descp <- witness;
    sig <- witness;
    sigp <- witness;
    vk <- witness;
    vkp <- witness;
    if ((siglen <> (W64.of_int 2948))) {
      reject <- (W64.of_int 1);
    } else {
      sigp <- sig;
      vkp <- vk;
      descp <- desc;
      sigp <@ _api_copy_raw_to_2948_prefix (sigp, sigu, 2948);
      (* Erased call to declassify *)
      vkp <@ _api_copy_raw_to_2752_prefix (vkp, vku, 2080);
      (* Erased call to declassify *)
      descp <- (BArray40.set64 descp 0 (W64.of_int vku));
      descp <- (BArray40.set64 descp 1 preu);
      descp <- (BArray40.set64 descp 2 prelen);
      descp <- (BArray40.set64 descp 3 mu);
      descp <- (BArray40.set64 descp 4 mlen);
      reject <@ sign_verify_internal_mode5_jazz (sigp, (W64.of_int 2948),
      vkp, vku, descp);
    }
    return reject;
  }
  proc cryptolab_haetae_mode2_verify_internal_desc (sigu:int, vku:int,
                                                    apip:BArray40.t) : 
  W64.t = {
    var r:W64.t;
    var ms:W64.t;
    var siglen:W64.t;
    var maddr:W64.t;
    var mlen:W64.t;
    var preaddr:W64.t;
    var prelen:W64.t;
    var reject:W64.t;
    (* Erased call to declassify *)
    ms <- (init_msf);
    apip <- (protect_ptr apip ms);
    siglen <- (BArray40.get64 apip 0);
    maddr <- (BArray40.get64 apip 1);
    mlen <- (BArray40.get64 apip 2);
    preaddr <- (BArray40.get64 apip 3);
    prelen <- (BArray40.get64 apip 4);
    reject <@ _api_verify_mode2_raw (sigu, siglen, maddr, mlen, preaddr,
    prelen, vku);
    reject <@ _verify_publish_reject (reject);
    if ((reject = (W64.of_int 0))) {
      r <- (W64.of_int 0);
    } else {
      r <@ _api_reject ();
    }
    return r;
  }
  proc cryptolab_haetae_mode3_verify_internal_desc (sigu:int, vku:int,
                                                    apip:BArray40.t) : 
  W64.t = {
    var r:W64.t;
    var ms:W64.t;
    var siglen:W64.t;
    var maddr:W64.t;
    var mlen:W64.t;
    var preaddr:W64.t;
    var prelen:W64.t;
    var reject:W64.t;
    (* Erased call to declassify *)
    ms <- (init_msf);
    apip <- (protect_ptr apip ms);
    siglen <- (BArray40.get64 apip 0);
    maddr <- (BArray40.get64 apip 1);
    mlen <- (BArray40.get64 apip 2);
    preaddr <- (BArray40.get64 apip 3);
    prelen <- (BArray40.get64 apip 4);
    reject <@ _api_verify_mode3_raw (sigu, siglen, maddr, mlen, preaddr,
    prelen, vku);
    reject <@ _verify_publish_reject (reject);
    if ((reject = (W64.of_int 0))) {
      r <- (W64.of_int 0);
    } else {
      r <@ _api_reject ();
    }
    return r;
  }
  proc cryptolab_haetae_mode5_verify_internal_desc (sigu:int, vku:int,
                                                    apip:BArray40.t) : 
  W64.t = {
    var r:W64.t;
    var ms:W64.t;
    var siglen:W64.t;
    var maddr:W64.t;
    var mlen:W64.t;
    var preaddr:W64.t;
    var prelen:W64.t;
    var reject:W64.t;
    (* Erased call to declassify *)
    ms <- (init_msf);
    apip <- (protect_ptr apip ms);
    siglen <- (BArray40.get64 apip 0);
    maddr <- (BArray40.get64 apip 1);
    mlen <- (BArray40.get64 apip 2);
    preaddr <- (BArray40.get64 apip 3);
    prelen <- (BArray40.get64 apip 4);
    reject <@ _api_verify_mode5_raw (sigu, siglen, maddr, mlen, preaddr,
    prelen, vku);
    reject <@ _verify_publish_reject (reject);
    if ((reject = (W64.of_int 0))) {
      r <- (W64.of_int 0);
    } else {
      r <@ _api_reject ();
    }
    return r;
  }
  proc cryptolab_haetae_mode2_verify_desc (sigu:int, vku:int, apip:BArray40.t) : 
  W64.t = {
    var r:W64.t;
    var ms:W64.t;
    var siglen:W64.t;
    var maddr:W64.t;
    var mlen:W64.t;
    var ctxaddr:W64.t;
    var ctxlen:W64.t;
    var prelen:W64.t;
    var flag:W64.t;
    var reject:W64.t;
    (* Erased call to declassify *)
    ms <- (init_msf);
    apip <- (protect_ptr apip ms);
    siglen <- (BArray40.get64 apip 0);
    maddr <- (BArray40.get64 apip 1);
    mlen <- (BArray40.get64 apip 2);
    ctxaddr <- (BArray40.get64 apip 3);
    ctxlen <- (BArray40.get64 apip 4);
    if (((W64.of_int 255) \ult ctxlen)) {
      r <@ _api_reject ();
    } else {
      prelen <- ctxlen;
      flag <- (W64.of_int 1);
      flag <- (flag `<<` (W8.of_int 63));
      prelen <- (prelen + flag);
      reject <@ _api_verify_mode2_raw (sigu, siglen, maddr, mlen, ctxaddr,
      prelen, vku);
      reject <@ _verify_publish_reject (reject);
      if ((reject = (W64.of_int 0))) {
        r <- (W64.of_int 0);
      } else {
        r <@ _api_reject ();
      }
    }
    return r;
  }
  proc cryptolab_haetae_mode3_verify_desc (sigu:int, vku:int, apip:BArray40.t) : 
  W64.t = {
    var r:W64.t;
    var ms:W64.t;
    var siglen:W64.t;
    var maddr:W64.t;
    var mlen:W64.t;
    var ctxaddr:W64.t;
    var ctxlen:W64.t;
    var prelen:W64.t;
    var flag:W64.t;
    var reject:W64.t;
    (* Erased call to declassify *)
    ms <- (init_msf);
    apip <- (protect_ptr apip ms);
    siglen <- (BArray40.get64 apip 0);
    maddr <- (BArray40.get64 apip 1);
    mlen <- (BArray40.get64 apip 2);
    ctxaddr <- (BArray40.get64 apip 3);
    ctxlen <- (BArray40.get64 apip 4);
    if (((W64.of_int 255) \ult ctxlen)) {
      r <@ _api_reject ();
    } else {
      prelen <- ctxlen;
      flag <- (W64.of_int 1);
      flag <- (flag `<<` (W8.of_int 63));
      prelen <- (prelen + flag);
      reject <@ _api_verify_mode3_raw (sigu, siglen, maddr, mlen, ctxaddr,
      prelen, vku);
      reject <@ _verify_publish_reject (reject);
      if ((reject = (W64.of_int 0))) {
        r <- (W64.of_int 0);
      } else {
        r <@ _api_reject ();
      }
    }
    return r;
  }
  proc cryptolab_haetae_mode5_verify_desc (sigu:int, vku:int, apip:BArray40.t) : 
  W64.t = {
    var r:W64.t;
    var ms:W64.t;
    var siglen:W64.t;
    var maddr:W64.t;
    var mlen:W64.t;
    var ctxaddr:W64.t;
    var ctxlen:W64.t;
    var prelen:W64.t;
    var flag:W64.t;
    var reject:W64.t;
    (* Erased call to declassify *)
    ms <- (init_msf);
    apip <- (protect_ptr apip ms);
    siglen <- (BArray40.get64 apip 0);
    maddr <- (BArray40.get64 apip 1);
    mlen <- (BArray40.get64 apip 2);
    ctxaddr <- (BArray40.get64 apip 3);
    ctxlen <- (BArray40.get64 apip 4);
    if (((W64.of_int 255) \ult ctxlen)) {
      r <@ _api_reject ();
    } else {
      prelen <- ctxlen;
      flag <- (W64.of_int 1);
      flag <- (flag `<<` (W8.of_int 63));
      prelen <- (prelen + flag);
      reject <@ _api_verify_mode5_raw (sigu, siglen, maddr, mlen, ctxaddr,
      prelen, vku);
      reject <@ _verify_publish_reject (reject);
      if ((reject = (W64.of_int 0))) {
        r <- (W64.of_int 0);
      } else {
        r <@ _api_reject ();
      }
    }
    return r;
  }
  proc cryptolab_haetae_mode2_open_desc (mu:int, mlenu:int, smu:int, vku:int,
                                         apip:BArray24.t) : W64.t = {
    var r:W64.t;
    var ms:W64.t;
    var smlen:W64.t;
    var ctxaddr:W64.t;
    var ctxlen:W64.t;
    var mlen:W64.t;
    var prelen:W64.t;
    var flag:W64.t;
    var reject:W64.t;
    var badlen:W64.t;
    var msgu:int;
    (* Erased call to declassify *)
    ms <- (init_msf);
    apip <- (protect_ptr apip ms);
    smlen <- (BArray24.get64 apip 0);
    ctxaddr <- (BArray24.get64 apip 1);
    ctxlen <- (BArray24.get64 apip 2);
    if ((smlen \ult (W64.of_int 1474))) {
      badlen <- (W64.of_int 0);
      badlen <- (badlen - (W64.of_int 1));
      Glob.mem <- (storeW64 Glob.mem mlenu badlen);
      mu <@ _api_zero_raw_len64 (mu, smlen);
      r <@ _api_reject ();
    } else {
      mlen <- smlen;
      mlen <- (mlen - (W64.of_int 1474));
      msgu <- smu;
      msgu <- (msgu + 1474);
      if (((W64.of_int 255) \ult ctxlen)) {
        reject <- (W64.of_int 1);
      } else {
        prelen <- ctxlen;
        flag <- (W64.of_int 1);
        flag <- (flag `<<` (W8.of_int 63));
        prelen <- (prelen + flag);
        reject <@ _api_verify_mode2_raw (smu, (W64.of_int 1474),
        (W64.of_int msgu), mlen, ctxaddr, prelen, vku);
      }
      reject <@ _verify_publish_reject (reject);
      if ((reject = (W64.of_int 0))) {
        Glob.mem <- (storeW64 Glob.mem mlenu mlen);
        mu <@ _api_copy_raw_to_raw_len64 (mu, msgu, mlen);
        r <- (W64.of_int 0);
      } else {
        badlen <- (W64.of_int 0);
        badlen <- (badlen - (W64.of_int 1));
        Glob.mem <- (storeW64 Glob.mem mlenu badlen);
        mu <@ _api_zero_raw_len64 (mu, smlen);
        r <@ _api_reject ();
      }
    }
    return r;
  }
  proc cryptolab_haetae_mode3_open_desc (mu:int, mlenu:int, smu:int, vku:int,
                                         apip:BArray24.t) : W64.t = {
    var r:W64.t;
    var ms:W64.t;
    var smlen:W64.t;
    var ctxaddr:W64.t;
    var ctxlen:W64.t;
    var mlen:W64.t;
    var prelen:W64.t;
    var flag:W64.t;
    var reject:W64.t;
    var badlen:W64.t;
    var msgu:int;
    (* Erased call to declassify *)
    ms <- (init_msf);
    apip <- (protect_ptr apip ms);
    smlen <- (BArray24.get64 apip 0);
    ctxaddr <- (BArray24.get64 apip 1);
    ctxlen <- (BArray24.get64 apip 2);
    if ((smlen \ult (W64.of_int 2349))) {
      badlen <- (W64.of_int 0);
      badlen <- (badlen - (W64.of_int 1));
      Glob.mem <- (storeW64 Glob.mem mlenu badlen);
      mu <@ _api_zero_raw_len64 (mu, smlen);
      r <@ _api_reject ();
    } else {
      mlen <- smlen;
      mlen <- (mlen - (W64.of_int 2349));
      msgu <- smu;
      msgu <- (msgu + 2349);
      if (((W64.of_int 255) \ult ctxlen)) {
        reject <- (W64.of_int 1);
      } else {
        prelen <- ctxlen;
        flag <- (W64.of_int 1);
        flag <- (flag `<<` (W8.of_int 63));
        prelen <- (prelen + flag);
        reject <@ _api_verify_mode3_raw (smu, (W64.of_int 2349),
        (W64.of_int msgu), mlen, ctxaddr, prelen, vku);
      }
      reject <@ _verify_publish_reject (reject);
      if ((reject = (W64.of_int 0))) {
        Glob.mem <- (storeW64 Glob.mem mlenu mlen);
        mu <@ _api_copy_raw_to_raw_len64 (mu, msgu, mlen);
        r <- (W64.of_int 0);
      } else {
        badlen <- (W64.of_int 0);
        badlen <- (badlen - (W64.of_int 1));
        Glob.mem <- (storeW64 Glob.mem mlenu badlen);
        mu <@ _api_zero_raw_len64 (mu, smlen);
        r <@ _api_reject ();
      }
    }
    return r;
  }
  proc cryptolab_haetae_mode5_open_desc (mu:int, mlenu:int, smu:int, vku:int,
                                         apip:BArray24.t) : W64.t = {
    var r:W64.t;
    var ms:W64.t;
    var smlen:W64.t;
    var ctxaddr:W64.t;
    var ctxlen:W64.t;
    var mlen:W64.t;
    var prelen:W64.t;
    var flag:W64.t;
    var reject:W64.t;
    var badlen:W64.t;
    var msgu:int;
    (* Erased call to declassify *)
    ms <- (init_msf);
    apip <- (protect_ptr apip ms);
    smlen <- (BArray24.get64 apip 0);
    ctxaddr <- (BArray24.get64 apip 1);
    ctxlen <- (BArray24.get64 apip 2);
    if ((smlen \ult (W64.of_int 2948))) {
      badlen <- (W64.of_int 0);
      badlen <- (badlen - (W64.of_int 1));
      Glob.mem <- (storeW64 Glob.mem mlenu badlen);
      mu <@ _api_zero_raw_len64 (mu, smlen);
      r <@ _api_reject ();
    } else {
      mlen <- smlen;
      mlen <- (mlen - (W64.of_int 2948));
      msgu <- smu;
      msgu <- (msgu + 2948);
      if (((W64.of_int 255) \ult ctxlen)) {
        reject <- (W64.of_int 1);
      } else {
        prelen <- ctxlen;
        flag <- (W64.of_int 1);
        flag <- (flag `<<` (W8.of_int 63));
        prelen <- (prelen + flag);
        reject <@ _api_verify_mode5_raw (smu, (W64.of_int 2948),
        (W64.of_int msgu), mlen, ctxaddr, prelen, vku);
      }
      reject <@ _verify_publish_reject (reject);
      if ((reject = (W64.of_int 0))) {
        Glob.mem <- (storeW64 Glob.mem mlenu mlen);
        mu <@ _api_copy_raw_to_raw_len64 (mu, msgu, mlen);
        r <- (W64.of_int 0);
      } else {
        badlen <- (W64.of_int 0);
        badlen <- (badlen - (W64.of_int 1));
        Glob.mem <- (storeW64 Glob.mem mlenu badlen);
        mu <@ _api_zero_raw_len64 (mu, smlen);
        r <@ _api_reject ();
      }
    }
    return r;
  }
}.
