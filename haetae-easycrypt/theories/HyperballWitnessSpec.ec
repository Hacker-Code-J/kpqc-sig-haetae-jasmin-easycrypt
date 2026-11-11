require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import BArray26 BArray512 BArray8192 BArray32768 HyperballFixedPointSpec HyperballReferenceConstants.

(* Fixed input witnesses and expected observations from the existing numerical
   replay. The values below are definitions, not correctness assumptions;
   separate checked lemmas derive every observation from the actual calls. *)
op hbw_mode (mode : int) : bool = mode=2 \/ mode=3 \/ mode=5.
op hbw_count mode : int = 256*(hb_ref_l mode + hb_ref_k mode).
op hbw_left mode : int = 256*hb_ref_l mode.
op hbw_events mode : int = hbw_count mode+2.

op hbw_candidate (mode : int) : BArray26.t =
  if mode=2 then BArray26.of_list (map W8.of_int [240; 43; 155; 234; 178; 250; 128; 227; 44; 255; 7; 1; 0; 0; 0; 0; 0; 250; 12; 100; 193; 126; 157; 5; 29; 104])
  else if mode=3 then BArray26.of_list (map W8.of_int [133; 102; 108; 88; 214; 255; 255; 255; 255; 255; 7; 1; 0; 0; 0; 0; 0; 230; 130; 72; 13; 94; 132; 211; 188; 108])
  else if mode=5 then BArray26.of_list (map W8.of_int [1; 55; 229; 171; 26; 116; 30; 76; 59; 240; 7; 1; 0; 0; 0; 0; 0; 48; 67; 117; 21; 162; 177; 82; 22; 160])
  else BArray26.of_list [].

op hbw_sample (mode : int) : W64.t =
  if mode=2 then W64.of_int 4136588167694172516
  else if mode=3 then W64.of_int 8893690980794764617
  else if mode=5 then W64.of_int 3143537084327925109
  else W64.zero.

op hbw_square (mode : int) : hb_fp =
  if mode=2 then (W64.of_int 140509563513772, W64.of_int 3455611969)
  else if mode=3 then (W64.of_int 262880264445775, W64.of_int 15973661233)
  else if mode=5 then (W64.of_int 17372889325272, W64.of_int 1995618747)
  else (W64.zero,W64.zero).

op hbw_half (mode : int) : hb_fp =
  if mode=2 then (W64.of_int 246938261909420, W64.of_int 2657365604544)
  else if mode=3 then (W64.of_int 233869965312719, W64.of_int 18417631402725)
  else if mode=5 then (W64.of_int 271553062191832, W64.of_int 2811826814609)
  else (W64.zero,W64.zero).

op hbw_first (mode : int) : hb_fp =
  if mode=2 then (W64.of_int 331270931819935, W64.of_int 18446744073675761646)
  else if mode=3 then (W64.of_int 241583609198600, W64.of_int 18446744073551616452)
  else if mode=5 then (W64.of_int 333906974325571, W64.of_int 18446744073698340199)
  else (W64.zero,W64.zero).

op hbw_inverse (mode : int) : hb_fp =
  if mode=2 then (W64.of_int 101666530011624, W64.of_int 17352118948918032670)
  else if mode=3 then (W64.of_int 101443927918593, W64.of_int 6515027660407619326)
  else if mode=5 then (W64.of_int 51879773209874, W64.of_int 14033702225847268899)
  else (W64.zero,W64.zero).

op hbw_scale (mode : int) : hb_fp =
  if mode=2 then (W64.of_int 265747297086624, W64.of_int 14053931103413738628)
  else if mode=3 then (W64.of_int 42658744122560, W64.of_int 9079590807424815727)
  else if mode=5 then (W64.of_int 182753957924859, W64.of_int 6560330886008659858)
  else (W64.zero,W64.zero).

op hbw_sum (mode : int) : hb_fp =
  if mode=2 then (W64.of_int 212401547108184, W64.of_int 5314731209089)
  else if mode=3 then (W64.of_int 186264953914782, W64.of_int 36835262805451)
  else if mode=5 then (W64.of_int 261631147673008, W64.of_int 5623653629219)
  else (W64.zero,W64.zero).

op hbw_coefficient (mode : int) : int =
  if mode=2 then -1704795102
  else if mode=3 then -334802028
  else if mode=5 then -632138900
  else 0.

op hbw_total (mode : int) : int =
  if mode=2 then 4464117257937700460544
  else if mode=3 then 258260884883511054336
  else if mode=5 then 1125272442323279360000
  else 0.

op hbw_quotient (mode : int) : int =
  if mode=2 then 242
  else if mode=3 then 14
  else if mode=5 then 61
  else 0.

op hbw_residue (mode : int) : int =
  if mode=2 then 5192099988969472
  else if mode=3 then 6467851577331712
  else if mode=5 then 21053826996711424
  else 0.

op hbw_signs : BArray512.t = BArray512.init (fun _ => W8.zero).
op hbw_zero_output : BArray8192.t = BArray8192.init (fun _ => W8.zero).
op hbw_samples (mode : int) : BArray32768.t =
  BArray32768.init (fun j => if j < 8*hbw_count mode
    then hbw_sample mode \bits8 (j %% 8) else W8.zero).
