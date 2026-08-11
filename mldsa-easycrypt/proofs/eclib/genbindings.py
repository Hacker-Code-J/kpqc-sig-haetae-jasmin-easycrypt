#! /usr/bin/env python3

# --------------------------------------------------------------------
import itertools as it

# --------------------------------------------------------------------
def _main():
    for r in (2, 4, 8, 16, 32):
        for w in (16, 32, 64, 128, 256):
            if r * w > 256:
                continue

            t = r*w

            print(rf'''
(* -------------------------------------------------------------------- *)
clone BS_WB_WS as BS_W{r}u{w} with
      op sizeS <- {w:3},
      op sizeB <- {t:3},
      op r     <- {r:3},
  theory WS    <- W{w:<3}  {{ rename "_XX" as "_{w}" }},
  theory WSE   <- WE{w:<3} {{ rename "_XX" as "_{w}" }},
  theory WB    <- W{t:<3}  {{ rename "_XX" as "_{r*w}" }},
  theory WBE   <- WE{t:<3} {{ rename "_XX" as "_{r*w}" }},
  theory BSWS  <- BSW{w},
  theory BSWB  <- BSW{t},
  theory W_WS  <- W{r}u{w}
                    {{ rename "'Ru'S" as "{r}u{w}"
                             "'R"    as "{r}"
                             "'S"    as "{w}"
                             "'B"    as "{t}" }}.''')

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
