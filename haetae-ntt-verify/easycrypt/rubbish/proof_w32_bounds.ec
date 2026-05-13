require import AllCore.
from Jasmin require import JWord.

lemma w32_min_sintE : W32.min_sint = -2147483648.
proof.
rewrite /W32.min_sint.
have -> : W32.size = 32 by done.
by [].
qed.

lemma w32_max_sintE : W32.max_sint = 2147483647.
proof.
rewrite /W32.max_sint.
have -> : W32.size = 32 by done.
by [].
qed.
