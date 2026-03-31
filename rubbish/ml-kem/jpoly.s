	.att_syntax
	.text
	.p2align	5
	.global	_poly_ntt_jazz
	.global	poly_ntt_jazz
_poly_ntt_jazz:
poly_ntt_jazz:
	.file 1 "jpoly.jazz"
	.loc 1 2 21
	movq	%rsp, %rax
	.loc 1 2 21
	leaq	-552(%rsp), %rsp
	.loc 1 2 21
	andq	$-8, %rsp
	.loc 1 2 21
	movq	%rbx, 512(%rsp)
	.loc 1 2 21
	movq	%rbp, 520(%rsp)
	.loc 1 2 21
	movq	%r12, 528(%rsp)
	.loc 1 2 21
	movq	%r13, 536(%rsp)
	.loc 1 2 21
	movq	%rax, 544(%rsp)
	.loc 1 11 4
	movw	(%rdi), %ax
	.loc 1 12 4
	movw	%ax, (%rsp)
	.loc 1 11 4
	movw	2(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 2(%rsp)
	.loc 1 11 4
	movw	4(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 4(%rsp)
	.loc 1 11 4
	movw	6(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 6(%rsp)
	.loc 1 11 4
	movw	8(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 8(%rsp)
	.loc 1 11 4
	movw	10(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 10(%rsp)
	.loc 1 11 4
	movw	12(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 12(%rsp)
	.loc 1 11 4
	movw	14(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 14(%rsp)
	.loc 1 11 4
	movw	16(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 16(%rsp)
	.loc 1 11 4
	movw	18(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 18(%rsp)
	.loc 1 11 4
	movw	20(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 20(%rsp)
	.loc 1 11 4
	movw	22(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 22(%rsp)
	.loc 1 11 4
	movw	24(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 24(%rsp)
	.loc 1 11 4
	movw	26(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 26(%rsp)
	.loc 1 11 4
	movw	28(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 28(%rsp)
	.loc 1 11 4
	movw	30(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 30(%rsp)
	.loc 1 11 4
	movw	32(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 32(%rsp)
	.loc 1 11 4
	movw	34(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 34(%rsp)
	.loc 1 11 4
	movw	36(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 36(%rsp)
	.loc 1 11 4
	movw	38(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 38(%rsp)
	.loc 1 11 4
	movw	40(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 40(%rsp)
	.loc 1 11 4
	movw	42(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 42(%rsp)
	.loc 1 11 4
	movw	44(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 44(%rsp)
	.loc 1 11 4
	movw	46(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 46(%rsp)
	.loc 1 11 4
	movw	48(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 48(%rsp)
	.loc 1 11 4
	movw	50(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 50(%rsp)
	.loc 1 11 4
	movw	52(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 52(%rsp)
	.loc 1 11 4
	movw	54(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 54(%rsp)
	.loc 1 11 4
	movw	56(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 56(%rsp)
	.loc 1 11 4
	movw	58(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 58(%rsp)
	.loc 1 11 4
	movw	60(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 60(%rsp)
	.loc 1 11 4
	movw	62(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 62(%rsp)
	.loc 1 11 4
	movw	64(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 64(%rsp)
	.loc 1 11 4
	movw	66(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 66(%rsp)
	.loc 1 11 4
	movw	68(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 68(%rsp)
	.loc 1 11 4
	movw	70(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 70(%rsp)
	.loc 1 11 4
	movw	72(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 72(%rsp)
	.loc 1 11 4
	movw	74(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 74(%rsp)
	.loc 1 11 4
	movw	76(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 76(%rsp)
	.loc 1 11 4
	movw	78(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 78(%rsp)
	.loc 1 11 4
	movw	80(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 80(%rsp)
	.loc 1 11 4
	movw	82(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 82(%rsp)
	.loc 1 11 4
	movw	84(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 84(%rsp)
	.loc 1 11 4
	movw	86(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 86(%rsp)
	.loc 1 11 4
	movw	88(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 88(%rsp)
	.loc 1 11 4
	movw	90(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 90(%rsp)
	.loc 1 11 4
	movw	92(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 92(%rsp)
	.loc 1 11 4
	movw	94(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 94(%rsp)
	.loc 1 11 4
	movw	96(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 96(%rsp)
	.loc 1 11 4
	movw	98(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 98(%rsp)
	.loc 1 11 4
	movw	100(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 100(%rsp)
	.loc 1 11 4
	movw	102(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 102(%rsp)
	.loc 1 11 4
	movw	104(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 104(%rsp)
	.loc 1 11 4
	movw	106(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 106(%rsp)
	.loc 1 11 4
	movw	108(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 108(%rsp)
	.loc 1 11 4
	movw	110(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 110(%rsp)
	.loc 1 11 4
	movw	112(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 112(%rsp)
	.loc 1 11 4
	movw	114(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 114(%rsp)
	.loc 1 11 4
	movw	116(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 116(%rsp)
	.loc 1 11 4
	movw	118(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 118(%rsp)
	.loc 1 11 4
	movw	120(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 120(%rsp)
	.loc 1 11 4
	movw	122(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 122(%rsp)
	.loc 1 11 4
	movw	124(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 124(%rsp)
	.loc 1 11 4
	movw	126(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 126(%rsp)
	.loc 1 11 4
	movw	128(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 128(%rsp)
	.loc 1 11 4
	movw	130(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 130(%rsp)
	.loc 1 11 4
	movw	132(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 132(%rsp)
	.loc 1 11 4
	movw	134(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 134(%rsp)
	.loc 1 11 4
	movw	136(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 136(%rsp)
	.loc 1 11 4
	movw	138(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 138(%rsp)
	.loc 1 11 4
	movw	140(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 140(%rsp)
	.loc 1 11 4
	movw	142(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 142(%rsp)
	.loc 1 11 4
	movw	144(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 144(%rsp)
	.loc 1 11 4
	movw	146(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 146(%rsp)
	.loc 1 11 4
	movw	148(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 148(%rsp)
	.loc 1 11 4
	movw	150(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 150(%rsp)
	.loc 1 11 4
	movw	152(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 152(%rsp)
	.loc 1 11 4
	movw	154(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 154(%rsp)
	.loc 1 11 4
	movw	156(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 156(%rsp)
	.loc 1 11 4
	movw	158(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 158(%rsp)
	.loc 1 11 4
	movw	160(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 160(%rsp)
	.loc 1 11 4
	movw	162(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 162(%rsp)
	.loc 1 11 4
	movw	164(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 164(%rsp)
	.loc 1 11 4
	movw	166(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 166(%rsp)
	.loc 1 11 4
	movw	168(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 168(%rsp)
	.loc 1 11 4
	movw	170(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 170(%rsp)
	.loc 1 11 4
	movw	172(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 172(%rsp)
	.loc 1 11 4
	movw	174(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 174(%rsp)
	.loc 1 11 4
	movw	176(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 176(%rsp)
	.loc 1 11 4
	movw	178(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 178(%rsp)
	.loc 1 11 4
	movw	180(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 180(%rsp)
	.loc 1 11 4
	movw	182(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 182(%rsp)
	.loc 1 11 4
	movw	184(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 184(%rsp)
	.loc 1 11 4
	movw	186(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 186(%rsp)
	.loc 1 11 4
	movw	188(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 188(%rsp)
	.loc 1 11 4
	movw	190(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 190(%rsp)
	.loc 1 11 4
	movw	192(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 192(%rsp)
	.loc 1 11 4
	movw	194(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 194(%rsp)
	.loc 1 11 4
	movw	196(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 196(%rsp)
	.loc 1 11 4
	movw	198(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 198(%rsp)
	.loc 1 11 4
	movw	200(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 200(%rsp)
	.loc 1 11 4
	movw	202(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 202(%rsp)
	.loc 1 11 4
	movw	204(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 204(%rsp)
	.loc 1 11 4
	movw	206(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 206(%rsp)
	.loc 1 11 4
	movw	208(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 208(%rsp)
	.loc 1 11 4
	movw	210(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 210(%rsp)
	.loc 1 11 4
	movw	212(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 212(%rsp)
	.loc 1 11 4
	movw	214(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 214(%rsp)
	.loc 1 11 4
	movw	216(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 216(%rsp)
	.loc 1 11 4
	movw	218(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 218(%rsp)
	.loc 1 11 4
	movw	220(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 220(%rsp)
	.loc 1 11 4
	movw	222(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 222(%rsp)
	.loc 1 11 4
	movw	224(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 224(%rsp)
	.loc 1 11 4
	movw	226(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 226(%rsp)
	.loc 1 11 4
	movw	228(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 228(%rsp)
	.loc 1 11 4
	movw	230(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 230(%rsp)
	.loc 1 11 4
	movw	232(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 232(%rsp)
	.loc 1 11 4
	movw	234(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 234(%rsp)
	.loc 1 11 4
	movw	236(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 236(%rsp)
	.loc 1 11 4
	movw	238(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 238(%rsp)
	.loc 1 11 4
	movw	240(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 240(%rsp)
	.loc 1 11 4
	movw	242(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 242(%rsp)
	.loc 1 11 4
	movw	244(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 244(%rsp)
	.loc 1 11 4
	movw	246(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 246(%rsp)
	.loc 1 11 4
	movw	248(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 248(%rsp)
	.loc 1 11 4
	movw	250(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 250(%rsp)
	.loc 1 11 4
	movw	252(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 252(%rsp)
	.loc 1 11 4
	movw	254(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 254(%rsp)
	.loc 1 11 4
	movw	256(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 256(%rsp)
	.loc 1 11 4
	movw	258(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 258(%rsp)
	.loc 1 11 4
	movw	260(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 260(%rsp)
	.loc 1 11 4
	movw	262(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 262(%rsp)
	.loc 1 11 4
	movw	264(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 264(%rsp)
	.loc 1 11 4
	movw	266(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 266(%rsp)
	.loc 1 11 4
	movw	268(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 268(%rsp)
	.loc 1 11 4
	movw	270(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 270(%rsp)
	.loc 1 11 4
	movw	272(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 272(%rsp)
	.loc 1 11 4
	movw	274(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 274(%rsp)
	.loc 1 11 4
	movw	276(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 276(%rsp)
	.loc 1 11 4
	movw	278(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 278(%rsp)
	.loc 1 11 4
	movw	280(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 280(%rsp)
	.loc 1 11 4
	movw	282(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 282(%rsp)
	.loc 1 11 4
	movw	284(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 284(%rsp)
	.loc 1 11 4
	movw	286(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 286(%rsp)
	.loc 1 11 4
	movw	288(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 288(%rsp)
	.loc 1 11 4
	movw	290(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 290(%rsp)
	.loc 1 11 4
	movw	292(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 292(%rsp)
	.loc 1 11 4
	movw	294(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 294(%rsp)
	.loc 1 11 4
	movw	296(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 296(%rsp)
	.loc 1 11 4
	movw	298(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 298(%rsp)
	.loc 1 11 4
	movw	300(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 300(%rsp)
	.loc 1 11 4
	movw	302(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 302(%rsp)
	.loc 1 11 4
	movw	304(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 304(%rsp)
	.loc 1 11 4
	movw	306(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 306(%rsp)
	.loc 1 11 4
	movw	308(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 308(%rsp)
	.loc 1 11 4
	movw	310(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 310(%rsp)
	.loc 1 11 4
	movw	312(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 312(%rsp)
	.loc 1 11 4
	movw	314(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 314(%rsp)
	.loc 1 11 4
	movw	316(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 316(%rsp)
	.loc 1 11 4
	movw	318(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 318(%rsp)
	.loc 1 11 4
	movw	320(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 320(%rsp)
	.loc 1 11 4
	movw	322(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 322(%rsp)
	.loc 1 11 4
	movw	324(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 324(%rsp)
	.loc 1 11 4
	movw	326(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 326(%rsp)
	.loc 1 11 4
	movw	328(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 328(%rsp)
	.loc 1 11 4
	movw	330(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 330(%rsp)
	.loc 1 11 4
	movw	332(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 332(%rsp)
	.loc 1 11 4
	movw	334(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 334(%rsp)
	.loc 1 11 4
	movw	336(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 336(%rsp)
	.loc 1 11 4
	movw	338(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 338(%rsp)
	.loc 1 11 4
	movw	340(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 340(%rsp)
	.loc 1 11 4
	movw	342(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 342(%rsp)
	.loc 1 11 4
	movw	344(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 344(%rsp)
	.loc 1 11 4
	movw	346(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 346(%rsp)
	.loc 1 11 4
	movw	348(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 348(%rsp)
	.loc 1 11 4
	movw	350(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 350(%rsp)
	.loc 1 11 4
	movw	352(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 352(%rsp)
	.loc 1 11 4
	movw	354(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 354(%rsp)
	.loc 1 11 4
	movw	356(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 356(%rsp)
	.loc 1 11 4
	movw	358(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 358(%rsp)
	.loc 1 11 4
	movw	360(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 360(%rsp)
	.loc 1 11 4
	movw	362(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 362(%rsp)
	.loc 1 11 4
	movw	364(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 364(%rsp)
	.loc 1 11 4
	movw	366(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 366(%rsp)
	.loc 1 11 4
	movw	368(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 368(%rsp)
	.loc 1 11 4
	movw	370(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 370(%rsp)
	.loc 1 11 4
	movw	372(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 372(%rsp)
	.loc 1 11 4
	movw	374(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 374(%rsp)
	.loc 1 11 4
	movw	376(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 376(%rsp)
	.loc 1 11 4
	movw	378(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 378(%rsp)
	.loc 1 11 4
	movw	380(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 380(%rsp)
	.loc 1 11 4
	movw	382(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 382(%rsp)
	.loc 1 11 4
	movw	384(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 384(%rsp)
	.loc 1 11 4
	movw	386(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 386(%rsp)
	.loc 1 11 4
	movw	388(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 388(%rsp)
	.loc 1 11 4
	movw	390(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 390(%rsp)
	.loc 1 11 4
	movw	392(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 392(%rsp)
	.loc 1 11 4
	movw	394(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 394(%rsp)
	.loc 1 11 4
	movw	396(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 396(%rsp)
	.loc 1 11 4
	movw	398(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 398(%rsp)
	.loc 1 11 4
	movw	400(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 400(%rsp)
	.loc 1 11 4
	movw	402(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 402(%rsp)
	.loc 1 11 4
	movw	404(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 404(%rsp)
	.loc 1 11 4
	movw	406(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 406(%rsp)
	.loc 1 11 4
	movw	408(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 408(%rsp)
	.loc 1 11 4
	movw	410(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 410(%rsp)
	.loc 1 11 4
	movw	412(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 412(%rsp)
	.loc 1 11 4
	movw	414(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 414(%rsp)
	.loc 1 11 4
	movw	416(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 416(%rsp)
	.loc 1 11 4
	movw	418(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 418(%rsp)
	.loc 1 11 4
	movw	420(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 420(%rsp)
	.loc 1 11 4
	movw	422(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 422(%rsp)
	.loc 1 11 4
	movw	424(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 424(%rsp)
	.loc 1 11 4
	movw	426(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 426(%rsp)
	.loc 1 11 4
	movw	428(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 428(%rsp)
	.loc 1 11 4
	movw	430(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 430(%rsp)
	.loc 1 11 4
	movw	432(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 432(%rsp)
	.loc 1 11 4
	movw	434(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 434(%rsp)
	.loc 1 11 4
	movw	436(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 436(%rsp)
	.loc 1 11 4
	movw	438(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 438(%rsp)
	.loc 1 11 4
	movw	440(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 440(%rsp)
	.loc 1 11 4
	movw	442(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 442(%rsp)
	.loc 1 11 4
	movw	444(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 444(%rsp)
	.loc 1 11 4
	movw	446(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 446(%rsp)
	.loc 1 11 4
	movw	448(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 448(%rsp)
	.loc 1 11 4
	movw	450(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 450(%rsp)
	.loc 1 11 4
	movw	452(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 452(%rsp)
	.loc 1 11 4
	movw	454(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 454(%rsp)
	.loc 1 11 4
	movw	456(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 456(%rsp)
	.loc 1 11 4
	movw	458(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 458(%rsp)
	.loc 1 11 4
	movw	460(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 460(%rsp)
	.loc 1 11 4
	movw	462(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 462(%rsp)
	.loc 1 11 4
	movw	464(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 464(%rsp)
	.loc 1 11 4
	movw	466(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 466(%rsp)
	.loc 1 11 4
	movw	468(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 468(%rsp)
	.loc 1 11 4
	movw	470(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 470(%rsp)
	.loc 1 11 4
	movw	472(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 472(%rsp)
	.loc 1 11 4
	movw	474(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 474(%rsp)
	.loc 1 11 4
	movw	476(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 476(%rsp)
	.loc 1 11 4
	movw	478(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 478(%rsp)
	.loc 1 11 4
	movw	480(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 480(%rsp)
	.loc 1 11 4
	movw	482(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 482(%rsp)
	.loc 1 11 4
	movw	484(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 484(%rsp)
	.loc 1 11 4
	movw	486(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 486(%rsp)
	.loc 1 11 4
	movw	488(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 488(%rsp)
	.loc 1 11 4
	movw	490(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 490(%rsp)
	.loc 1 11 4
	movw	492(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 492(%rsp)
	.loc 1 11 4
	movw	494(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 494(%rsp)
	.loc 1 11 4
	movw	496(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 496(%rsp)
	.loc 1 11 4
	movw	498(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 498(%rsp)
	.loc 1 11 4
	movw	500(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 500(%rsp)
	.loc 1 11 4
	movw	502(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 502(%rsp)
	.loc 1 11 4
	movw	504(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 504(%rsp)
	.loc 1 11 4
	movw	506(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 506(%rsp)
	.loc 1 11 4
	movw	508(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 508(%rsp)
	.loc 1 11 4
	movw	510(%rdi), %ax
	.loc 1 12 4
	movw	%ax, 510(%rsp)
	.loc 1 15 2
	movq	%rsp, %rax
	.loc 1 15 2
	call	L_poly_ntt$1
	.loc 1 15 2
Lpoly_ntt_jazz$1:
	.loc 1 18 4
	movw	(%rsp), %ax
	.loc 1 19 4
	movw	%ax, (%rdi)
	.loc 1 18 4
	movw	2(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 2(%rdi)
	.loc 1 18 4
	movw	4(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 4(%rdi)
	.loc 1 18 4
	movw	6(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 6(%rdi)
	.loc 1 18 4
	movw	8(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 8(%rdi)
	.loc 1 18 4
	movw	10(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 10(%rdi)
	.loc 1 18 4
	movw	12(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 12(%rdi)
	.loc 1 18 4
	movw	14(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 14(%rdi)
	.loc 1 18 4
	movw	16(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 16(%rdi)
	.loc 1 18 4
	movw	18(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 18(%rdi)
	.loc 1 18 4
	movw	20(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 20(%rdi)
	.loc 1 18 4
	movw	22(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 22(%rdi)
	.loc 1 18 4
	movw	24(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 24(%rdi)
	.loc 1 18 4
	movw	26(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 26(%rdi)
	.loc 1 18 4
	movw	28(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 28(%rdi)
	.loc 1 18 4
	movw	30(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 30(%rdi)
	.loc 1 18 4
	movw	32(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 32(%rdi)
	.loc 1 18 4
	movw	34(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 34(%rdi)
	.loc 1 18 4
	movw	36(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 36(%rdi)
	.loc 1 18 4
	movw	38(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 38(%rdi)
	.loc 1 18 4
	movw	40(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 40(%rdi)
	.loc 1 18 4
	movw	42(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 42(%rdi)
	.loc 1 18 4
	movw	44(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 44(%rdi)
	.loc 1 18 4
	movw	46(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 46(%rdi)
	.loc 1 18 4
	movw	48(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 48(%rdi)
	.loc 1 18 4
	movw	50(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 50(%rdi)
	.loc 1 18 4
	movw	52(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 52(%rdi)
	.loc 1 18 4
	movw	54(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 54(%rdi)
	.loc 1 18 4
	movw	56(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 56(%rdi)
	.loc 1 18 4
	movw	58(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 58(%rdi)
	.loc 1 18 4
	movw	60(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 60(%rdi)
	.loc 1 18 4
	movw	62(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 62(%rdi)
	.loc 1 18 4
	movw	64(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 64(%rdi)
	.loc 1 18 4
	movw	66(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 66(%rdi)
	.loc 1 18 4
	movw	68(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 68(%rdi)
	.loc 1 18 4
	movw	70(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 70(%rdi)
	.loc 1 18 4
	movw	72(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 72(%rdi)
	.loc 1 18 4
	movw	74(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 74(%rdi)
	.loc 1 18 4
	movw	76(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 76(%rdi)
	.loc 1 18 4
	movw	78(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 78(%rdi)
	.loc 1 18 4
	movw	80(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 80(%rdi)
	.loc 1 18 4
	movw	82(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 82(%rdi)
	.loc 1 18 4
	movw	84(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 84(%rdi)
	.loc 1 18 4
	movw	86(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 86(%rdi)
	.loc 1 18 4
	movw	88(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 88(%rdi)
	.loc 1 18 4
	movw	90(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 90(%rdi)
	.loc 1 18 4
	movw	92(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 92(%rdi)
	.loc 1 18 4
	movw	94(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 94(%rdi)
	.loc 1 18 4
	movw	96(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 96(%rdi)
	.loc 1 18 4
	movw	98(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 98(%rdi)
	.loc 1 18 4
	movw	100(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 100(%rdi)
	.loc 1 18 4
	movw	102(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 102(%rdi)
	.loc 1 18 4
	movw	104(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 104(%rdi)
	.loc 1 18 4
	movw	106(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 106(%rdi)
	.loc 1 18 4
	movw	108(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 108(%rdi)
	.loc 1 18 4
	movw	110(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 110(%rdi)
	.loc 1 18 4
	movw	112(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 112(%rdi)
	.loc 1 18 4
	movw	114(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 114(%rdi)
	.loc 1 18 4
	movw	116(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 116(%rdi)
	.loc 1 18 4
	movw	118(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 118(%rdi)
	.loc 1 18 4
	movw	120(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 120(%rdi)
	.loc 1 18 4
	movw	122(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 122(%rdi)
	.loc 1 18 4
	movw	124(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 124(%rdi)
	.loc 1 18 4
	movw	126(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 126(%rdi)
	.loc 1 18 4
	movw	128(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 128(%rdi)
	.loc 1 18 4
	movw	130(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 130(%rdi)
	.loc 1 18 4
	movw	132(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 132(%rdi)
	.loc 1 18 4
	movw	134(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 134(%rdi)
	.loc 1 18 4
	movw	136(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 136(%rdi)
	.loc 1 18 4
	movw	138(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 138(%rdi)
	.loc 1 18 4
	movw	140(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 140(%rdi)
	.loc 1 18 4
	movw	142(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 142(%rdi)
	.loc 1 18 4
	movw	144(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 144(%rdi)
	.loc 1 18 4
	movw	146(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 146(%rdi)
	.loc 1 18 4
	movw	148(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 148(%rdi)
	.loc 1 18 4
	movw	150(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 150(%rdi)
	.loc 1 18 4
	movw	152(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 152(%rdi)
	.loc 1 18 4
	movw	154(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 154(%rdi)
	.loc 1 18 4
	movw	156(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 156(%rdi)
	.loc 1 18 4
	movw	158(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 158(%rdi)
	.loc 1 18 4
	movw	160(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 160(%rdi)
	.loc 1 18 4
	movw	162(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 162(%rdi)
	.loc 1 18 4
	movw	164(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 164(%rdi)
	.loc 1 18 4
	movw	166(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 166(%rdi)
	.loc 1 18 4
	movw	168(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 168(%rdi)
	.loc 1 18 4
	movw	170(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 170(%rdi)
	.loc 1 18 4
	movw	172(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 172(%rdi)
	.loc 1 18 4
	movw	174(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 174(%rdi)
	.loc 1 18 4
	movw	176(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 176(%rdi)
	.loc 1 18 4
	movw	178(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 178(%rdi)
	.loc 1 18 4
	movw	180(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 180(%rdi)
	.loc 1 18 4
	movw	182(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 182(%rdi)
	.loc 1 18 4
	movw	184(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 184(%rdi)
	.loc 1 18 4
	movw	186(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 186(%rdi)
	.loc 1 18 4
	movw	188(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 188(%rdi)
	.loc 1 18 4
	movw	190(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 190(%rdi)
	.loc 1 18 4
	movw	192(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 192(%rdi)
	.loc 1 18 4
	movw	194(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 194(%rdi)
	.loc 1 18 4
	movw	196(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 196(%rdi)
	.loc 1 18 4
	movw	198(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 198(%rdi)
	.loc 1 18 4
	movw	200(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 200(%rdi)
	.loc 1 18 4
	movw	202(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 202(%rdi)
	.loc 1 18 4
	movw	204(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 204(%rdi)
	.loc 1 18 4
	movw	206(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 206(%rdi)
	.loc 1 18 4
	movw	208(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 208(%rdi)
	.loc 1 18 4
	movw	210(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 210(%rdi)
	.loc 1 18 4
	movw	212(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 212(%rdi)
	.loc 1 18 4
	movw	214(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 214(%rdi)
	.loc 1 18 4
	movw	216(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 216(%rdi)
	.loc 1 18 4
	movw	218(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 218(%rdi)
	.loc 1 18 4
	movw	220(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 220(%rdi)
	.loc 1 18 4
	movw	222(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 222(%rdi)
	.loc 1 18 4
	movw	224(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 224(%rdi)
	.loc 1 18 4
	movw	226(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 226(%rdi)
	.loc 1 18 4
	movw	228(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 228(%rdi)
	.loc 1 18 4
	movw	230(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 230(%rdi)
	.loc 1 18 4
	movw	232(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 232(%rdi)
	.loc 1 18 4
	movw	234(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 234(%rdi)
	.loc 1 18 4
	movw	236(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 236(%rdi)
	.loc 1 18 4
	movw	238(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 238(%rdi)
	.loc 1 18 4
	movw	240(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 240(%rdi)
	.loc 1 18 4
	movw	242(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 242(%rdi)
	.loc 1 18 4
	movw	244(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 244(%rdi)
	.loc 1 18 4
	movw	246(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 246(%rdi)
	.loc 1 18 4
	movw	248(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 248(%rdi)
	.loc 1 18 4
	movw	250(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 250(%rdi)
	.loc 1 18 4
	movw	252(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 252(%rdi)
	.loc 1 18 4
	movw	254(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 254(%rdi)
	.loc 1 18 4
	movw	256(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 256(%rdi)
	.loc 1 18 4
	movw	258(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 258(%rdi)
	.loc 1 18 4
	movw	260(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 260(%rdi)
	.loc 1 18 4
	movw	262(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 262(%rdi)
	.loc 1 18 4
	movw	264(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 264(%rdi)
	.loc 1 18 4
	movw	266(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 266(%rdi)
	.loc 1 18 4
	movw	268(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 268(%rdi)
	.loc 1 18 4
	movw	270(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 270(%rdi)
	.loc 1 18 4
	movw	272(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 272(%rdi)
	.loc 1 18 4
	movw	274(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 274(%rdi)
	.loc 1 18 4
	movw	276(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 276(%rdi)
	.loc 1 18 4
	movw	278(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 278(%rdi)
	.loc 1 18 4
	movw	280(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 280(%rdi)
	.loc 1 18 4
	movw	282(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 282(%rdi)
	.loc 1 18 4
	movw	284(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 284(%rdi)
	.loc 1 18 4
	movw	286(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 286(%rdi)
	.loc 1 18 4
	movw	288(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 288(%rdi)
	.loc 1 18 4
	movw	290(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 290(%rdi)
	.loc 1 18 4
	movw	292(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 292(%rdi)
	.loc 1 18 4
	movw	294(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 294(%rdi)
	.loc 1 18 4
	movw	296(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 296(%rdi)
	.loc 1 18 4
	movw	298(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 298(%rdi)
	.loc 1 18 4
	movw	300(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 300(%rdi)
	.loc 1 18 4
	movw	302(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 302(%rdi)
	.loc 1 18 4
	movw	304(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 304(%rdi)
	.loc 1 18 4
	movw	306(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 306(%rdi)
	.loc 1 18 4
	movw	308(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 308(%rdi)
	.loc 1 18 4
	movw	310(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 310(%rdi)
	.loc 1 18 4
	movw	312(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 312(%rdi)
	.loc 1 18 4
	movw	314(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 314(%rdi)
	.loc 1 18 4
	movw	316(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 316(%rdi)
	.loc 1 18 4
	movw	318(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 318(%rdi)
	.loc 1 18 4
	movw	320(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 320(%rdi)
	.loc 1 18 4
	movw	322(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 322(%rdi)
	.loc 1 18 4
	movw	324(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 324(%rdi)
	.loc 1 18 4
	movw	326(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 326(%rdi)
	.loc 1 18 4
	movw	328(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 328(%rdi)
	.loc 1 18 4
	movw	330(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 330(%rdi)
	.loc 1 18 4
	movw	332(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 332(%rdi)
	.loc 1 18 4
	movw	334(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 334(%rdi)
	.loc 1 18 4
	movw	336(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 336(%rdi)
	.loc 1 18 4
	movw	338(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 338(%rdi)
	.loc 1 18 4
	movw	340(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 340(%rdi)
	.loc 1 18 4
	movw	342(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 342(%rdi)
	.loc 1 18 4
	movw	344(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 344(%rdi)
	.loc 1 18 4
	movw	346(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 346(%rdi)
	.loc 1 18 4
	movw	348(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 348(%rdi)
	.loc 1 18 4
	movw	350(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 350(%rdi)
	.loc 1 18 4
	movw	352(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 352(%rdi)
	.loc 1 18 4
	movw	354(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 354(%rdi)
	.loc 1 18 4
	movw	356(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 356(%rdi)
	.loc 1 18 4
	movw	358(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 358(%rdi)
	.loc 1 18 4
	movw	360(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 360(%rdi)
	.loc 1 18 4
	movw	362(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 362(%rdi)
	.loc 1 18 4
	movw	364(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 364(%rdi)
	.loc 1 18 4
	movw	366(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 366(%rdi)
	.loc 1 18 4
	movw	368(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 368(%rdi)
	.loc 1 18 4
	movw	370(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 370(%rdi)
	.loc 1 18 4
	movw	372(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 372(%rdi)
	.loc 1 18 4
	movw	374(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 374(%rdi)
	.loc 1 18 4
	movw	376(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 376(%rdi)
	.loc 1 18 4
	movw	378(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 378(%rdi)
	.loc 1 18 4
	movw	380(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 380(%rdi)
	.loc 1 18 4
	movw	382(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 382(%rdi)
	.loc 1 18 4
	movw	384(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 384(%rdi)
	.loc 1 18 4
	movw	386(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 386(%rdi)
	.loc 1 18 4
	movw	388(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 388(%rdi)
	.loc 1 18 4
	movw	390(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 390(%rdi)
	.loc 1 18 4
	movw	392(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 392(%rdi)
	.loc 1 18 4
	movw	394(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 394(%rdi)
	.loc 1 18 4
	movw	396(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 396(%rdi)
	.loc 1 18 4
	movw	398(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 398(%rdi)
	.loc 1 18 4
	movw	400(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 400(%rdi)
	.loc 1 18 4
	movw	402(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 402(%rdi)
	.loc 1 18 4
	movw	404(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 404(%rdi)
	.loc 1 18 4
	movw	406(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 406(%rdi)
	.loc 1 18 4
	movw	408(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 408(%rdi)
	.loc 1 18 4
	movw	410(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 410(%rdi)
	.loc 1 18 4
	movw	412(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 412(%rdi)
	.loc 1 18 4
	movw	414(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 414(%rdi)
	.loc 1 18 4
	movw	416(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 416(%rdi)
	.loc 1 18 4
	movw	418(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 418(%rdi)
	.loc 1 18 4
	movw	420(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 420(%rdi)
	.loc 1 18 4
	movw	422(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 422(%rdi)
	.loc 1 18 4
	movw	424(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 424(%rdi)
	.loc 1 18 4
	movw	426(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 426(%rdi)
	.loc 1 18 4
	movw	428(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 428(%rdi)
	.loc 1 18 4
	movw	430(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 430(%rdi)
	.loc 1 18 4
	movw	432(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 432(%rdi)
	.loc 1 18 4
	movw	434(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 434(%rdi)
	.loc 1 18 4
	movw	436(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 436(%rdi)
	.loc 1 18 4
	movw	438(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 438(%rdi)
	.loc 1 18 4
	movw	440(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 440(%rdi)
	.loc 1 18 4
	movw	442(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 442(%rdi)
	.loc 1 18 4
	movw	444(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 444(%rdi)
	.loc 1 18 4
	movw	446(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 446(%rdi)
	.loc 1 18 4
	movw	448(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 448(%rdi)
	.loc 1 18 4
	movw	450(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 450(%rdi)
	.loc 1 18 4
	movw	452(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 452(%rdi)
	.loc 1 18 4
	movw	454(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 454(%rdi)
	.loc 1 18 4
	movw	456(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 456(%rdi)
	.loc 1 18 4
	movw	458(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 458(%rdi)
	.loc 1 18 4
	movw	460(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 460(%rdi)
	.loc 1 18 4
	movw	462(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 462(%rdi)
	.loc 1 18 4
	movw	464(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 464(%rdi)
	.loc 1 18 4
	movw	466(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 466(%rdi)
	.loc 1 18 4
	movw	468(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 468(%rdi)
	.loc 1 18 4
	movw	470(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 470(%rdi)
	.loc 1 18 4
	movw	472(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 472(%rdi)
	.loc 1 18 4
	movw	474(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 474(%rdi)
	.loc 1 18 4
	movw	476(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 476(%rdi)
	.loc 1 18 4
	movw	478(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 478(%rdi)
	.loc 1 18 4
	movw	480(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 480(%rdi)
	.loc 1 18 4
	movw	482(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 482(%rdi)
	.loc 1 18 4
	movw	484(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 484(%rdi)
	.loc 1 18 4
	movw	486(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 486(%rdi)
	.loc 1 18 4
	movw	488(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 488(%rdi)
	.loc 1 18 4
	movw	490(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 490(%rdi)
	.loc 1 18 4
	movw	492(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 492(%rdi)
	.loc 1 18 4
	movw	494(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 494(%rdi)
	.loc 1 18 4
	movw	496(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 496(%rdi)
	.loc 1 18 4
	movw	498(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 498(%rdi)
	.loc 1 18 4
	movw	500(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 500(%rdi)
	.loc 1 18 4
	movw	502(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 502(%rdi)
	.loc 1 18 4
	movw	504(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 504(%rdi)
	.loc 1 18 4
	movw	506(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 506(%rdi)
	.loc 1 18 4
	movw	508(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 508(%rdi)
	.loc 1 18 4
	movw	510(%rsp), %ax
	.loc 1 19 4
	movw	%ax, 510(%rdi)
	.loc 1 20 3
	movq	512(%rsp), %rbx
	.loc 1 20 3
	movq	520(%rsp), %rbp
	.loc 1 20 3
	movq	528(%rsp), %r12
	.loc 1 20 3
	movq	536(%rsp), %r13
	.loc 1 20 3
	movq	544(%rsp), %rsp
	ret
	.file 2 "poly.jinc"
	.loc 2 19 1
L_poly_ntt$1:
	.loc 2 37 2
	leaq	glob_data + 0(%rip), %rcx
	.loc 2 38 2
	movq	$0, %rdx
	.loc 2 39 2
	movq	$128, %rsi
	.loc 2 40 2
	jmp 	L_poly_ntt$4
	.loc 2 40 2
L_poly_ntt$5:
	.loc 2 42 4
	movq	$0, %r10
	.loc 2 43 4
	jmp 	L_poly_ntt$6
	.loc 2 43 4
L_poly_ntt$7:
	.loc 2 45 6
	incq	%rdx
	.loc 2 46 6
	movw	(%rcx,%rdx,2), %r8w
	.loc 2 47 6
	movq	%r10, %r9
	.loc 2 48 19
	addq	%rsi, %r10
	.loc 2 49 6
	jmp 	L_poly_ntt$8
	.loc 2 49 6
L_poly_ntt$9:
	.loc 2 51 8
	movw	(%rax,%r9,2), %r11w
	.loc 2 52 8
	movw	%r11w, %bx
	.loc 2 53 8
	movq	%r9, %rbp
	.loc 2 53 20
	addq	%rsi, %rbp
	.loc 2 54 8
	movw	(%rax,%rbp,2), %r12w
	.file 3 "reduce.jinc"
	.loc 3 13 2
	movswl	%r12w, %r12d
	.loc 3 14 2
	movswl	%r8w, %r13d
	.loc 3 15 2
	imull	%r13d, %r12d
	.loc 3 17 2
	imull	$-218038272, %r12d, %r13d
	.loc 3 18 2
	sarl	$16, %r13d
	.loc 3 20 2
	imull	$-3329, %r13d, %r13d
	.loc 3 21 2
	addl	%r12d, %r13d
	.loc 3 22 2
	sarl	$16, %r13d
	.loc 2 56 8
	subw	%r13w, %bx
	.loc 2 57 8
	addw	%r11w, %r13w
	.loc 2 58 8
	movw	%bx, (%rax,%rbp,2)
	.loc 2 59 8
	movw	%r13w, (%rax,%r9,2)
	.loc 2 60 8
	incq	%r9
	.loc 2 49 6
L_poly_ntt$8:
	.loc 2 49 13
	cmpq	%r10, %r9
	.loc 2 49 6
	jb  	L_poly_ntt$9
	.loc 2 62 6
	movq	%r9, %r10
	.loc 2 62 17
	addq	%rsi, %r10
	.loc 2 43 4
L_poly_ntt$6:
	.loc 2 43 11
	cmpq	$256, %r10
	.loc 2 43 4
	jb  	L_poly_ntt$7
	.loc 2 64 4
	shrq	$1, %rsi
	.loc 2 40 2
L_poly_ntt$4:
	.loc 2 40 9
	cmpq	$2, %rsi
	.loc 2 40 2
	jnb 	L_poly_ntt$5
	.loc 2 10 2
	movq	$0, %rcx
	.loc 2 11 2
	jmp 	L_poly_ntt$2
	.loc 2 11 2
L_poly_ntt$3:
	.loc 2 13 4
	movw	(%rax,%rcx,2), %dx
	.loc 3 33 2
	movswl	%dx, %esi
	.loc 3 34 2
	imull	$20159, %esi, %esi
	.loc 3 36 2
	sarl	$26, %esi
	.loc 3 37 2
	imull	$3329, %esi, %esi
	.loc 3 40 2
	subw	%si, %dx
	.loc 2 15 4
	movw	%dx, (%rax,%rcx,2)
	.loc 2 16 4
	incq	%rcx
	.loc 2 11 2
L_poly_ntt$2:
	.loc 2 11 9
	cmpq	$256, %rcx
	.loc 2 11 2
	jb  	L_poly_ntt$3
	.loc 2 69 2
	ret
	.data
	.p2align	5
_glob_data:
glob_data:
G$jzetas:
	.byte	-19
	.byte	8
	.byte	11
	.byte	10
	.byte	-102
	.byte	11
	.byte	20
	.byte	7
	.byte	-43
	.byte	5
	.byte	-114
	.byte	5
	.byte	31
	.byte	1
	.byte	-54
	.byte	0
	.byte	86
	.byte	12
	.byte	110
	.byte	2
	.byte	41
	.byte	6
	.byte	-74
	.byte	0
	.byte	-62
	.byte	3
	.byte	79
	.byte	8
	.byte	63
	.byte	7
	.byte	-68
	.byte	5
	.byte	61
	.byte	2
	.byte	-44
	.byte	7
	.byte	8
	.byte	1
	.byte	127
	.byte	1
	.byte	-60
	.byte	9
	.byte	-78
	.byte	5
	.byte	-65
	.byte	6
	.byte	127
	.byte	12
	.byte	88
	.byte	10
	.byte	-7
	.byte	3
	.byte	-36
	.byte	2
	.byte	96
	.byte	2
	.byte	-5
	.byte	6
	.byte	-101
	.byte	1
	.byte	52
	.byte	12
	.byte	-34
	.byte	6
	.byte	-57
	.byte	4
	.byte	-116
	.byte	2
	.byte	-39
	.byte	10
	.byte	-9
	.byte	3
	.byte	-12
	.byte	7
	.byte	-45
	.byte	5
	.byte	-25
	.byte	11
	.byte	-7
	.byte	6
	.byte	4
	.byte	2
	.byte	-7
	.byte	12
	.byte	-63
	.byte	11
	.byte	103
	.byte	10
	.byte	-81
	.byte	6
	.byte	119
	.byte	8
	.byte	126
	.byte	0
	.byte	-67
	.byte	5
	.byte	-84
	.byte	9
	.byte	-89
	.byte	12
	.byte	-14
	.byte	11
	.byte	62
	.byte	3
	.byte	107
	.byte	0
	.byte	116
	.byte	7
	.byte	10
	.byte	12
	.byte	74
	.byte	9
	.byte	115
	.byte	11
	.byte	-63
	.byte	3
	.byte	29
	.byte	7
	.byte	44
	.byte	10
	.byte	-64
	.byte	1
	.byte	-40
	.byte	8
	.byte	-91
	.byte	2
	.byte	6
	.byte	8
	.byte	-78
	.byte	8
	.byte	-82
	.byte	1
	.byte	43
	.byte	2
	.byte	75
	.byte	3
	.byte	30
	.byte	8
	.byte	103
	.byte	3
	.byte	14
	.byte	6
	.byte	105
	.byte	0
	.byte	-90
	.byte	1
	.byte	75
	.byte	2
	.byte	-79
	.byte	0
	.byte	22
	.byte	12
	.byte	-34
	.byte	11
	.byte	53
	.byte	11
	.byte	38
	.byte	6
	.byte	117
	.byte	6
	.byte	11
	.byte	12
	.byte	10
	.byte	3
	.byte	-121
	.byte	4
	.byte	110
	.byte	12
	.byte	-8
	.byte	9
	.byte	-53
	.byte	5
	.byte	-89
	.byte	10
	.byte	95
	.byte	4
	.byte	-53
	.byte	6
	.byte	-124
	.byte	2
	.byte	-103
	.byte	9
	.byte	93
	.byte	1
	.byte	-94
	.byte	1
	.byte	73
	.byte	1
	.byte	101
	.byte	12
	.byte	-74
	.byte	12
	.byte	49
	.byte	3
	.byte	73
	.byte	4
	.byte	91
	.byte	2
	.byte	98
	.byte	2
	.byte	42
	.byte	5
	.byte	-4
	.byte	7
	.byte	72
	.byte	7
	.byte	-128
	.byte	1
	.byte	66
	.byte	8
	.byte	121
	.byte	12
	.byte	-62
	.byte	4
	.byte	-54
	.byte	7
	.byte	-105
	.byte	9
	.byte	-36
	.byte	0
	.byte	94
	.byte	8
	.byte	-122
	.byte	6
	.byte	96
	.byte	8
	.byte	7
	.byte	7
	.byte	3
	.byte	8
	.byte	26
	.byte	3
	.byte	27
	.byte	7
	.byte	-85
	.byte	9
	.byte	-101
	.byte	9
	.byte	-34
	.byte	1
	.byte	-107
	.byte	12
	.byte	-51
	.byte	11
	.byte	-28
	.byte	3
	.byte	-33
	.byte	3
	.byte	-66
	.byte	3
	.byte	77
	.byte	7
	.byte	-14
	.byte	5
	.byte	92
	.byte	6
G$jzetas_inv:
	.byte	-91
	.byte	6
	.byte	15
	.byte	7
	.byte	-76
	.byte	5
	.byte	67
	.byte	9
	.byte	34
	.byte	9
	.byte	29
	.byte	9
	.byte	52
	.byte	1
	.byte	108
	.byte	0
	.byte	35
	.byte	11
	.byte	102
	.byte	3
	.byte	86
	.byte	3
	.byte	-26
	.byte	5
	.byte	-25
	.byte	9
	.byte	-2
	.byte	4
	.byte	-6
	.byte	5
	.byte	-95
	.byte	4
	.byte	123
	.byte	6
	.byte	-93
	.byte	4
	.byte	37
	.byte	12
	.byte	106
	.byte	3
	.byte	55
	.byte	5
	.byte	63
	.byte	8
	.byte	-120
	.byte	0
	.byte	-65
	.byte	4
	.byte	-127
	.byte	11
	.byte	-71
	.byte	5
	.byte	5
	.byte	5
	.byte	-41
	.byte	7
	.byte	-97
	.byte	10
	.byte	-90
	.byte	10
	.byte	-72
	.byte	8
	.byte	-48
	.byte	9
	.byte	75
	.byte	0
	.byte	-100
	.byte	0
	.byte	-72
	.byte	11
	.byte	95
	.byte	11
	.byte	-92
	.byte	11
	.byte	104
	.byte	3
	.byte	125
	.byte	10
	.byte	54
	.byte	6
	.byte	-94
	.byte	8
	.byte	90
	.byte	2
	.byte	54
	.byte	7
	.byte	9
	.byte	3
	.byte	-109
	.byte	0
	.byte	122
	.byte	8
	.byte	-9
	.byte	9
	.byte	-10
	.byte	0
	.byte	-116
	.byte	6
	.byte	-37
	.byte	6
	.byte	-52
	.byte	1
	.byte	35
	.byte	1
	.byte	-21
	.byte	0
	.byte	80
	.byte	12
	.byte	-74
	.byte	10
	.byte	91
	.byte	11
	.byte	-104
	.byte	12
	.byte	-13
	.byte	6
	.byte	-102
	.byte	9
	.byte	-29
	.byte	4
	.byte	-74
	.byte	9
	.byte	-42
	.byte	10
	.byte	83
	.byte	11
	.byte	79
	.byte	4
	.byte	-5
	.byte	4
	.byte	92
	.byte	10
	.byte	41
	.byte	4
	.byte	65
	.byte	11
	.byte	-43
	.byte	2
	.byte	-28
	.byte	5
	.byte	64
	.byte	9
	.byte	-114
	.byte	1
	.byte	-73
	.byte	3
	.byte	-9
	.byte	0
	.byte	-115
	.byte	5
	.byte	-106
	.byte	12
	.byte	-61
	.byte	9
	.byte	15
	.byte	1
	.byte	90
	.byte	0
	.byte	85
	.byte	3
	.byte	68
	.byte	7
	.byte	-125
	.byte	12
	.byte	-118
	.byte	4
	.byte	82
	.byte	6
	.byte	-102
	.byte	2
	.byte	64
	.byte	1
	.byte	8
	.byte	0
	.byte	-3
	.byte	10
	.byte	8
	.byte	6
	.byte	26
	.byte	1
	.byte	46
	.byte	7
	.byte	13
	.byte	5
	.byte	10
	.byte	9
	.byte	40
	.byte	2
	.byte	117
	.byte	10
	.byte	58
	.byte	8
	.byte	35
	.byte	6
	.byte	-51
	.byte	0
	.byte	102
	.byte	11
	.byte	6
	.byte	6
	.byte	-95
	.byte	10
	.byte	37
	.byte	10
	.byte	8
	.byte	9
	.byte	-87
	.byte	2
	.byte	-126
	.byte	0
	.byte	66
	.byte	6
	.byte	79
	.byte	7
	.byte	61
	.byte	3
	.byte	-126
	.byte	11
	.byte	-7
	.byte	11
	.byte	45
	.byte	5
	.byte	-60
	.byte	10
	.byte	69
	.byte	7
	.byte	-62
	.byte	5
	.byte	-78
	.byte	4
	.byte	63
	.byte	9
	.byte	75
	.byte	12
	.byte	-40
	.byte	6
	.byte	-109
	.byte	10
	.byte	-85
	.byte	0
	.byte	55
	.byte	12
	.byte	-30
	.byte	11
	.byte	115
	.byte	7
	.byte	44
	.byte	7
	.byte	-19
	.byte	5
	.byte	103
	.byte	1
	.byte	-10
	.byte	2
	.byte	-95
	.byte	5
