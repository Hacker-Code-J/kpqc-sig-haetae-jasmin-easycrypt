	.att_syntax
	.text
	.p2align	5
	.global	poly_basemul_jazz
	.global	poly_invntt_jazz
	.global	poly_ntt_jazz
	.type	poly_basemul_jazz, %function
poly_basemul_jazz:
	movq	%rsp, %rax
	leaq	-24(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rbp, (%rsp)
	movq	%r12, 8(%rsp)
	movq	%rax, 16(%rsp)
	leaq	-16(%rsp), %rsp
	call	L_poly_basemul$1
Lpoly_basemul_jazz$1:
	leaq	16(%rsp), %rsp
	movq	(%rsp), %rbp
	movq	8(%rsp), %r12
	movq	16(%rsp), %rsp
	ret
	.type	poly_invntt_jazz, %function
poly_invntt_jazz:
	movq	%rsp, %rax
	leaq	-32(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rbx, (%rsp)
	movq	%rbp, 8(%rsp)
	movq	%r12, 16(%rsp)
	movq	%rax, 24(%rsp)
	call	L_poly_invntt$1
Lpoly_invntt_jazz$1:
	movq	(%rsp), %rbx
	movq	8(%rsp), %rbp
	movq	16(%rsp), %r12
	movq	24(%rsp), %rsp
	ret
	.type	poly_ntt_jazz, %function
poly_ntt_jazz:
	movq	%rsp, %rax
	leaq	-32(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rbx, (%rsp)
	movq	%rbp, 8(%rsp)
	movq	%r12, 16(%rsp)
	movq	%rax, 24(%rsp)
	call	L_poly_ntt$1
Lpoly_ntt_jazz$1:
	movq	(%rsp), %rbx
	movq	8(%rsp), %rbp
	movq	16(%rsp), %r12
	movq	24(%rsp), %rsp
	ret
L_poly_ntt$1:
	leaq	glob_data + 256(%rip), %rax
	movq	$0, %rcx
	movq	$128, %rdx
	jmp 	L_poly_ntt$4
L_poly_ntt$5:
	movq	$0, %r9
	jmp 	L_poly_ntt$6
L_poly_ntt$7:
	incq	%rcx
	movw	(%rax,%rcx,2), %si
	movq	%r9, %r8
	addq	%rdx, %r9
	jmp 	L_poly_ntt$8
L_poly_ntt$9:
	movw	(%rdi,%r8,2), %r10w
	movw	%r10w, %r11w
	movq	%r8, %rbx
	addq	%rdx, %rbx
	movw	(%rdi,%rbx,2), %bp
	movswl	%bp, %ebp
	movswl	%si, %r12d
	imull	%r12d, %ebp
	imull	$-218038272, %ebp, %r12d
	sarl	$16, %r12d
	imull	$-3329, %r12d, %r12d
	addl	%ebp, %r12d
	sarl	$16, %r12d
	subw	%r12w, %r11w
	addw	%r10w, %r12w
	movw	%r11w, (%rdi,%rbx,2)
	movw	%r12w, (%rdi,%r8,2)
	incq	%r8
L_poly_ntt$8:
	cmpq	%r9, %r8
	jb  	L_poly_ntt$9
	movq	%r8, %r9
	addq	%rdx, %r9
L_poly_ntt$6:
	cmpq	$256, %r9
	jb  	L_poly_ntt$7
	shrq	$1, %rdx
L_poly_ntt$4:
	cmpq	$2, %rdx
	jnb 	L_poly_ntt$5
	movq	$0, %r8
	jmp 	L_poly_ntt$2
L_poly_ntt$3:
	movw	(%rdi,%r8,2), %r9w
	movswl	%r9w, %r12d
	imull	$20159, %r12d, %r12d
	sarl	$26, %r12d
	imull	$3329, %r12d, %r12d
	subw	%r12w, %r9w
	movw	%r9w, (%rdi,%r8,2)
	incq	%r8
L_poly_ntt$2:
	cmpq	$256, %r8
	jb  	L_poly_ntt$3
	ret
L_poly_invntt$1:
	leaq	glob_data + 0(%rip), %rax
	movq	$0, %rcx
	movq	$2, %rdx
	jmp 	L_poly_invntt$4
L_poly_invntt$5:
	movq	$0, %r9
	jmp 	L_poly_invntt$6
L_poly_invntt$7:
	movw	(%rax,%rcx,2), %si
	incq	%rcx
	movq	%r9, %r8
	addq	%rdx, %r9
	jmp 	L_poly_invntt$8
L_poly_invntt$9:
	movw	(%rdi,%r8,2), %bp
	movq	%r8, %rbx
	addq	%rdx, %rbx
	movw	(%rdi,%rbx,2), %r10w
	movw	%r10w, %r11w
	addw	%bp, %r11w
	movswl	%r11w, %r12d
	imull	$20159, %r12d, %r12d
	sarl	$26, %r12d
	imull	$3329, %r12d, %r12d
	subw	%r12w, %r11w
	movw	%r11w, (%rdi,%r8,2)
	subw	%r10w, %bp
	movswl	%bp, %ebp
	movswl	%si, %r12d
	imull	%r12d, %ebp
	imull	$-218038272, %ebp, %r12d
	sarl	$16, %r12d
	imull	$-3329, %r12d, %r12d
	addl	%ebp, %r12d
	sarl	$16, %r12d
	movw	%r12w, (%rdi,%rbx,2)
	incq	%r8
L_poly_invntt$8:
	cmpq	%r9, %r8
	jb  	L_poly_invntt$9
	movq	%r8, %r9
	addq	%rdx, %r9
L_poly_invntt$6:
	cmpq	$256, %r9
	jb  	L_poly_invntt$7
	shlq	$1, %rdx
L_poly_invntt$4:
	cmpq	$128, %rdx
	jbe 	L_poly_invntt$5
	movw	254(%rax), %cx
	movq	$0, %r8
	jmp 	L_poly_invntt$2
L_poly_invntt$3:
	movw	(%rdi,%r8,2), %r9w
	movswl	%r9w, %ebp
	movswl	%cx, %r12d
	imull	%r12d, %ebp
	imull	$-218038272, %ebp, %r12d
	sarl	$16, %r12d
	imull	$-3329, %r12d, %r9d
	addl	%ebp, %r9d
	sarl	$16, %r9d
	movw	%r9w, (%rdi,%r8,2)
	incq	%r8
L_poly_invntt$2:
	cmpq	$256, %r8
	jb  	L_poly_invntt$3
	ret
L_poly_basemul$1:
	movq	%rdi, 8(%rsp)
	movq	$0, %rax
	jmp 	L_poly_basemul$2
L_poly_basemul$3:
	leaq	glob_data + 384(%rip), %rcx
	movq	%rax, %rdi
	shrq	$2, %rdi
	movw	(%rcx,%rdi,2), %cx
	movw	(%rsi,%rax,2), %di
	movw	(%rdx,%rax,2), %r8w
	incq	%rax
	movw	(%rsi,%rax,2), %r9w
	movw	(%rdx,%rax,2), %r10w
	decq	%rax
	movswl	%r9w, %ebp
	movswl	%r10w, %r12d
	imull	%r12d, %ebp
	imull	$-218038272, %ebp, %r12d
	sarl	$16, %r12d
	imull	$-3329, %r12d, %r12d
	addl	%ebp, %r12d
	sarl	$16, %r12d
	movswl	%r12w, %ebp
	movswl	%cx, %r12d
	imull	%r12d, %ebp
	imull	$-218038272, %ebp, %r12d
	sarl	$16, %r12d
	imull	$-3329, %r12d, %r12d
	addl	%ebp, %r12d
	sarl	$16, %r12d
	movw	%r12w, %r11w
	movswl	%di, %ebp
	movswl	%r8w, %r12d
	imull	%r12d, %ebp
	imull	$-218038272, %ebp, %r12d
	sarl	$16, %r12d
	imull	$-3329, %r12d, %r12d
	addl	%ebp, %r12d
	sarl	$16, %r12d
	addw	%r12w, %r11w
	movswl	%di, %ebp
	movswl	%r10w, %r12d
	imull	%r12d, %ebp
	imull	$-218038272, %ebp, %r12d
	sarl	$16, %r12d
	imull	$-3329, %r12d, %r12d
	addl	%ebp, %r12d
	sarl	$16, %r12d
	movswl	%r9w, %ebp
	movswl	%r8w, %edi
	imull	%edi, %ebp
	imull	$-218038272, %ebp, %edi
	sarl	$16, %edi
	imull	$-3329, %edi, %r9d
	addl	%ebp, %r9d
	sarl	$16, %r9d
	addw	%r9w, %r12w
	movq	8(%rsp), %rdi
	movw	%r11w, (%rdi,%rax,2)
	incq	%rax
	movw	%r12w, (%rdi,%rax,2)
	movq	%rdi, 16(%rsp)
	negw	%cx
	incq	%rax
	movw	(%rsi,%rax,2), %di
	movw	(%rdx,%rax,2), %r8w
	incq	%rax
	movw	(%rsi,%rax,2), %r9w
	movw	(%rdx,%rax,2), %r10w
	decq	%rax
	movswl	%r9w, %ebp
	movswl	%r10w, %r12d
	imull	%r12d, %ebp
	imull	$-218038272, %ebp, %r12d
	sarl	$16, %r12d
	imull	$-3329, %r12d, %r12d
	addl	%ebp, %r12d
	sarl	$16, %r12d
	movswl	%r12w, %ebp
	movswl	%cx, %r12d
	imull	%r12d, %ebp
	imull	$-218038272, %ebp, %r12d
	sarl	$16, %r12d
	imull	$-3329, %r12d, %r12d
	addl	%ebp, %r12d
	sarl	$16, %r12d
	movw	%r12w, %r11w
	movswl	%di, %ebp
	movswl	%r8w, %r12d
	imull	%r12d, %ebp
	imull	$-218038272, %ebp, %r12d
	sarl	$16, %r12d
	imull	$-3329, %r12d, %r12d
	addl	%ebp, %r12d
	sarl	$16, %r12d
	addw	%r12w, %r11w
	movswl	%di, %ebp
	movswl	%r10w, %edi
	imull	%edi, %ebp
	imull	$-218038272, %ebp, %edi
	sarl	$16, %edi
	imull	$-3329, %edi, %r12d
	addl	%ebp, %r12d
	sarl	$16, %r12d
	movswl	%r9w, %ebp
	movswl	%r8w, %edi
	imull	%edi, %ebp
	imull	$-218038272, %ebp, %edi
	sarl	$16, %edi
	imull	$-3329, %edi, %r9d
	addl	%ebp, %r9d
	sarl	$16, %r9d
	addw	%r9w, %r12w
	movq	16(%rsp), %rdi
	movw	%r11w, (%rdi,%rax,2)
	incq	%rax
	movw	%r12w, (%rdi,%rax,2)
	incq	%rax
L_poly_basemul$2:
	cmpq	$253, %rax
	jb  	L_poly_basemul$3
	ret
	.data
	.p2align	5
glob_data:
G$jzetas_inv:
	.byte	165,   6,  15,   7, 180,   5,  67,   9,  34,   9,  29,   9,  52,   1, 108,   0
	.byte	 35,  11, 102,   3,  86,   3, 230,   5, 231,   9, 254,   4, 250,   5, 161,   4
	.byte	123,   6, 163,   4,  37,  12, 106,   3,  55,   5,  63,   8, 136,   0, 191,   4
	.byte	129,  11, 185,   5,   5,   5, 215,   7, 159,  10, 166,  10, 184,   8, 208,   9
	.byte	 75,   0, 156,   0, 184,  11,  95,  11, 164,  11, 104,   3, 125,  10,  54,   6
	.byte	162,   8,  90,   2,  54,   7,   9,   3, 147,   0, 122,   8, 247,   9, 246,   0
	.byte	140,   6, 219,   6, 204,   1,  35,   1, 235,   0,  80,  12, 182,  10,  91,  11
	.byte	152,  12, 243,   6, 154,   9, 227,   4, 182,   9, 214,  10,  83,  11,  79,   4
	.byte	251,   4,  92,  10,  41,   4,  65,  11, 213,   2, 228,   5,  64,   9, 142,   1
	.byte	183,   3, 247,   0, 141,   5, 150,  12, 195,   9,  15,   1,  90,   0,  85,   3
	.byte	 68,   7, 131,  12, 138,   4,  82,   6, 154,   2,  64,   1,   8,   0, 253,  10
	.byte	  8,   6,  26,   1,  46,   7,  13,   5,  10,   9,  40,   2, 117,  10,  58,   8
	.byte	 35,   6, 205,   0, 102,  11,   6,   6, 161,  10,  37,  10,   8,   9, 169,   2
	.byte	130,   0,  66,   6,  79,   7,  61,   3, 130,  11, 249,  11,  45,   5, 196,  10
	.byte	 69,   7, 194,   5, 178,   4,  63,   9,  75,  12, 216,   6, 147,  10, 171,   0
	.byte	 55,  12, 226,  11, 115,   7,  44,   7, 237,   5, 103,   1, 246,   2, 161,   5
G$jzetas:
	.byte	237,   8,  11,  10, 154,  11,  20,   7, 213,   5, 142,   5,  31,   1, 202,   0
	.byte	 86,  12, 110,   2,  41,   6, 182,   0, 194,   3,  79,   8,  63,   7, 188,   5
	.byte	 61,   2, 212,   7,   8,   1, 127,   1, 196,   9, 178,   5, 191,   6, 127,  12
	.byte	 88,  10, 249,   3, 220,   2,  96,   2, 251,   6, 155,   1,  52,  12, 222,   6
	.byte	199,   4, 140,   2, 217,  10, 247,   3, 244,   7, 211,   5, 231,  11, 249,   6
	.byte	  4,   2, 249,  12, 193,  11, 103,  10, 175,   6, 119,   8, 126,   0, 189,   5
	.byte	172,   9, 167,  12, 242,  11,  62,   3, 107,   0, 116,   7,  10,  12,  74,   9
	.byte	115,  11, 193,   3,  29,   7,  44,  10, 192,   1, 216,   8, 165,   2,   6,   8
	.byte	178,   8, 174,   1,  43,   2,  75,   3,  30,   8, 103,   3,  14,   6, 105,   0
	.byte	166,   1,  75,   2, 177,   0,  22,  12, 222,  11,  53,  11,  38,   6, 117,   6
	.byte	 11,  12,  10,   3, 135,   4, 110,  12, 248,   9, 203,   5, 167,  10,  95,   4
	.byte	203,   6, 132,   2, 153,   9,  93,   1, 162,   1,  73,   1, 101,  12, 182,  12
	.byte	 49,   3,  73,   4,  91,   2,  98,   2,  42,   5, 252,   7,  72,   7, 128,   1
	.byte	 66,   8, 121,  12, 194,   4, 202,   7, 151,   9, 220,   0,  94,   8, 134,   6
	.byte	 96,   8,   7,   7,   3,   8,  26,   3,  27,   7, 171,   9, 155,   9, 222,   1
	.byte	149,  12, 205,  11, 228,   3, 223,   3, 190,   3,  77,   7, 242,   5,  92,   6
	.ident	"Jasmin Compiler 2026.03.0"
	.section	".note.GNU-stack", "", %progbits
