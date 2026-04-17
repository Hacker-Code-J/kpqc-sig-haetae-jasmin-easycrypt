#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "params.h"
#include "poly.h"

/* ANSI color codes */
#define COLOR_GREEN   "\x1b[32m"
#define COLOR_YELLOW  "\x1b[33m"
#define COLOR_BLUE    "\x1b[34m"
#define COLOR_CYAN    "\x1b[36m"
#define COLOR_RESET   "\x1b[0m"
#define COLOR_BOLD    "\x1b[1m"

/* Adjust these to your scheme */
// #define N 256
// #define Q 3329
#define TESTS 200000

// typedef struct {
//     int16_t coeffs[N];
// } poly;

/* reference */
// void poly_ntt(poly *r);
// void poly_invntt_tomont(poly *r);
// void poly_pointwise_montgomery(poly *r, const poly *a, const poly *b);

/* jasmin */
extern void poly_ntt_jazz(poly *r);
extern void poly_invntt_jazz(poly *r);
extern void poly_basemul_jazz(poly *r, const poly *a, const poly *b);

static int16_t mod_q(int32_t x) {
    int32_t r = x % HAETAE_Q;
    if (r < 0) r += HAETAE_Q;
    return (int16_t)r;
}

static void poly_copy(poly *dst, const poly *src) {
    memcpy(dst, src, sizeof(poly));
}

/* safer for schemes where outputs may differ only by representative */
static int poly_equal_modq(const poly *a, const poly *b) {
    for (size_t i = 0; i < HAETAE_N; i++) {
        if (mod_q(a->coeffs[i]) != mod_q(b->coeffs[i])) {
            return 0;
        }
    }
    return 1;
}

static void print_poly_diff(const char *label, const poly *a, const poly *b) {
    printf("%s mismatch\n", label);
    for (size_t i = 0; i < HAETAE_N; i++) {
        int16_t xa = mod_q(a->coeffs[i]);
        int16_t xb = mod_q(b->coeffs[i]);
        if (xa != xb) {
            printf("  coeff[%zu]: ref=%d (raw %d), jazz=%d (raw %d)\n",
                   i, xa, a->coeffs[i], xb, b->coeffs[i]);
            return;
        }
    }
}

static void random_poly(poly *p) {
    for (size_t i = 0; i < HAETAE_N; i++) {
        /* try broad input range, not just canonical [0, Q) */
        int32_t x = (rand() % (8 * HAETAE_Q)) - (4 * HAETAE_Q);
        p->coeffs[i] = (int16_t)x;
    }
}

static void fill_edge_poly(poly *p, int mode) {
    for (size_t i = 0; i < HAETAE_N; i++) {
        switch (mode) {
        case 0: p->coeffs[i] = 0; break;
        case 1: p->coeffs[i] = 1; break;
        case 2: p->coeffs[i] = HAETAE_Q - 1; break;
        case 3: p->coeffs[i] = -1; break;
        case 4: p->coeffs[i] = HAETAE_Q; break;
        case 5: p->coeffs[i] = -HAETAE_Q; break;
        case 6: p->coeffs[i] = (i & 1) ? (HAETAE_Q - 1) : 0; break;
        case 7: p->coeffs[i] = (i & 1) ? 1 : -1; break;
        default: p->coeffs[i] = 0; break;
        }
    }
}

static int test_ntt_once(const poly *in) {
    poly ref, jazz;

    poly_copy(&ref, in);
    poly_copy(&jazz, in);

    poly_ntt(&ref);
    poly_ntt_jazz(&jazz);

    if (!poly_equal_modq(&ref, &jazz)) {
        print_poly_diff("poly_ntt", &ref, &jazz);
        return 0;
    }
    return 1;
}

static int test_invntt_once(const poly *in) {
    poly ref, jazz;

    poly_copy(&ref, in);
    poly_copy(&jazz, in);

    poly_invntt_tomont(&ref);
    poly_invntt_jazz(&jazz);

    if (!poly_equal_modq(&ref, &jazz)) {
        print_poly_diff("poly_invntt", &ref, &jazz);
        return 0;
    }
    return 1;
}

static int test_basemul_once(const poly *a, const poly *b) {
    poly ref, jazz;

    poly_pointwise_montgomery(&ref, a, b);
    poly_basemul_jazz(&jazz, a, b);

    if (!poly_equal_modq(&ref, &jazz)) {
        print_poly_diff("poly_basemul", &ref, &jazz);
        return 0;
    }
    return 1;
}

static int test_pipeline_once(const poly *a, const poly *b) {
    poly ar, br, rr;
    poly aj, bj, rj;

    poly_copy(&ar, a);
    poly_copy(&br, b);
    poly_copy(&aj, a);
    poly_copy(&bj, b);

    poly_ntt(&ar);
    poly_ntt(&br);
    poly_pointwise_montgomery(&rr, &ar, &br);
    poly_invntt_tomont(&rr);

    poly_ntt_jazz(&aj);
    poly_ntt_jazz(&bj);
    poly_basemul_jazz(&rj, &aj, &bj);
    poly_invntt_jazz(&rj);

    if (!poly_equal_modq(&rr, &rj)) {
        print_poly_diff("pipeline ref vs jazz", &rr, &rj);
        return 0;
    }
    return 1;
}

static int test_basemul_commutativity(const poly *a, const poly *b) {
    poly r1, r2;

    poly_basemul_jazz(&r1, a, b);
    poly_basemul_jazz(&r2, b, a);

    if (!poly_equal_modq(&r1, &r2)) {
        print_poly_diff("basemul_commutativity", &r1, &r2);
        return 0;
    }
    return 1;
}

static int test_associativity_jazz(const poly *a, const poly *b, const poly *c) {
    poly ab, abc1, bc, abc2;
    
    poly_basemul_jazz(&ab, a, b);
    poly_basemul_jazz(&abc1, &ab, c);

    poly_basemul_jazz(&bc, b, c);
    poly_basemul_jazz(&abc2, a, &bc);

    if (!poly_equal_modq(&abc1, &abc2)) {
        print_poly_diff("basemul_associativity", &abc1, &abc2);
        return 0;
    }
    return 1;
}

int main(void) {
    srand((unsigned)time(NULL));

    poly a, b;

    printf("=== Starting HAETAE NTT Tests ===\n\n");

    /* deterministic edge cases first */
    printf(COLOR_CYAN "Testing edge cases...\n" COLOR_RESET);
    for (int m1 = 0; m1 < 8; m1++) {
        fill_edge_poly(&a, m1);

        if (!test_ntt_once(&a)) return 1;
        if (!test_invntt_once(&a)) return 1;;

        for (int m2 = 0; m2 < 8; m2++) {
            fill_edge_poly(&b, m2);
            if (!test_basemul_once(&a, &b)) return 1;
            if (!test_pipeline_once(&a, &b)) return 1;
            if (!test_basemul_commutativity(&a, &b)) return 1;
        }
    }
    printf(COLOR_GREEN "✓ All edge cases passed\n" COLOR_RESET COLOR_BOLD "\n");

    /* randomized tests */
    printf("Running %d randomized tests...\n", TESTS);
    for (size_t t = 0; t < TESTS; t++) {
        random_poly(&a);
        random_poly(&b);
        poly c;
        random_poly(&c);

        if (!test_ntt_once(&a)) {
            printf("failed random poly_ntt at test %zu\n", t);
            return 1;
        }
        if (!test_invntt_once(&a)) {
            printf("failed random poly_invntt at test %zu\n", t);
            return 1;
        }
        if (!test_basemul_once(&a, &b)) {
            printf("failed random poly_basemul at test %zu\n", t);
            return 1;
        }
        if (!test_pipeline_once(&a, &b)) {
            printf("failed random pipeline at test %zu\n", t);
            return 1;
        }
        if (!test_basemul_commutativity(&a, &b)) {
            printf("failed random basemul_commutativity at test %zu\n", t);
            return 1;
        }
        if (!test_associativity_jazz(&a, &b, &c)) {
            printf("failed random associativity_jazz at test %zu\n", t);
            return 1;
        }

        if ((t + 1) % 10000 == 0) {
            int percent = (int)(((t + 1) * 100) / TESTS);
            int bar_len = (percent / 5);
            printf("\r  [");
            for (int i = 0; i < 20; i++) printf(i < bar_len ? "=" : " ");
            printf("] %3d%% (%zu/%d) tests", percent, t + 1, TESTS);
            fflush(stdout);
        }
    }
    printf("\n" COLOR_GREEN "✓ All randomized tests passed\n\n" COLOR_RESET);

    printf("=== " COLOR_GREEN "✓ All tests passed successfully" COLOR_RESET " ===\n");
    return 0;
}

// jasminc -nowarning -o hpoly.s  jasmin/hpoly.jazz 
// /usr/bin/cc -Wall -Wextra -g -O3 -fomit-frame-pointer -o test_haetae_ntt poly.c ntt.c reduce.c hpoly.s test_haetae_ntt.c 