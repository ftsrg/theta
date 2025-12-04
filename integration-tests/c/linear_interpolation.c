// This file is part of the SV-Benchmarks collection of verification tasks:
// https://github.com/sosy-lab/sv-benchmarks
//
// SPDX-FileCopyrightText: 2023 Jérôme Boillot <jerome.boillot@ens.fr>
//
// SPDX-License-Identifier: Apache-2.0
//
// We assume sizeof(int)=4.
//
// Corresponds to Figure 3 of "Symbolic transformation of expressions in modular arithmetic"
// combined with Figure 1 (as in `distance_through_overflow.c`).

#include <assert.h>

extern void abort(void);
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }

extern int __VERIFIER_nondet_int();

int main() {
	int x0 = __VERIFIER_nondet_int();
	int x = __VERIFIER_nondet_int();
	int x1 = __VERIFIER_nondet_int();
	int y0 = __VERIFIER_nondet_int();
	int y1 = __VERIFIER_nondet_int();

	if (x < x0 || x > x1 || x0 >= x1 || y1 < y0) abort();
	int r = y0 + (long long) ((unsigned long long) ((unsigned int) x-x0) * ((unsigned int) y1-y0) / ((unsigned int) x1-x0));
	
	__VERIFIER_assert(y0 <= r && r <= y1);
	return 0;
}

