// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
/**
 * Certified Null Operation in C
 *
 * A program that does absolutely nothing at the application level.
 * Returns 0 (success) without any side effects.
 *
 * Properties:
 * - Terminates immediately
 * - No I/O operations
 * - No memory allocation
 * - Exit code 0
 */

int main(void) {
    return 0;
}

/*
 * Verification notes:
 * - Startup code (crt0) runs before main
 * - At assembly level, registers are modified
 * - At logical level: CNO
 * - At physical level: CPU cycles consumed
 *
 * This demonstrates the gap between logical and physical computation.
 */
