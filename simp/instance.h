/*
 * Copyright (c) 2023 Bo Jin <jinbostar@gmail.com>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

#ifndef INSTANCE_H
#define INSTANCE_H

#include <stdio.h>

typedef struct {
  int n_stacks; // number of stacks, indexed from 0 to n_stacks - 1
  int n_tiers;  // number of tiers, indexed from 1 to n_tiers
  int n_blocks; // number of blocks
  int max_prio; // maximum priority
  int *h;       // height array
  int **p;      // priority matrix
} instance_t;

/**
 * Create space for an instance
 *
 * @param n_stacks number of stacks
 * @param n_tiers number of tiers
 * @return created instance
 */
instance_t *malloc_instance(int n_stacks, int n_tiers);

/**
 * Free the space of an instance
 *
 * @param inst the instance
 */
void free_instance(instance_t *inst);

/**
 * Read an instance from file
 *
 * @param input input file name
 * @return created instance
 */
instance_t *read_instance(char *input);

/**
 * Print an instance
 *
 * @param fp output stream
 * @param inst the instance
 */
void print_instance(FILE *fp, instance_t *inst);

#endif
