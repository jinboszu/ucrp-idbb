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

#ifndef STATE_H
#define STATE_H

#include "instance.h"
#include <stdbool.h>

enum { NEVER, MOVE_OUT, MOVE_IN, RETRIEVE };

typedef struct {
  int n_stacks; // number of stacks, indexed from 0 to n_stacks - 1
  int n_tiers;  // number of tiers, indexed from 1 to n_tiers (0 is ground)

  int n_blocks;          // number of blocks
  int n_bad;             // number of badly-placed blocks
  int s_min;             // target stack
  int *h;                // h[s]: height of stack s
  int *last_change_time; // last_change_time[s]: time of last change to stack s
  int *last_change_type; // last_change_type[s]: type of last change to stack s
  int *last_move_out_time; // last_move_out_time[s]: time of last relocation
                           // moving out of stack s
  int *last_move_in_time;  // last_move_in_time[s]: time of last relocation
                           // moving into stack s

  int **p; // p[s][t]: priority
  int **q; // q[s][t]: quality, i.e., smallest among p[s][1...h[s]]
  int **b; // b[s][t]: badness, i.e., number of consecutive badly-placed blocks
  int **l; // l[s][t]: time when the block is put into slot (s, t)
} state_t;

/**
 * Create space for a state
 *
 * @param n_stacks number of stacks
 * @param n_tiers number of tiers
 * @return created state
 */
state_t *malloc_state(int n_stacks, int n_tiers);

/**
 * Free the space of a state
 *
 * @param state the state
 */
void free_state(state_t *state);

/**
 * Copy a state
 *
 * @param dst_state destination state
 * @param src_state source state
 */
void copy_state(state_t *dst_state, state_t *src_state);

/**
 * Check if the target block is retrievable
 *
 * @param state the state
 * @return true if the target block is retrievable
 */
bool is_retrievable(state_t *state);

/**
 * Initialize a state from an instance
 *
 * @param state the state
 * @param inst the instance
 */
void init_state(state_t *state, instance_t *inst);

/**
 * Relocate the topmost block of a stack to another stack
 *
 * @param state the state
 * @param s source stack
 * @param d destination stack
 * @param l time of this relocation
 */
void relocate(state_t *state, int s, int d, int l);

/**
 * Retrieve the target block from the top of the target stack
 *
 * @param state the state
 * @param l time of this retrieval
 */
void retrieve(state_t *state, int l);

#endif
