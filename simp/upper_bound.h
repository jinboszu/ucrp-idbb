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

#ifndef UPPER_BOUND_H
#define UPPER_BOUND_H

#include "move.h"
#include "state.h"

/**
 * Solve a state by the JZW heuristic. Be careful that the state will be
 * modified in place.
 *
 * @param state the state
 * @param path array of moves
 * @param len current number of moves
 * @param max_len maximum allowed length
 * @return length of the heuristic solution or INT_MAX if failure occurs
 */
int jzw(state_t *state, move_t *path, int len, int max_len);

/**
 * Solve a state by the SM-2 heuristic. Be careful that the state will be
 * modified in place.
 *
 * @param state the state
 * @param path array of moves
 * @param len current number of moves
 * @param max_len maximum allowed length
 * @return length of the heuristic solution or INT_MAX if failure occurs
 */
int sm2(state_t *state, move_t *path, int len, int max_len);

#endif
