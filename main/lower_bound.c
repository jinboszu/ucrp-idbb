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

#include "lower_bound.h"
#include <limits.h>
#include <string.h>

/*
 * LB-TS
 */

int lb_ts(state_t *state, int max_k, int *h) {
  if (state->n_bad == 0 || max_k == 0 || has_empty_stack(state)) {
    return state->n_bad;
  }

  int n_stacks = state->n_stacks;
  int n_tiers = state->n_tiers;
  int **p = state->p; // p[s][t]: priority
  int **q = state->q; // q[s][t]: quality, i.e., smallest among p[s][1...h[s]]
  int **b = state->b; // b[s][t]: badness, i.e., number of consecutive
                      // badly-placed blocks

  int remain = state->n_bad;
  memcpy(h, state->h, sizeof(int) * n_stacks);

  int k = 0;
  while (true) {
    int s_min = -1;
    int q_min = INT_MAX;
    int q_max = 0;
    for (int s = 0; s < n_stacks; s++) {
      if (q_min > q[s][h[s]] ||
          (q_min == q[s][h[s]] && p[s_min][h[s_min]] <= p[s][h[s]])) {
        s_min = s;
        q_min = q[s][h[s]];
      }
      if (h[s] < n_tiers && q_max < q[s][h[s]]) {
        q_max = q[s][h[s]];
      }
    }

    int p_min = INT_MAX;
    int p_min_bad = INT_MAX;
    for (int v = 0; v < n_stacks;) {
      if (p[v][h[v]] == q_min) {
        if (--h[v] == 0) {
          return state->n_bad + k;
        }

        if (v == s_min && q[v][h[v]] > q_min) {
          s_min = -1;
          q_min = INT_MAX;
          for (int s = 0; s < n_stacks; s++) {
            if (q_min > q[s][h[s]] ||
                (q_min == q[s][h[s]] && p[s_min][h[s_min]] <= p[s][h[s]])) {
              s_min = s;
              q_min = q[s][h[s]];
            }
          }
        }
        if (q_max < q[v][h[v]]) {
          q_max = q[v][h[v]];
        }
        if (p_min <= q_min || p_min_bad <= q_max) {
          v = 0;
          p_min = INT_MAX;
          p_min_bad = INT_MAX;
        }
      } else if (b[v][h[v]] > 0 && p[v][h[v]] <= q_max) {
        if (--remain == 0 || --h[v] == 0) {
          return state->n_bad + k;
        }
      } else {
        if (p_min > p[v][h[v]]) {
          p_min = p[v][h[v]];
        }
        if (b[v][h[v]] > 0 && p_min_bad > p[v][h[v]]) {
          p_min_bad = p[v][h[v]];
        }
        v++;
      }
    }
    if (++k == max_k) {
      return state->n_bad + k;
    }
    for (int s = 0; s < n_stacks; s++) {
      if ((b[s][h[s]] > 0 && --remain == 0) || --h[s] == 0) {
        return state->n_bad + k;
      }
    }
  }
}
