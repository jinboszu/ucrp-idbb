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

#include "upper_bound.h"
#include <limits.h>

int jzw(state_t *state, move_t *path, int len, int max_len) {
  if (len + state->n_bad > max_len) {
    return INT_MAX;
  }

  int n_stacks = state->n_stacks;
  int n_tiers = state->n_tiers;
  int *h = state->h;
  int **p = state->p;
  int **q = state->q;
  int **b = state->b;

  while (state->n_bad > 0) {
    while (is_retrievable(state)) {
      retrieve(state, len);
    }

    int q_min = q[state->s_min][h[state->s_min]];
    int src = -1;
    for (int s = 0; s < n_stacks; s++) {
      int n_empty_slots = (n_stacks - 1) * n_tiers - (state->n_blocks - h[s]);
      if (q[s][h[s]] == q_min && b[s][h[s]] <= n_empty_slots &&
          (src == -1 || b[src][h[src]] > b[s][h[s]])) {
        src = s;
      }
    }
    if (src == -1) {
      return INT_MAX;
    }

    int dst = -1;
    for (int s = 0; s < n_stacks; s++) {
      if (s != src && h[s] < n_tiers && p[src][h[src]] <= q[s][h[s]] &&
          (dst == -1 || q[dst][h[dst]] > q[s][h[s]])) {
        dst = s;
      }
    }

    if (dst != -1) {
      if (h[dst] < n_tiers - 1) {
        int s_pre = -1;
        for (int s = 0; s < n_stacks; s++) {
          if (s != src && s != dst && b[s][h[s]] > 0 &&
              p[src][h[src]] <= p[s][h[s]] && p[s][h[s]] <= q[dst][h[dst]] &&
              (s_pre == -1 || p[s_pre][h[s_pre]] < p[s][h[s]])) {
            s_pre = s;
          }
        }
        if (s_pre != -1) {
          src = s_pre;
        }
      }
    } else {
      if (len + state->n_bad == max_len) {
        return INT_MAX;
      }

      int s_max = -1;
      int s_sec = -1;
      for (int s = 0; s < n_stacks; s++) {
        if (s != src && h[s] < n_tiers) {
          if (s_max == -1 || q[s_max][h[s_max]] < q[s][h[s]]) {
            s_sec = s_max;
            s_max = s;
          } else if (s_sec == -1 || q[s_sec][h[s_sec]] < q[s][h[s]]) {
            s_sec = s;
          }
        }
      }

      int s_opt = -1;
      for (int s = 0; s < n_stacks; s++) {
        if (s != src && h[s] > 0 && b[s][h[s]] == 0 &&
            (s != s_max && p[s][h[s]] <= q[s_max][h[s_max]] ||
             s == s_max && s_sec != -1 && p[s][h[s]] <= q[s_sec][h[s_sec]]) &&
            p[src][h[src]] <= q[s][h[s] - 1] &&
            (s_opt == -1 || p[s_opt][h[s_opt]] < p[s][h[s]])) {
          s_opt = s;
        }
      }

      if (s_opt != -1) {
        src = s_opt;
        for (int s = 0; s < n_stacks; s++) {
          if (s != src && h[s] < n_tiers && p[src][h[src]] <= q[s][h[s]] &&
              (dst == -1 || q[dst][h[dst]] > q[s][h[s]])) {
            dst = s;
          }
        }

        if (h[dst] < n_tiers - 1) {
          int s_pre = -1;
          for (int s = 0; s < n_stacks; s++) {
            if (s != src && s != dst && b[s][h[s]] > 0 &&
                p[src][h[src]] <= p[s][h[s]] && p[s][h[s]] <= q[dst][h[dst]] &&
                (s_pre == -1 || p[s_pre][h[s_pre]] < p[s][h[s]])) {
              s_pre = s;
            }
          }
          if (s_pre != -1) {
            src = s_pre;
          }
        }
      } else {
        dst = s_max;
        if (h[dst] == n_tiers - 1) {
          bool smallest = true;
          for (int k = 1; k < b[src][h[src]]; k++) {
            if (p[src][h[src] - k] < p[src][h[src]]) {
              smallest = false;
              break;
            }
          }
          if (!smallest && s_sec != -1) {
            dst = s_sec;
          }
        }
      }
    }

    if (path != NULL) {
      path[len].p = p[src][h[src]];
      path[len].s = src;
      path[len].d = dst;
    }
    relocate(state, src, dst, ++len);
  }

  return len;
}

int sm2(state_t *state, move_t *path, int len, int max_len) {
  if (len + state->n_bad > max_len) {
    return INT_MAX;
  }

  int n_stacks = state->n_stacks;
  int n_tiers = state->n_tiers;
  int *h = state->h;
  int **p = state->p;
  int **q = state->q;
  int **b = state->b;

  while (state->n_bad > 0) {
    while (is_retrievable(state)) {
      retrieve(state, len);
    }

    int q_min = q[state->s_min][h[state->s_min]];
    int src = -1;
    for (int s = 0; s < n_stacks; s++) {
      int n_empty_slots = (n_stacks - 1) * n_tiers - (state->n_blocks - h[s]);
      if (q[s][h[s]] == q_min && b[s][h[s]] <= n_empty_slots &&
          (src == -1 || b[src][h[src]] > b[s][h[s]])) {
        src = s;
      }
    }
    if (src == -1) {
      return INT_MAX;
    }

    int dst = -1;
    int best_diff = INT_MAX;

    for (int from = 0; from < n_stacks; from++) {
      if (b[from][h[from]] > 0) {
        for (int to = 0; to < n_stacks; to++) {
          int diff = q[to][h[to]] - p[from][h[from]];
          if (from != to && h[to] < n_tiers && diff >= 0 && diff < best_diff) {
            src = from;
            dst = to;
            best_diff = diff;
          }
        }
      }
    }

    if (dst == -1) {
      if (len + state->n_bad == max_len) {
        return INT_MAX;
      }

      for (int from = 0; from < n_stacks; from++) {
        if (b[from][h[from]] == 0) {
          int s_bad = -1;
          int s_bad_alt = -1;
          for (int s = 0; s < n_stacks; s++) {
            if (b[s][h[s]] > 0 && p[s][h[s]] <= q[from][h[from] - 1]) {
              if (s_bad == -1 || p[s_bad][h[s_bad]] < p[s][h[s]]) {
                s_bad_alt = s_bad;
                s_bad = s;
              } else if (s_bad_alt == -1 ||
                         p[s_bad_alt][h[s_bad_alt]] < p[s][h[s]]) {
                s_bad_alt = s;
              }
            }
          }

          if (s_bad != -1) {
            int to = -1;
            int to_alt = -1;
            for (int s = 0; s < n_stacks; s++) {
              if (s != from && h[s] < n_tiers &&
                  p[from][h[from]] <= q[s][h[s]]) {
                if (to == -1 || q[to][h[to]] > q[s][h[s]]) {
                  to_alt = to;
                  to = s;
                } else if (to_alt == -1 || q[to_alt][h[to_alt]] > q[s][h[s]]) {
                  to_alt = s;
                }
              }
            }

            if (to != -1) {
              if (s_bad != to) {
                int diff = q[from][h[from] - 1] - p[s_bad][h[s_bad]] +
                           q[to][h[to]] - p[from][h[from]];
                if (diff < best_diff) {
                  src = from;
                  dst = to;
                  best_diff = diff;
                }
              } else {
                if (s_bad_alt != -1) {
                  int diff = q[from][h[from] - 1] - p[s_bad_alt][h[s_bad_alt]] +
                             q[to][h[to]] - p[from][h[from]];
                  if (diff < best_diff) {
                    src = from;
                    dst = to;
                    best_diff = diff;
                  }
                }
                if (to_alt != -1) {
                  int diff = q[from][h[from] - 1] - p[s_bad][h[s_bad]] +
                             q[to_alt][h[to_alt]] - p[from][h[from]];
                  if (diff < best_diff) {
                    src = from;
                    dst = to;
                    best_diff = diff;
                  }
                }
              }
            }
          }
        }
      }

      if (dst == -1) {
        for (int s = 0; s < n_stacks; s++) {
          if (s != src && h[s] < n_tiers &&
              (dst == -1 || q[dst][h[dst]] < q[s][h[s]])) {
            dst = s;
          }
        }
      }
    }

    if (path != NULL) {
      path[len].p = p[src][h[src]];
      path[len].s = src;
      path[len].d = dst;
    }
    relocate(state, src, dst, ++len);
  }

  return len;
}
