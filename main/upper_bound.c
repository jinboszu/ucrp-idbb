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
  int *list = state->list;
  int *rank = state->rank;
  int **p = state->p;
  int **q = state->q;
  int **b = state->b;

  while (state->n_bad > 0) {
    while (is_retrievable(state)) {
      retrieve(state, len);
    }

    int q_min = q[list[0]][h[list[0]]];
    int i_next = -1;
    for (int i = 0; i < n_stacks; i++) {
      int s = list[i];
      if (q[s][h[s]] > q_min) {
        break;
      }
      int n_empty_slots = (n_stacks - 1) * n_tiers - (state->n_blocks - h[s]);
      if (b[s][h[s]] <= n_empty_slots) {
        i_next = i;
        break;
      }
    }
    if (i_next == -1) {
      return INT_MAX;
    }

    int i_max;
    int q_max;
    for (int i = n_stacks - 1;; i--) {
      int s = list[i];
      if (i != i_next && h[s] < n_tiers) {
        i_max = i;
        q_max = q[s][h[s]];
        break;
      }
    }

    bool has_multi_q_max = false;
    if (q_min < q_max) {
      for (int i = i_max - 1;; i--) {
        int s = list[i];
        if (q[s][h[s]] < q_max) {
          break;
        }
        if (h[s] < n_tiers) {
          has_multi_q_max = true;
          break;
        }
      }
    }

    int src = list[i_next];
    int dst;

    if (p[src][h[src]] <= q_max) {
      for (int i = i_next + 1;; i++) {
        int s = list[i];
        if (h[s] < n_tiers && p[src][h[src]] <= q[s][h[s]]) {
          dst = s;
          break;
        }
      }

      if (h[dst] < n_tiers - 1) {
        int s_pre = -1;
        for (int i = 0; i < rank[dst]; i++) {
          int s = list[i];
          if (s != src && b[s][h[s]] > 0 && p[src][h[src]] <= p[s][h[s]] &&
              p[s][h[s]] <= q[dst][h[dst]] &&
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

      int i_opt = -1;
      for (int dir = 1, i = i_max;; i += dir) {
        if (i == n_stacks || (i > i_max && q[list[i]][h[list[i]]] > q_max)) {
          i = i_max + (dir = -1);
        }
        int s = list[i];
        if (q[s][h[s]] == q_min) {
          break;
        }
        if (b[s][h[s]] == 0 && p[src][h[src]] <= q[s][h[s] - 1] &&
            (i != i_max || has_multi_q_max)) {
          i_opt = i;
          break;
        }
      }

      if (i_opt != -1) {
        src = list[i_opt];
        for (int dir = -1, i = i_opt + dir;; i += dir) {
          if (i < i_opt && q[list[i]][h[list[i]]] < p[src][h[src]]) {
            i = i_opt + (dir = 1);
          }
          int s = list[i];
          if (h[s] < n_tiers) {
            dst = s;
            break;
          }
        }

        if (h[dst] < n_tiers - 1) {
          int s_pre = -1;
          for (int i = 0; i < rank[dst]; i++) {
            int s = list[i];
            if (s != src && b[s][h[s]] > 0 && p[src][h[src]] <= p[s][h[s]] &&
                p[s][h[s]] <= q[dst][h[dst]] &&
                (s_pre == -1 || p[s_pre][h[s_pre]] < p[s][h[s]])) {
              s_pre = s;
            }
          }
          if (s_pre != -1) {
            src = s_pre;
          }
        }
      } else {
        dst = list[i_max];
        if (h[dst] == n_tiers - 1) {
          bool smallest = true;
          for (int k = 1; k < b[src][h[src]]; k++) {
            if (p[src][h[src] - k] < p[src][h[src]]) {
              smallest = false;
              break;
            }
          }
          if (!smallest) {
            for (int i = i_max - 1; i >= 0; i--) {
              int s = list[i];
              if (s != src && h[s] < n_tiers) {
                dst = s;
                break;
              }
            }
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
  int *list = state->list;
  int *rank = state->rank;
  int **p = state->p;
  int **q = state->q;
  int **b = state->b;

  while (state->n_bad > 0) {
    while (is_retrievable(state)) {
      retrieve(state, len);
    }

    int q_min = q[list[0]][h[list[0]]];
    int i_next = -1;
    for (int i = 0; i < n_stacks; i++) {
      int s = list[i];
      if (q[s][h[s]] > q_min) {
        break;
      }
      int n_empty_slots = (n_stacks - 1) * n_tiers - (state->n_blocks - h[s]);
      if (b[s][h[s]] <= n_empty_slots) {
        i_next = i;
        break;
      }
    }
    if (i_next == -1) {
      return INT_MAX;
    }

    int i_max;
    int q_max;
    for (int i = n_stacks - 1;; i--) {
      int s = list[i];
      if (i != i_next && h[s] < n_tiers) {
        i_max = i;
        q_max = q[s][h[s]];
        break;
      }
    }

    bool has_multi_q_max = false;
    if (q_min < q_max) {
      for (int i = i_max - 1;; i--) {
        int s = list[i];
        if (q[s][h[s]] < q_max) {
          break;
        }
        if (h[s] < n_tiers) {
          has_multi_q_max = true;
          break;
        }
      }
    }

    int src = -1;
    int dst = -1;
    int best_diff = INT_MAX;

    if (q_min < q_max) {
      for (int i = 0; i < i_max; i++) {
        int from = list[i];
        if (h[from] == 0) {
          break;
        }
        if (b[from][h[from]] > 0 && p[from][h[from]] <= q_max) {
          for (int j = i + 1;; j++) {
            int to = list[j];
            int diff = q[to][h[to]] - p[from][h[from]];
            if (diff >= best_diff) {
              break;
            }
            if (h[to] < n_tiers && diff >= 0) {
              src = from;
              dst = to;
              best_diff = diff;
              break;
            }
          }
        }
      }
    }

    if (best_diff == INT_MAX) {
      if (len + state->n_bad == max_len) {
        return INT_MAX;
      }

      if (q_min < q_max) {
        for (int i = 0; i < n_stacks; i++) {
          int from = list[i];
          if (q[from][h[from]] > q_max) {
            break;
          }
          if (b[from][h[from]] == 0 && (i != i_max || has_multi_q_max)) {
            int s_bad = -1;
            int s_bad_alt = -1;
            for (int j = 0; j < n_stacks; j++) {
              int s = list[j];
              if (q[s][h[s]] >= q[from][h[from] - 1]) {
                break;
              }
              int diff = q[from][h[from] - 1] - p[s][h[s]];
              if (b[s][h[s]] > 0 && diff >= 0 && diff < best_diff) {
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
              for (int dir = -1, j = i + dir;; j += dir) {
                if (dir == -1 && q[list[j]][h[list[j]]] < p[from][h[from]]) {
                  j = i + (dir = 1);
                }
                int s = list[j];
                int diff = q[from][h[from] - 1] - p[s_bad][h[s_bad]] +
                           q[s][h[s]] - p[from][h[from]];
                if (diff >= best_diff) {
                  break;
                }
                if (h[s] < n_tiers) {
                  to = s;
                  break;
                }
              }

              if (to != -1) {
                if (s_bad != to) {
                  src = from;
                  dst = to;
                  best_diff = q[from][h[from] - 1] - p[s_bad][h[s_bad]] +
                              q[to][h[to]] - p[from][h[from]];
                } else {
                  if (s_bad_alt != -1) {
                    int diff = q[from][h[from] - 1] -
                               p[s_bad_alt][h[s_bad_alt]] + q[to][h[to]] -
                               p[from][h[from]];
                    if (diff < best_diff) {
                      src = from;
                      dst = to;
                      best_diff = diff;
                    }
                  }
                  for (int dir = (rank[to] < i ? -1 : 1), j = rank[to] + dir;
                       j <= i_max; j += dir) {
                    if (dir == -1 &&
                        q[list[j]][h[list[j]]] < p[from][h[from]]) {
                      j = i + (dir = 1);
                    }
                    int s = list[j];
                    int diff = q[from][h[from] - 1] - p[s_bad][h[s_bad]] +
                               q[s][h[s]] - p[from][h[from]];
                    if (diff >= best_diff) {
                      break;
                    }
                    if (h[s] < n_tiers) {
                      src = from;
                      dst = s;
                      best_diff = diff;
                      break;
                    }
                  }
                }
              }
            }
          }
        }
      }

      if (src == -1) {
        src = list[i_next];
        dst = list[i_max];
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
