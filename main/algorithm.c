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

#include "algorithm.h"
#include "lower_bound.h"
#include "timer.h"
#include "upper_bound.h"
#include <limits.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
  int lb;
  state_t *state;
} node_t;

typedef struct {
  int pri;
  int src;
  int dst;
  int q_src;
  int q_dst;
  int child_lb;
  state_t *child_state;
} branch_t;

static int compare_branch(const void *a, const void *b) {
  branch_t *x = (branch_t *)a;
  branch_t *y = (branch_t *)b;
  return x->child_lb != y->child_lb ? x->child_lb - y->child_lb
         : x->q_dst != y->q_dst     ? y->q_dst - x->q_dst
                                    : x->q_src - y->q_src;
}

/*
 * Temporary variables
 */
static state_t *root_state;          // for initialization
static state_t *probe_state;         // for probing
static int *array_s1;                // for lower bounding
static int *min_last_change_left;    // for Rule 3 (TC)
static int *max_last_move_out_right; // for Rule 4 (IB)
static int *max_group_src_temp;      // for Rules 10 (SC)
static int *max_group_src_right;     // for Rule 10 (SC)
static int *max_group_dst_right;     // for Rule 11 (SD)
static move_t *path;                 // for branch-and-bound
static node_t *hist;                 // for branch-and-bound
static state_t *temp_state;          // for branch-and-bound
static branch_t *pool;               // for branch-and-bound

/*
 * Parameters
 */
static int n_stacks;
static int n_tiers;
static int max_prio;

/*
 * Report
 */
static int best_lb;
static int best_ub;
static move_t *best_sol;
static double start_time;
static double end_time;
static double time_to_best_lb;
static double time_to_best_ub;
static long n_nodes;
static long n_probe;

/*
 * Timer
 */
static long n_timer;
static long timer_cycle;

static void debug_info(char *status) {
  fprintf(stdout,
          "[%s] best_lb = %d @ %.3f / best_ub = %d @ %.3f / time = %.3f / "
          "nodes = %ld / probe = %ld\n",
          status, best_lb, time_to_best_lb - start_time, best_ub,
          time_to_best_ub - start_time, get_time() - start_time, n_nodes,
          n_probe);
  fflush(stdout);
}

/*
 * Branch-and-bound
 */
static bool search(int level, branch_t *branches) {
  n_nodes++;

  /*
   * Check time limit
   */
  if (++n_timer == timer_cycle) {
    n_timer = 0;
    if (get_time() >= end_time) {
      return true;
    }
    debug_info("running");
  }

  /*
   * Current state
   */
  int curr_lb = hist[level].lb;
  state_t *curr_state = hist[level].state;

  /*
   * Prepare Rule 3 (TC)
   *
   * min_last_change_left[s] = min{last_change_time[s'] | s' < s && h[s'] <
   * n_tiers}
   */
  int min_last_change_temp = INT_MAX;
  for (int s = 0; s < n_stacks; s++) {
    min_last_change_left[s] = min_last_change_temp;
    if (curr_state->h[s] < n_tiers &&
        min_last_change_temp > curr_state->last_change_time[s]) {
      min_last_change_temp = curr_state->last_change_time[s];
    }
  }

  /*
   * Prepare Rule 4 (IB)
   *
   * max_last_move_out_right[s] = max{last_move_out_time[s'] | s' > s}
   */
  int max_last_move_out_temp = 0;
  for (int s = n_stacks - 1; s >= 0; s--) {
    max_last_move_out_right[s] = max_last_move_out_temp;
    if (max_last_move_out_temp < curr_state->last_move_out_time[s]) {
      max_last_move_out_temp = curr_state->last_move_out_time[s];
    }
  }

  /*
   * Prepare Rule 10 (SC)
   *
   * max_group_src_right[s] = max{k | pk == p[s][h[s]] && sk > s &&
   * last_change_type[sk] == MOVE_OUT}
   */
  int min_prio =
      curr_state->q[curr_state->list[0]][curr_state->h[curr_state->list[0]]];
  memset(max_group_src_temp + min_prio + 1, 0,
         sizeof(int) * (max_prio - min_prio));
  for (int s = n_stacks - 1; s >= 0; s--) {
    max_group_src_right[s] =
        curr_state->h[s] == 0
            ? 0
            : max_group_src_temp[curr_state->p[s][curr_state->h[s]]];
    if (curr_state->last_change_type[s] == MOVE_OUT) {
      int k = curr_state->last_change_time[s];
      int pk = path[k - 1].p;
      if (pk > min_prio && max_group_src_temp[pk] < k) {
        max_group_src_temp[pk] = k;
      }
    }
  }

  /*
   * Prepare lower bounding
   */
  int s_max = -1;
  int s_sec = -1;
  for (int i = n_stacks - 1; i >= 0; i--) {
    int s = curr_state->list[i];
    if (curr_state->h[s] < n_tiers) {
      if (s_max == -1) {
        s_max = s;
      } else {
        s_sec = s;
        break;
      }
    }
  }

  /*
   * Prepare branching
   */
  int size = 0;

  /*
   * Enumerate source stack
   */
  bool first_sn = true;
  for (int sn = 0; sn < n_stacks; sn++) {
    /*
     * Check feasibility
     */
    if (curr_state->h[sn] == 0 ||
        curr_state->n_blocks - curr_state->h[sn] == (n_stacks - 1) * n_tiers) {
      continue;
    }

    int pn = curr_state->p[sn][curr_state->h[sn]];   // priority value
    int q_sn = curr_state->q[sn][curr_state->h[sn]]; // quality value
    int lv = curr_state->l[sn][curr_state->h[sn]];   // last relocation time

    /*
     * Lower bounding
     */
    bool to_be_bad = pn > curr_state->q[s_max][curr_state->h[s_max]] ||
                     (sn == s_max && s_sec != -1 &&
                      pn > curr_state->q[s_sec][curr_state->h[s_sec]]);
    if (level + 1 + curr_lb - (pn > q_sn) + to_be_bad -
            (curr_lb > curr_state->n_bad && (pn <= q_sn || to_be_bad)) >
        best_lb) {
      continue;
    }

    if (lv > 0) {
      int k = lv; // last time the block is relocated
      int sk = path[k - 1].s;

      /*
       * Check Rule 1 (TA)
       */
      if (curr_state->last_change_time[sk] == k &&
          curr_state->last_change_type[sk] == MOVE_OUT) {
        continue; // TA: merge two relocations and perform later
      }
    }

    /*
     * Check Rule 3 (TC)
     *
     * if exists s' < sn such that h[s'] < n_tiers && last_change_time[s'] < k
     *
     * min_last_change_left[s] = min{last_change_time[s'] | s' < s && h[s'] <
     * n_tiers}
     */
    if (min_last_change_left[sn] < lv) {
      continue; // TC: choose alternative transitive stack
    }

    /*
     * Check Rule 10 (SC)
     *
     * if exists k > last_change_time[sn] such that pk = pn && sk > sn &&
     * last_change_type[sk] == MOVE_OUT
     *
     * max_group_src_right[s] = max{k | pk == p[s][h[s]] && sk > s &&
     * last_change_type[sk] == MOVE_OUT}
     */
    if (curr_state->last_change_time[sn] < max_group_src_right[sn]) {
      continue; // SC: swap source stacks of two relocations
    }

    /*
     * Prepare Rule 11 (SD)
     *
     * max_group_dst_right[d] = max{k | pk == pn && dk > d &&
     * last_change_type[dk] == MOVE_IN}
     */
    int max_group_dst_temp = 0;
    for (int d = n_stacks - 1; d >= 0; d--) {
      max_group_dst_right[d] = max_group_dst_temp;
      if (curr_state->last_change_type[d] == MOVE_IN) {
        int k = curr_state->last_change_time[d];
        int pk = path[k - 1].p;
        if (pk == pn && max_group_dst_temp < k) {
          max_group_dst_temp = k;
        }
      }
    }

    /*
     * Enumerate destination stack
     */
    bool first_dn = true;
    bool first_empty = true;
    for (int dn = 0; dn < n_stacks; dn++) {
      /*
       * Check feasibility
       */
      if (dn == sn || curr_state->h[dn] == n_tiers) {
        continue;
      }

      /*
       * Update path when generating branches
       */
      path[level].p = pn;
      path[level].s = sn;
      path[level].d = dn;

      /*
       * Goal test
       */
      int q_dn = curr_state->q[dn][curr_state->h[dn]];
      if (curr_state->n_bad - (pn > q_sn) + (pn > q_dn) == 0) {
        best_ub = level + 1;
        memcpy(best_sol, path, sizeof(move_t) * best_ub);
        time_to_best_ub = get_time();
        debug_info("goal");
        return true;
      }

      /*
       * Check Rule 7 (EA)
       */
      if (curr_state->h[dn] == 0) {
        if (first_empty) {
          first_empty = false;
        } else {
          continue; // EA: choose the leftmost empty stack
        }
      }

      /*
       * Check Rule 2 (TB)
       */
      if (curr_state->last_change_time[dn] < lv) {
        continue; // TB: merge two relocations and perform earlier
      }

      /*
       * Check Rule 4 (IB)
       *
       * if exists s' > s such that last_move_out_time[s'] >
       * max{last_change_time[sn], last_change_time[dn]}
       *
       * max_last_move_out_right[s] = max{last_move_out_time[s'] | s' > s}
       */
      if (curr_state->last_change_time[sn] < max_last_move_out_right[sn] &&
          curr_state->last_change_time[dn] < max_last_move_out_right[sn]) {
        continue; // IB: perform (pn, sn, dn) before (*, s', *)
      }

      if (curr_state->last_change_type[dn] == MOVE_OUT) {
        int k = curr_state->last_change_time[dn];
        int pk = path[k - 1].p;
        int dk = path[k - 1].d;
        if (pk == pn) {
          /*
           * Check Rule 8 (SA)
           */
          if (curr_state->last_change_time[sn] < k) {
            continue; // SA: merge two relocations and perform earlier
          }

          /*
           * Check Rule 9 (SB)
           */
          if (curr_state->last_change_time[dk] == k) {
            continue; // SB: merge two relocations and perform later
          }
        }
      }

      /*
       * Check Rule 11 (SD)
       *
       * if exists k > last_change_time[dn] such that pk = pn && dk > dn &&
       * last_change_type[dk] == MOVE_IN
       *
       * max_group_dst_right[d] = max{k | pk == pn && dk > d &&
       * last_change_type[dk] == MOVE_IN}
       */
      if (curr_state->last_change_time[dn] < max_group_dst_right[dn]) {
        continue; // SD: swap destination stacks of two relocations
      }

      /*
       * Lower bounding
       */
      if (level + 1 + curr_lb - (pn > q_sn) + (pn > q_dn) -
              (curr_lb > curr_state->n_bad && (pn <= q_sn || pn > q_dn)) >
          best_lb) {
        continue;
      }

      /*
       * Child state
       */
      if (first_sn) {
        first_sn = false;
        copy_state_body(hist[level + 1].state, curr_state);
      }
      if (first_dn) {
        first_dn = false;
        copy_state_head(temp_state, curr_state);
        reuse_state_body(temp_state, hist[level + 1].state);
        move_out(temp_state, sn, level + 1);
      }
      state_t *child_state = branches[size].child_state;
      copy_state_head(child_state, temp_state);
      reuse_state_body(child_state, hist[level + 1].state);
      move_in(child_state, dn, pn, level + 1);

      /*
       * Retrieve
       */
      bool dominated = false;
      while (is_retrievable(child_state)) {
        int s_min = child_state->list[0];
        int p = child_state->p[s_min][child_state->h[s_min]];
        int l = child_state->l[s_min][child_state->h[s_min]];

        if (l > 0) {
          int k = l;
          int sk = path[k - 1].s;

          /*
           * Check Rule 5 (RA)
           */
          if (child_state->last_move_out_time[sk] == k &&
              child_state->last_move_in_time[sk] < k &&
              hist[k - 1].state->q[sk][hist[k - 1].state->h[sk]] == p) {
            dominated = true; // RA: k-th relocation can be left out
            break;            // no need to continue retrievals
          }

          for (int d = 0; d < s_min; d++) {
            /*
             * Check Rule 6 (RB)
             */
            if (hist[k - 1].state->h[d] < n_tiers &&
                child_state->last_move_out_time[d] < k &&
                child_state->last_move_in_time[d] < k &&
                hist[k - 1].state->q[d][hist[k - 1].state->h[d]] >= p) {
              dominated = true; // RB: choose alternative transitive stack
              break; // no need to find more alternative transitive stack
            }
          }
          if (dominated) {
            break; // no need to continue retrievals
          }
        }

        retrieve(child_state, level + 1);
      }

      if (dominated) {
        continue; // dominated according to RA or RB
      }

      /*
       * Child lower bound
       */
      int child_lb =
          lb_ts(child_state, best_lb - level - child_state->n_bad, array_s1);

      /*
       * Lower bounding
       */
      if (level + 1 + child_lb > best_lb) {
        continue;
      }

      /*
       * Probing
       */
      if (level + 1 + child_lb == best_lb - 1) {
        n_probe++;

        copy_state(probe_state, child_state);
        int new_len_jzw = jzw(probe_state, path, level + 1, best_ub - 1);
        if (new_len_jzw != INT_MAX) {
          best_ub = new_len_jzw;
          memcpy(best_sol, path, sizeof(move_t) * best_ub);
          time_to_best_ub = get_time();
          debug_info("update");
          if (best_lb == best_ub) {
            return true;
          }
        }

        copy_state(probe_state, child_state);
        int new_len_sm2 = sm2(probe_state, path, level + 1, best_ub - 1);
        if (new_len_sm2 != INT_MAX) {
          best_ub = new_len_sm2;
          memcpy(best_sol, path, sizeof(move_t) * best_ub);
          time_to_best_ub = get_time();
          debug_info("update");
          if (best_lb == best_ub) {
            return true;
          }
        }
      }

      /*
       * Non-dominated branches
       */
      branches[size].pri = pn;
      branches[size].src = sn;
      branches[size].dst = dn;
      branches[size].q_src = q_sn;
      branches[size].q_dst = q_dn;
      branches[size].child_lb = child_lb;
      size++;
    }
  }

  /*
   * Depth-first search
   */
  if (size > 0) {
    qsort(branches, size, sizeof(branch_t), compare_branch);

    for (int i = 0; i < size; i++) {
      path[level].p = branches[i].pri;
      path[level].s = branches[i].src;
      path[level].d = branches[i].dst;

      hist[level + 1].lb = branches[i].child_lb;
      reuse_state_head(hist[level + 1].state, branches[i].child_state);

      int dn = path[level].d;
      if (hist[level + 1].state->h[dn] == curr_state->h[dn] + 1) {
        update_slot(hist[level + 1].state, dn, hist[level + 1].state->h[dn],
                    path[level].p, level + 1);
      }

      if (search(level + 1, branches + size)) {
        return true;
      }
    }
  }

  return false;
}

report_t *solve(instance_t *inst, int _t) {
  /*
   * Parameters
   */
  n_stacks = inst->n_stacks;
  n_tiers = inst->n_tiers;
  max_prio = inst->max_prio;
  start_time = get_time();
  end_time = start_time + _t;

  /*
   * Root state
   */
  root_state = malloc_state(n_stacks, n_tiers, true, true, true);
  init_state(root_state, inst);
  while (is_retrievable(root_state)) {
    retrieve(root_state, 0);
  }
  if (root_state->n_blocks == 0) {
    free_state(root_state);
    return new_report(0, 0, 0, 0, NULL, 0, 0, 0, 0, 0);
  }

  /*
   * Check if there is a solution
   */
  probe_state = malloc_state(n_stacks, n_tiers, true, true, false);
  copy_state(probe_state, root_state);
  int init_len_jzw = jzw(probe_state, NULL, 0, INT_MAX);
  copy_state(probe_state, root_state);
  int init_len_sm2 = sm2(probe_state, NULL, 0, INT_MAX);
  int max_depth = init_len_jzw < init_len_sm2 ? init_len_jzw : init_len_sm2;
  if (max_depth == INT_MAX) {
    free_state(root_state);
    free_state(probe_state);
    return NULL;
  }

  /*
   * Temporary variables for lower bounding
   */
  array_s1 = malloc(sizeof(int) * n_stacks);

  /*
   * Temporary variables for branch-and-bound
   */
  min_last_change_left = malloc(sizeof(int) * n_stacks);
  max_last_move_out_right = malloc(sizeof(int) * n_stacks);
  max_group_src_temp = malloc(sizeof(int) * (max_prio + 1));
  max_group_src_right = malloc(sizeof(int) * n_stacks);
  max_group_dst_right = malloc(sizeof(int) * n_stacks);

  path = malloc(sizeof(move_t) * max_depth);
  hist = malloc(sizeof(node_t) * (max_depth + 1));
  for (int i = 1; i <= max_depth; i++) {
    hist[i].state = malloc_state(n_stacks, n_tiers, false, true, true);
  }
  temp_state = malloc_state(n_stacks, n_tiers, true, false, true);
  pool = malloc(sizeof(branch_t) * max_depth * n_stacks * (n_stacks - 1));
  for (int i = 0; i < max_depth * n_stacks * (n_stacks - 1); i++) {
    pool[i].child_state = malloc_state(n_stacks, n_tiers, true, false, true);
  }

  /*
   * Root lower bound
   */
  int root_lb = lb_ts(root_state, INT_MAX, array_s1);

  /*
   * Initialize best lower and upper bounds
   */
  best_lb = root_lb;
  time_to_best_lb = start_time;
  best_sol = malloc(sizeof(move_t) * max_depth);
  copy_state(probe_state, root_state);
  best_ub = init_len_jzw < init_len_sm2
                ? jzw(probe_state, best_sol, 0, INT_MAX)
                : sm2(probe_state, best_sol, 0, INT_MAX);
  time_to_best_ub = start_time;

  /*
   * Initialize history
   */
  hist[0].lb = root_lb;
  hist[0].state = root_state;

  /*
   * Iterative deepening search
   */
  n_nodes = 0;
  n_probe = 0;
  n_timer = 0;
  timer_cycle = 1000000;

  debug_info("start");
  while (best_lb < best_ub) {
    if (search(0, pool)) {
      break;
    }
    best_lb++;
    time_to_best_lb = get_time();
    debug_info("deepen");
  }
  debug_info("end");

  /*
   * Free temporary variables
   */
  free_state(root_state);
  free_state(probe_state);
  free(array_s1);
  free(min_last_change_left);
  free(max_last_move_out_right);
  free(max_group_src_temp);
  free(max_group_src_right);
  free(max_group_dst_right);
  free(path);
  for (int i = 1; i <= max_depth; i++) {
    free_state(hist[i].state);
  }
  free(hist);
  free_state(temp_state);
  for (int i = 0; i < max_depth * n_stacks * (n_stacks - 1); i++) {
    free_state(pool[i].child_state);
  }
  free(pool);

  /*
   * Report
   */
  report_t *report =
      new_report(root_lb, max_depth, best_lb, best_ub, best_sol,
                 time_to_best_lb - start_time, time_to_best_ub - start_time,
                 get_time() - start_time, n_nodes, n_probe);
  free(best_sol);
  return report;
}
