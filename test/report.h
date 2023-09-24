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

#ifndef REPORT_H
#define REPORT_H

#include "move.h"

typedef struct {
  int init_lb;            // initial lower bound
  int init_ub;            // initial upper bound
  int best_lb;            // best lower bound
  int best_ub;            // best upper bound
  move_t *best_sol;       // best solution
  double time_to_best_lb; // time to the best lower bound
  double time_to_best_ub; // time to the best upper bound
  double time_used;       // total time used in seconds
  long n_nodes;           // number of nodes explored
  long n_probe;           // number of nodes probed
} report_t;

/**
 * Create a report
 *
 * @param init_lb initial lower bound
 * @param init_ub initial upper bound
 * @param best_lb best lower bound
 * @param best_ub best upper bound
 * @param best_sol best solution
 * @param time_to_best_lb time to the best lower bound
 * @param time_to_best_ub time to the best upper bound
 * @param time_used total time used in seconds
 * @param n_nodes number of nodes explored
 * @param n_probe number of nodes probed
 * @return created report
 */
report_t *new_report(int init_lb, int init_ub, int best_lb, int best_ub,
                     move_t *best_sol, double time_to_best_lb,
                     double time_to_best_ub, double time_used, long n_nodes,
                     long n_probe);

/**
 * Free the space of a report
 *
 * @param report pointer to the report
 */
void free_report(report_t *report);

#endif
