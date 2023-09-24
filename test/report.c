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

#include "report.h"
#include <stdlib.h>
#include <string.h>

report_t *new_report(int init_lb, int init_ub, int best_lb, int best_ub,
                     move_t *best_sol, double time_to_best_lb,
                     double time_to_best_ub, double time_used, long n_nodes,
                     long n_probe) {
  report_t *report = malloc(sizeof(report_t));
  report->init_lb = init_lb;
  report->init_ub = init_ub;
  report->best_lb = best_lb;
  report->best_ub = best_ub;
  report->best_sol = best_sol == NULL
                         ? NULL
                         : memcpy(malloc(sizeof(move_t) * best_ub), best_sol,
                                  sizeof(move_t) * best_ub);
  report->time_to_best_lb = time_to_best_lb;
  report->time_to_best_ub = time_to_best_ub;
  report->time_used = time_used;
  report->n_nodes = n_nodes;
  report->n_probe = n_probe;
  return report;
}

void free_report(report_t *report) {
  if (report->best_sol != NULL) {
    free(report->best_sol);
  }
  free(report);
}
