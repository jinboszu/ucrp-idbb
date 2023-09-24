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
#include <getopt.h>
#include <stdlib.h>
#include <string.h>

static void usage(void) {
  fprintf(stdout, "usage: main-solve -h\n");
  fprintf(stdout, "usage: main-solve"
                  " --input/-i input_file"
                  " --time_limit/-t time_limit\n");
  fprintf(stdout, "\t--input/-i: input file\n");
  fprintf(stdout, "\t--time_limit/-t: time limit in seconds\n");
  fprintf(stdout, "input format:\n");
  fprintf(stdout, "\tline 0: n_stacks n_tiers n_blocks\n");
  fprintf(stdout, "\tline 1: h1 p[1][1] ... p[1][h1]\n");
  fprintf(stdout, "\tline 2: h2 p[2][1] ... p[2][h2]\n");
  fprintf(stdout, "\t...\n");
  fprintf(stdout, "\tline S: hS p[S][1] ... p[S][hS]\n");
  fflush(stdout);
}

int main(int argc, char **argv) {
  char *opts = "hi:t:";
  struct option options[] = {{"help", no_argument, NULL, 'h'},
                             {"input", required_argument, NULL, 'i'},
                             {"time_limit", required_argument, NULL, 't'},
                             {NULL, 0, NULL, 0}};

  char *input = "data/test.txt";
  int time_limit = 1800;

  for (int opt; (opt = getopt_long(argc, argv, opts, options, NULL)) != -1;) {
    switch (opt) {
    case 'h':
      usage();
      return EXIT_SUCCESS;
    case 'i':
      input = optarg;
      break;
    case 't':
      time_limit = (int)strtol(optarg, NULL, 10);
      break;
    default:
      fprintf(stderr, "Unknown option: %c\n", opt);
      return EXIT_FAILURE;
    }
  }

  fprintf(stdout,
          "Parameters:\n"
          "\tinput = %s\n"
          "\ttime_limit = %d\n",
          input, time_limit);
  fflush(stdout);

  instance_t *inst = read_instance(input);
  if (inst == NULL) {
    fprintf(stderr, "Failed to read instance from: %s\n", input);
    return EXIT_FAILURE;
  }

  print_instance(stdout, inst);
  fflush(stdout);

  report_t *report = solve(inst, time_limit);

  print_moves(stdout, report->best_sol, report->best_ub);
  fflush(stdout);

  free_instance(inst);
  free_report(report);

  return EXIT_SUCCESS;
}
