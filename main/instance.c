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

#include "instance.h"
#include <stdlib.h>
#include <string.h>

instance_t *malloc_instance(int n_stacks, int n_tiers) {
  instance_t *inst = malloc(sizeof(instance_t));
  inst->n_stacks = n_stacks;
  inst->n_tiers = n_tiers;
  inst->h = malloc(sizeof(int) * n_stacks);
  inst->p = malloc(sizeof(int *) * n_stacks);
  inst->p[0] = malloc(sizeof(int) * n_stacks * (n_tiers + 1));
  for (int s = 1; s < n_stacks; s++) {
    inst->p[s] = inst->p[0] + s * (n_tiers + 1);
  }
  return inst;
}

void free_instance(instance_t *inst) {
  free(inst->h);
  free(inst->p[0]);
  free(inst->p);
  free(inst);
}

static char *parse_int(char *iter, int *num) {
  char *next;
  *num = (int)strtol(iter, &next, 10);
  return iter == next ? NULL : next;
}

instance_t *read_instance(char *input) {
  FILE *fp = fopen(input, "r");
  if (fp == NULL) {
    fprintf(stderr, "Failed to open file: %s\n", input);
    return NULL;
  }

  char buf[BUFSIZ];
  int line = 0;
  char *iter;

  do {
    line++;
    iter = fgets(buf, BUFSIZ, fp) + strspn(buf, " \t");
  } while (*iter == '#' || *iter == '\0');

  int n_stacks;
  iter = parse_int(iter, &n_stacks);
  if (iter == NULL) {
    fprintf(stderr, "Failed to read n_stacks in line %d: %s\n", line, buf);
    fclose(fp);
    return NULL;
  }
  int n_tiers;
  iter = parse_int(iter, &n_tiers);
  if (iter == NULL) {
    fprintf(stderr, "Failed to read n_tiers in line %d: %s\n", line, buf);
    fclose(fp);
    return NULL;
  }
  int n_blocks;
  iter = parse_int(iter, &n_blocks);
  if (iter == NULL) {
    fprintf(stderr, "Failed to read n_blocks in line %d: %s\n", line, buf);
    fclose(fp);
    return NULL;
  }

  instance_t *inst = malloc_instance(n_stacks, n_tiers);
  inst->n_blocks = n_blocks;
  inst->max_prio = 0;

  for (int s = 0; s < n_stacks; s++) {
    do {
      line++;
      iter = fgets(buf, BUFSIZ, fp) + strspn(buf, " \t");
    } while (*iter == '#' || *iter == '\0');

    iter = parse_int(iter, &inst->h[s]);
    if (iter == NULL) {
      fprintf(stderr, "Failed to read h[%d] in line %d: %s\n", s + 1, line,
              buf);
      fclose(fp);
      free_instance(inst);
      return NULL;
    }

    for (int t = 1; t <= inst->h[s]; t++) {
      iter = parse_int(iter, &inst->p[s][t]);
      if (iter == NULL) {
        fprintf(stderr, "Failed to read p[%d][%d] in line %d: %s\n", s + 1, t,
                line, buf);
        fclose(fp);
        free_instance(inst);
        return NULL;
      }

      if (inst->max_prio < inst->p[s][t]) {
        inst->max_prio = inst->p[s][t];
      }
    }
  }

  fclose(fp);

  return inst;
}

void print_instance(FILE *fp, instance_t *inst) {
  for (int t = inst->n_tiers; t >= 1; t--) {
    for (int s = 0; s < inst->n_stacks; s++) {
      if (inst->h[s] < t) {
        fprintf(fp, "[   ]");
      } else {
        fprintf(fp, "[%3d]", inst->p[s][t]);
      }
    }
    fprintf(fp, "\n");
  }

  for (int s = 0; s < inst->n_stacks; s++) {
    fprintf(fp, "-----");
  }
  fprintf(fp, "\n");

  for (int s = 0; s < inst->n_stacks; s++) {
    fprintf(fp, " %3d ", s);
  }
  fprintf(fp, "\n");
}
