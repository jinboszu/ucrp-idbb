#ifndef STATE_H
#define STATE_H

#include "instance.h"
#include <stdbool.h>

enum { NEVER, MOVE_OUT, MOVE_IN, RETRIEVE };

typedef struct {
  int n_stacks;  // number of stacks, indexed from 0 to n_stacks - 1
  int n_tiers;   // number of tiers, indexed from 1 to n_tiers (0 is ground)
  bool has_head; // true if including head arrays
  bool has_body; // true if including body matrices
  bool tracked;  // true if including tracking information

  int n_blocks;          // number of blocks
  int n_bad;             // number of badly-placed blocks
  int *h;                // h[s]: height of stack s
  int *list;             // list[i]: i-th stack in the ordered list
  int *rank;             // rank[s]: rank of stack s
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
 * @param n_stacks number of stacks
 * @param n_tiers number of tiers
 * @param has_head true if including head arrays
 * @param has_body true if including body matrices
 * @param tracked true if including tracking information
 * @return created state
 */
state_t *malloc_state(int n_stacks, int n_tiers, bool has_head, bool has_body,
                      bool tracked);

/**
 * Free the space of a state
 * @param state the state
 */
void free_state(state_t *state);

/**
 * Copy head arrays
 * @param dst_state destination state
 * @param src_state source state
 */
void copy_state_head(state_t *dst_state, state_t *src_state);

/**
 * Copy body matrices
 * @param dst_state destination state
 * @param src_state source state
 */
void copy_state_body(state_t *dst_state, state_t *src_state);

/**
 * Copy all values
 * @param dst_state destination state
 * @param src_state source state
 */
void copy_state(state_t *dst_state, state_t *src_state);

/**
 * Reuse head arrays
 * @param dst_state destination state
 * @param src_state source state
 */
void reuse_state_head(state_t *dst_state, state_t *src_state);

/**
 * Reuse body matrices
 * @param dst_state destination state
 * @param src_state source state
 */
void reuse_state_body(state_t *dst_state, state_t *src_state);

/**
 * @param state the state
 * @return true if the target block is retrievable
 */
bool is_retrievable(state_t *state);

/**
 * @param state the state
 * @return true if at least one empty stack exists
 */
bool has_empty_stack(state_t *state);

/**
 * Update matrix information for a slot
 * @param state the state
 * @param s stack
 * @param t tier
 * @param p priority
 * @param l time
 */
void update_slot(state_t *state, int s, int t, int p, int l);

/**
 * Initialize a state from an instance
 * @param state the state
 * @param inst the instance
 */
void init_state(state_t *state, instance_t *inst);

/**
 * Move a block out of a stack
 * @param state the state
 * @param s source stack
 * @param l time of this relocation
 */
void move_out(state_t *state, int s, int l);

/**
 * Move a block into a stack
 * @param state the state
 * @param d destination stack
 * @param p priority value
 * @param l time of this relocation
 */
void move_in(state_t *state, int d, int p, int l);

/**
 * Relocate the topmost block of a stack to another stack
 * @param state the state
 * @param s source stack
 * @param d destination stack
 * @param l time of this relocation
 */
void relocate(state_t *state, int s, int d, int l);

/**
 * Retrieve the target block from the top of stack list[0]
 * @param state the state
 * @param l time of this retrieval
 */
void retrieve(state_t *state, int l);

#endif
