#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef uint64_t SNAKEVAL;

void printHelp(FILE *out, SNAKEVAL val);
extern uint64_t NUM_TAG_MASK;
extern uint64_t CLOSURE_TAG_MASK;
extern uint64_t TUPLE_TAG_MASK;
extern uint64_t CLOSURE_TAG;
extern uint64_t TUPLE_TAG;
extern uint64_t FWD_PTR_TAG;
extern uint64_t NIL;
extern uint64_t tupleCounter;
extern uint64_t *STACK_BOTTOM;
extern uint64_t *FROM_S;
extern uint64_t *FROM_E;
extern uint64_t *TO_S;
extern uint64_t *TO_E;

void naive_print_heap(uint64_t *heap, uint64_t *heap_end) {
  printf("In naive_print_heap from %p to %p\n", heap, heap_end);
  for (uint64_t i = 0; i < (uint64_t)(heap_end - heap); i += 1) {
    printf("  %ld/%p: %p (%ld)\n", i, (heap + i), (uint64_t *)(*(heap + i)),
           *(heap + i));
  }
}

// Implement the functions below
void smarter_print_space(uint64_t *start, uint64_t *end) {
  uint64_t *curr = start;
  while (curr < end) {
    printf("%p: ", curr);
    printHelp(stdout, *curr);
    printf("\n");
    curr++;
  }
}

void smarter_print_heap(uint64_t *from_start, uint64_t *from_end,
                        uint64_t *to_start, uint64_t *to_end) {
  printf("From space:\n");
  smarter_print_space(from_start, from_end);
  printf("To space:\n");
  smarter_print_space(to_start, to_end);
}

/*
  Copies a Garter value from the given address to the new heap,
  but only if the value is heap-allocated and needs copying.

  Arguments:
    garter_val_addr: the *address* of some Garter value, which contains a Garter
  value, i.e. a tagged word. It may or may not be a pointer to a heap-allocated
  value... heap_top: the location at which to begin copying, if any copying is
  needed

  Return value:
    The new top of the heap, at which to continue allocations

  Side effects:
    If the data needed to be copied, then this replaces the value at its old
  location with a forwarding pointer to its new location
 */
uint64_t *copy_if_needed(uint64_t *garter_val_addr, uint64_t *heap_top) {
  // printf("Heap top called with %p\n", heap_top);
  uint64_t garter_val = *garter_val_addr;
  //printf("Copy if needed: ");
  //printHelp(stdout, garter_val);
  //printf("\n");
  uint64_t *heap_addr;
  uint64_t len;
  if ((garter_val & TUPLE_TAG_MASK) == TUPLE_TAG && garter_val != NIL) {
    // printf("Found tuple, copying: \n");
    // printHelp(stdout, garter_val);
    // printf("\n");
    //   untag to get addr to heap thing
    heap_addr = (uint64_t *)(garter_val - TUPLE_TAG);
    if ((*heap_addr & TUPLE_TAG_MASK) == FWD_PTR_TAG) {
      // printf("Found forwarding pointer, updating\n");
      *garter_val_addr = *heap_addr - FWD_PTR_TAG + TUPLE_TAG;
      return heap_top;
    }
    // printf("Copying tuple: ");
    // printHelp(stdout, garter_val);
    // printf("\n");
    //  read length of tuple, including length word itself
    len = (*heap_addr / 2) + 1;
    // printf("Length is %ld\n", len);
    //    copy heap thing to to-space
    for (int i = 0; i < len; i++) {
      heap_top[i] = heap_addr[i];
    }
    // replace old heap thing in from-space with forwarding pointer to to-space
    // printf("Replacing old tuple with forwarding pointer\n");
    *heap_addr = (uint64_t)heap_top | FWD_PTR_TAG;
    // change original pointer to heap thing to point to new to-space location
    *garter_val_addr = (uint64_t)heap_top + TUPLE_TAG;
    // move heap_top pointer, pad if len is even (len plus tuple elements will
    // be odd)
    // printf("Adding %ld to heap top\n", (len + (len % 2)) * sizeof(uint64_t));
    // heap_top += (len + (len % 2)) * sizeof(uint64_t);
    heap_top += len;
    if (len % 2 == 0) {
      heap_top[0] = 0xEEEEE;
      heap_top += 1;
    }
    // printf("Returning new top: %p\n", heap_top);
  }
  if ((garter_val & CLOSURE_TAG_MASK) == CLOSURE_TAG) {
    heap_addr = (uint64_t *)(garter_val - CLOSURE_TAG);

    if ((*heap_addr & CLOSURE_TAG_MASK) == FWD_PTR_TAG) {
      // printf("Found forwarding pointer, updating\n");
      *garter_val_addr = (*heap_addr - FWD_PTR_TAG) + CLOSURE_TAG;
      return heap_top;
    }

    // printf("found a lambda at: %p", heap_addr);
    // printHelp(stdout, garter_val);
    // printf("\n");

    len = 3 + (heap_addr[2] / 2);
    for (int i = 0; i < len; i++) {
      heap_top[i] = heap_addr[i];
    }
    // printf("new closure");
    // printHelp(stdout, garter_val);
    // printf("\n");

    *heap_addr = (uint64_t)heap_top | FWD_PTR_TAG;
    // change original pointer to heap thing to point to new to-space location
    *garter_val_addr = (uint64_t)heap_top + CLOSURE_TAG;
    // move everything over
    // update top pointer
    heap_top += len;
    if (len % 2 == 0) {
      heap_top[0] = 0xEEEEE;
      heap_top += 1;
    }
    // printf("Returning new top: %p\n", heap_top);
  }
  return heap_top;
}

/*
  Implements Cheney's garbage collection algorithm.

  Arguments:
    bottom_frame: the base pointer of our_code_starts_here, i.e. the bottommost
  Garter frame top_frame: the base pointer of the topmost Garter stack frame
    top_stack: the current stack pointer of the topmost Garter stack frame
    from_start and from_end: bookend the from-space of memory that is being
  compacted to_start: the beginning of the to-space of memory

  Returns:
    The new location within to_start at which to allocate new data
 */
uint64_t *gc(uint64_t *bottom_frame, uint64_t *top_frame, uint64_t *top_stack,
             uint64_t *from_start, uint64_t *from_end, uint64_t *to_start) {
  // printf("Running garbage collection, to start is: %p\n", to_start);
  // smarter_print_heap(from_start, from_end, to_start, to_start);
  // printf("\n");

  uint64_t *old_top_frame = top_frame;
  uint64_t *old_to_start = to_start;
  do {
    for (uint64_t *cur_word = top_stack /* maybe need a +1 here? */;
         cur_word < top_frame; cur_word++) {
      to_start = copy_if_needed(cur_word, to_start);
    }
    /* Shift to next stack frame:
     * [top_frame] points to the saved RBP, which is the RBP of the next stack
     * frame, [top_frame + 8] is the return address, and [top_frame + 16] is
     * therefore the next frame's stack-top
     */
    top_stack = top_frame + 2;
    old_top_frame = top_frame;
    top_frame = (uint64_t *)(*top_frame);
  } while (old_top_frame < bottom_frame); // Use the old stack frame to decide
                                          // if there's more GC'ing to do

  //printf("finished looking through stack, to start is: %p\n", to_start);

  //printf("Copied stack, now copying heap\n");
  //  iterate over to-space and copy referenced items into to-space
  uint64_t *curr = old_to_start;
  while (curr < to_start) {
    // copy this word if needed
    to_start = copy_if_needed(curr, to_start);
    // move to next word
    curr++;
  }

  //printf("Completed garbage collection\n");
  //smarter_print_heap(from_start, from_end, old_to_start, to_start);
  //printf("\n");

  // after copying and GC'ing all the stack frames, return the new allocation
  // starting point
  return to_start;
}
