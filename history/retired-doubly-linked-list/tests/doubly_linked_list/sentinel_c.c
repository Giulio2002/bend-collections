#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static size_t allocations, releases;
static void *count_malloc(size_t bytes) {
  void *p = malloc(bytes);
  if (p) allocations++;
  return p;
}
static void count_free(void *p) {
  if (p) releases++;
  free(p);
}
#define malloc count_malloc
#define free count_free
#include "../../benchmarks/native/sentinel_list.h"
#undef malloc
#undef free

static void check(SentinelList *list, const uint32_t *values, size_t count) {
  assert(list->length == count);
  assert(allocations - releases == count);
  ListNode *node = list->sentinel.next, *prev = &list->sentinel;
  for (size_t i = 0; i < count; i++) {
    assert(node != &list->sentinel);
    assert(node->prev == prev && prev->next == node);
    assert(node->value == values[i]);
    prev = node;
    node = node->next;
  }
  assert(node == &list->sentinel && node->prev == prev);
  node = list->sentinel.prev;
  for (size_t i = count; i; i--) {
    assert(node != &list->sentinel && node->value == values[i - 1]);
    assert(node->next->prev == node && node->prev->next == node);
    node = node->prev;
  }
  assert(node == &list->sentinel);
}

int main(void) {
  SentinelList list;
  uint32_t values[257], rng = 42;
  size_t count = 0;
  list_init(&list);
  check(&list, values, count);
  for (size_t step = 0; step < 100000; step++) {
    rng = rng * 1664525u + 1013904223u;
    int insert = !count || (count < 256 && ((rng >> 16) & 1));
    size_t index = (rng >> 1) % (count + (insert ? 1 : 0));
    ListNode *node = list.sentinel.next;
    for (size_t i = 0; i < index; i++) node = node->next;
    if (insert) {
      ListNode *added = list_insert_before(&list, node, rng);
      assert(added->value == rng && added->next == node);
      memmove(values + index + 1, values + index, (count-index)*sizeof(*values));
      values[index] = rng;
      count++;
    } else {
      size_t before = releases;
      assert(list_remove(&list, node) == values[index]);
      assert(releases == before + 1);
      memmove(values + index, values + index + 1, (count-index-1)*sizeof(*values));
      count--;
    }
    check(&list, values, count);
    if (step % 997 == 0) {
      list_clear(&list);
      count = 0;
      check(&list, values, count);
    }
  }
  list_clear(&list);
  check(&list, values, 0);
  assert(allocations == releases);
  printf("100000 operations passed; allocations=%zu frees=%zu\n", allocations, releases);
}
