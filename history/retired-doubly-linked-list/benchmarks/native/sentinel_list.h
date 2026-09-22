/* Conventional circular doubly linked list. No arena, slot table or free list.
 * The embedded sentinel is stable: initialized lists must not be copied/moved.
 * A removed node pointer is invalid. Callers must not retain/use it afterwards.
 */
#ifndef SENTINEL_LIST_H
#define SENTINEL_LIST_H
#include <stdint.h>
#include <stdlib.h>

typedef struct ListNode {
  struct ListNode *prev, *next;
  uint32_t value;
} ListNode;

typedef struct {
  ListNode sentinel;
  size_t length;
} SentinelList;

static void list_init(SentinelList *list) {
  list->sentinel.prev = list->sentinel.next = &list->sentinel;
  list->sentinel.value = 0;
  list->length = 0;
}

/* right must belong to list (the sentinel is allowed). */
static ListNode *list_insert_before(SentinelList *list, ListNode *right,
                                    uint32_t value) {
  if (list->length == SIZE_MAX) abort();
  ListNode *node = malloc(sizeof(*node));
  if (!node) abort();
  node->value = value;
  node->prev = right->prev;
  node->next = right;
  right->prev->next = node;
  right->prev = node;
  list->length++;
  return node;
}

/* node must be a live, non-sentinel member of list. */
static uint32_t list_remove(SentinelList *list, ListNode *node) {
  uint32_t value = node->value;
  node->prev->next = node->next;
  node->next->prev = node->prev;
  list->length--;
  free(node);
  return value;
}

static void list_clear(SentinelList *list) {
  ListNode *node = list->sentinel.next;
  while (node != &list->sentinel) {
    ListNode *next = node->next;
    free(node);
    node = next;
  }
  list_init(list);
}
#endif
