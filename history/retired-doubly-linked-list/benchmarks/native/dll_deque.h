/* Conventional node-per-allocation sentinel DLL shared by deque and queue.
 * Removal calls free immediately; no retained pool or generation scheme.
 */
#ifndef DLL_DEQUE_H
#define DLL_DEQUE_H
#include "common.h"
#include "sentinel_list.h"
typedef struct {
  uint32_t rng, chk;
  SentinelList list;
} St;
static void dq_die(void) { fputs("deque allocation failed\n",stderr); exit(2); }
static void dq_init(St *s, uint32_t seed) {
  s->rng=seed; s->chk=0; list_init(&s->list);
}
static void dq_destroy(St *s) { list_clear(&s->list); }
static void dq_push(St *s,uint32_t value,int front) {
  list_insert_before(&s->list,front?s->list.sentinel.next:&s->list.sentinel,value);
}
static uint32_t dq_pop(St *s,int front) {
  if(!s->list.length)return 9;
  return list_remove(&s->list,front?s->list.sentinel.next:s->list.sentinel.prev);
}
static inline void dq_pf(St*s){s->rng=lcg(s->rng);dq_push(s,s->rng,1);s->chk=mix(s->chk,1);}
static inline void dq_pb(St*s){s->rng=lcg(s->rng);dq_push(s,s->rng,0);s->chk=mix(s->chk,1);}
static inline void dq_popf(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,dq_pop(s,1));}
static inline void dq_popb(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,dq_pop(s,0));}
static inline void dq_peekf(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,s->list.length?s->list.sentinel.next->value:9);}
static inline void dq_peekb(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,s->list.length?s->list.sentinel.prev->value:9);}
static inline void dq_len(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,s->list.length);}
typedef struct Cell {uint32_t value;struct Cell*next;} Cell;
static inline void dq_to_list(St*s) {
  s->rng=lcg(s->rng);
  Cell *cells=s->list.length?malloc((size_t)s->list.length*sizeof(Cell)):NULL;
  if(s->list.length&&!cells)dq_die();
  uint32_t j=0;
  for(ListNode *node=s->list.sentinel.next;node!=&s->list.sentinel;node=node->next,j++)
    cells[j]=(Cell){node->value,j+1<s->list.length?&cells[j+1]:NULL};
  Cell *p=cells; keep(p);
  uint32_t n=0;for(;p;p=p->next)n++;
  s->chk=mix(s->chk,n);free(cells);
}
static inline void dq_new(St*s){s->rng=lcg(s->rng);St fresh;dq_init(&fresh,0);St*p=&fresh;keep(p);s->chk=mix(s->chk,p->list.length);dq_destroy(p);}
static inline void dq_null(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,s->rng);}
static void dq_settle(St*s){for(ListNode *node=s->list.sentinel.next;node!=&s->list.sentinel;node=node->next)s->chk=mix(s->chk,node->value);}
#endif
