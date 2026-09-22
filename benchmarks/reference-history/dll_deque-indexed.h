/* Indexed doubly linked deque with reusable node slots.
 * Owns one geometrically grown allocation. Removed slots form a free list;
 * storage follows peak live occupancy, never cumulative operation count.
 * This is shared by the deque and its FIFO queue specialization.
 */
#ifndef DLL_DEQUE_H
#define DLL_DEQUE_H
#include "common.h"
#define NO_NODE UINT32_MAX
typedef struct { uint32_t value, prev, next; } DqNode;
typedef struct {
  uint32_t rng, chk, head, tail, len, cap, used, free_head;
  DqNode *nodes;
} St;
static void dq_die(void) { fputs("deque allocation failed\n",stderr); exit(2); }
static void dq_init(St *s, uint32_t seed) {
  *s=(St){.rng=seed,.head=NO_NODE,.tail=NO_NODE,.cap=1,.free_head=NO_NODE};
  s->nodes=malloc(sizeof(DqNode));
  if(!s->nodes) dq_die();
  s->nodes[0]=(DqNode){0,NO_NODE,NO_NODE};
}
static void dq_destroy(St *s) { free(s->nodes); s->nodes=NULL; }
static uint32_t dq_alloc(St *s) {
  if(s->free_head!=NO_NODE) {
    uint32_t id=s->free_head; s->free_head=s->nodes[id].next; return id;
  }
  if(s->used==s->cap) {
    if(s->cap>UINT32_MAX/2) dq_die();
    uint32_t cap=s->cap*2;
    DqNode *p=realloc(s->nodes,(size_t)cap*sizeof(*p));
    if(!p) dq_die();
    s->nodes=p; s->cap=cap;
  }
  return s->used++;
}
static void dq_push(St *s,uint32_t value,int front) {
  uint32_t id=dq_alloc(s),a=front?NO_NODE:s->tail,b=front?s->head:NO_NODE;
  s->nodes[id]=(DqNode){value,a,b};
  if(a!=NO_NODE)s->nodes[a].next=id; else s->head=id;
  if(b!=NO_NODE)s->nodes[b].prev=id; else s->tail=id;
  s->len++;
}
static uint32_t dq_pop(St *s,int front) {
  if(!s->len)return 9;
  uint32_t id=front?s->head:s->tail;
  DqNode n=s->nodes[id];
  if(n.prev!=NO_NODE)s->nodes[n.prev].next=n.next; else s->head=n.next;
  if(n.next!=NO_NODE)s->nodes[n.next].prev=n.prev; else s->tail=n.prev;
  s->nodes[id].next=s->free_head; s->free_head=id; s->len--;
  return n.value;
}
static inline void dq_pf(St*s){s->rng=lcg(s->rng);dq_push(s,s->rng,1);s->chk=mix(s->chk,1);}
static inline void dq_pb(St*s){s->rng=lcg(s->rng);dq_push(s,s->rng,0);s->chk=mix(s->chk,1);}
static inline void dq_popf(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,dq_pop(s,1));}
static inline void dq_popb(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,dq_pop(s,0));}
static inline void dq_peekf(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,s->len?s->nodes[s->head].value:9);}
static inline void dq_peekb(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,s->len?s->nodes[s->tail].value:9);}
static inline void dq_len(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,s->len);}
typedef struct Cell {uint32_t value;struct Cell*next;} Cell;
static inline void dq_to_list(St*s) {
  s->rng=lcg(s->rng);
  Cell *cells=s->len?malloc((size_t)s->len*sizeof(Cell)):NULL;
  if(s->len&&!cells)dq_die();
  uint32_t j=0;
  for(uint32_t id=s->head;id!=NO_NODE;id=s->nodes[id].next,j++)
    cells[j]=(Cell){s->nodes[id].value,j+1<s->len?&cells[j+1]:NULL};
  Cell *p=cells; keep(p);
  uint32_t n=0;for(;p;p=p->next)n++;
  s->chk=mix(s->chk,n);free(cells);
}
static inline void dq_new(St*s){s->rng=lcg(s->rng);St fresh;dq_init(&fresh,0);St*p=&fresh;keep(p);s->chk=mix(s->chk,p->len);dq_destroy(p);}
static inline void dq_null(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,s->rng);}
static void dq_settle(St*s){for(uint32_t id=s->head;id!=NO_NODE;id=s->nodes[id].next)s->chk=mix(s->chk,s->nodes[id].value);}
#endif
