/* Two-list queue/deque matching src/queue.bend and src/deque.bend.
 * FIFO reverses the entire back when front empties; deque splits the
 * opposite side in half. Each node is malloc'd and freed individually.
 */
#ifndef TWO_LIST_H
#define TWO_LIST_H
#include "common.h"
typedef struct Cell { uint32_t value; struct Cell *next; } Cell;
typedef struct {
  uint32_t rng, chk, len, nf, nb;
  Cell *front, *back;
} St;
static Cell *cell_new(uint32_t value, Cell *next) {
  Cell *p=malloc(sizeof(*p)); if(!p)abort();
  *p=(Cell){value,next}; return p;
}
static Cell *cells_reverse(Cell *xs) {
  Cell *out=NULL;
  while(xs){Cell *next=xs->next;xs->next=out;out=xs;xs=next;}
  return out;
}
static void cells_free(Cell *xs) {
  while(xs){Cell *next=xs->next;free(xs);xs=next;}
}
static void dq_init(St *s,uint32_t seed){*s=(St){.rng=seed};}
static void dq_destroy(St *s){cells_free(s->front);cells_free(s->back);s->front=s->back=NULL;s->len=s->nf=s->nb=0;}
static void dq_push(St *s,uint32_t value,int front) {
  if(s->len==UINT32_MAX)abort();
  if(front){s->front=cell_new(value,s->front);s->nf++;}
  else{s->back=cell_new(value,s->back);s->nb++;}
  s->len++;
}
static void dq_ready(St *s,int front) {
  Cell **to=front?&s->front:&s->back, **from=front?&s->back:&s->front;
  uint32_t *nt=front?&s->nf:&s->nb, *nf=front?&s->nb:&s->nf;
  if(*to)return;
#ifdef TWO_LIST_FIFO
  uint32_t keep=0;
#else
  uint32_t keep=*nf/2;
#endif
  Cell **cut=from;
  for(uint32_t i=0;i<keep;i++)cut=&(*cut)->next;
  Cell *moved=*cut;*cut=NULL;
  *to=cells_reverse(moved);*nt=*nf-keep;*nf=keep;
}
static uint32_t dq_pop(St *s,int front) {
  dq_ready(s,front);
  Cell **end=front?&s->front:&s->back;
  uint32_t *n=front?&s->nf:&s->nb;
  if(!*end)return 9;
  Cell *p=*end;uint32_t value=p->value;
  *end=p->next;free(p);(*n)--;s->len--;return value;
}
static uint32_t dq_peek(St *s,int front) {
  dq_ready(s,front);Cell *p=front?s->front:s->back;return p?p->value:9;
}
/* Materialize front ++ reverse(back), preserving the source. */
static Cell *dq_values(St *s) {
  Cell *out=NULL,*tail=NULL;
  for(Cell *p=s->front;p;p=p->next){Cell *n=cell_new(p->value,NULL);if(tail)tail->next=n;else out=n;tail=n;}
  Cell *back=NULL;
  for(Cell *p=s->back;p;p=p->next)back=cell_new(p->value,back);
  if(tail)tail->next=back;else out=back;
  return out;
}
static inline void dq_pf(St*s){s->rng=lcg(s->rng);dq_push(s,s->rng,1);s->chk=mix(s->chk,1);}
static inline void dq_pb(St*s){s->rng=lcg(s->rng);dq_push(s,s->rng,0);s->chk=mix(s->chk,1);}
static inline void dq_popf(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,dq_pop(s,1));}
static inline void dq_popb(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,dq_pop(s,0));}
static inline void dq_peekf(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,dq_peek(s,1));}
static inline void dq_peekb(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,dq_peek(s,0));}
static inline void dq_len(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,s->len);}
static inline void dq_to_list(St*s){s->rng=lcg(s->rng);Cell *xs=dq_values(s);Cell *p=xs;keep(p);uint32_t n=0;for(;p;p=p->next)n++;s->chk=mix(s->chk,n);cells_free(xs);}
static inline void dq_new(St*s){s->rng=lcg(s->rng);St fresh;dq_init(&fresh,0);St*p=&fresh;keep(p);s->chk=mix(s->chk,p->len);dq_destroy(p);}
static inline void dq_null(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,s->rng);}
static void dq_settle(St*s){Cell *xs=dq_values(s);for(Cell*p=xs;p;p=p->next)s->chk=mix(s->chk,p->value);cells_free(xs);}
#endif
