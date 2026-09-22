/* Native-list stack matching Bend's immutable, shareable List nodes.
 * The stack owns its top reference. Returned list snapshots retain the top;
 * popping a shared stack node never invalidates an outstanding snapshot.
 */
#ifndef BENCH_STACK_H
#define BENCH_STACK_H
#include "common.h"
typedef struct Cell {uint32_t value;size_t refs;struct Cell*next;} Cell;
typedef struct {uint32_t rng,chk,len;Cell*top;} St;
static Cell* retain(Cell*p){if(p){if(p->refs==SIZE_MAX)abort();p->refs++;}return p;}
static void release(Cell*p){while(p&&--p->refs==0){Cell*next=p->next;free(p);p=next;}}
static void st_init(St*s,uint32_t seed){*s=(St){.rng=seed};}
static void st_destroy(St*s){release(s->top);s->top=NULL;s->len=0;}
static void st_push(St*s,uint32_t value){if(s->len==UINT32_MAX)abort();Cell*p=malloc(sizeof(*p));if(!p)abort();*p=(Cell){value,1,s->top};s->top=p;s->len++;}
static uint32_t st_pop(St*s){Cell*p=s->top;if(!p)return 9;uint32_t v=p->value;s->top=retain(p->next);s->len--;release(p);return v;}
static inline void dq_pb(St*s){s->rng=lcg(s->rng);st_push(s,s->rng);s->chk=mix(s->chk,1);}
static inline void dq_popf(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,st_pop(s));}
static inline void dq_peekf(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,s->top?s->top->value:9);}
static inline void dq_len(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,s->len);}
static inline void dq_to_list(St*s){s->rng=lcg(s->rng);Cell*xs=retain(s->top);Cell*p=xs;keep(p);uint32_t n=0;for(;p;p=p->next)n++;s->chk=mix(s->chk,n);release(xs);}
static inline void dq_new(St*s){s->rng=lcg(s->rng);St fresh;st_init(&fresh,0);St*p=&fresh;keep(p);s->chk=mix(s->chk,p->len);st_destroy(p);}
static inline void dq_null(St*s){s->rng=lcg(s->rng);s->chk=mix(s->chk,s->rng);}
static void dq_settle(St*s){for(Cell*p=s->top;p;p=p->next)s->chk=mix(s->chk,p->value);}
#define dq_init st_init
#define dq_destroy st_destroy
#endif
