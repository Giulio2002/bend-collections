#include "../../benchmarks/native/common.h"
#include <assert.h>
static size_t allocations, releases;
static void *test_alloc(size_t n){void*p=malloc(n);if(p)allocations++;return p;}
static void test_free(void*p){if(p)releases++;free(p);}
#define malloc test_alloc
#define free test_free
#include "../../benchmarks/native/two_list.h"
#undef malloc
#undef free
static void verify(St*s,uint32_t*values,size_t n){
  assert(s->len==n && s->nf+s->nb==n);
  size_t nf=0,nb=0;
  for(Cell*p=s->front;p;p=p->next){assert(nf<n);assert(p->value==values[nf++]);}
  for(Cell*p=s->back;p;p=p->next){assert(nb<n);assert(p->value==values[n-1-nb++]);}
  assert(nf==s->nf && nb==s->nb && allocations-releases==n);
  Cell*out=dq_values(s);size_t i=0;
  for(Cell*p=out;p;p=p->next){assert(i<n);assert(p->value==values[i++]);}
  assert(i==n);cells_free(out);assert(allocations-releases==n);
}
int main(void){
  St s;dq_init(&s,0);uint32_t values[257],rng=123;size_t n=0;
  verify(&s,values,n);
  for(size_t step=0;step<100000;step++){
    rng=lcg(rng);unsigned op=(rng>>16)%6;
#ifdef TWO_LIST_FIFO
    int front=1;
#else
    int front=op&1;
#endif
    if(!n || (n<256 && op<2)){
#ifdef TWO_LIST_FIFO
      int at_front=0;
#else
      int at_front=front;
#endif
      dq_push(&s,rng,at_front);
      if(at_front){memmove(values+1,values,n*sizeof(*values));values[0]=rng;}
      else values[n]=rng;
      n++;
    }else if(op<4 || n==256){
      uint32_t expected=front?values[0]:values[n-1];assert(dq_pop(&s,front)==expected);
      if(front)memmove(values,values+1,(n-1)*sizeof(*values));n--;
    }else assert(dq_peek(&s,front)==(front?values[0]:values[n-1]));
    verify(&s,values,n);
  }
  dq_destroy(&s);assert(allocations==releases);
  printf("PASS 100000 operations; allocations=%zu frees=%zu\n",allocations,releases);
}
