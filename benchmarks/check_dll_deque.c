#include "native/dll_deque.h"
#include <assert.h>
int main(void) {
  St s;dq_init(&s,0);uint32_t a[1024],n=0,r=7;
  for(unsigned k=0;k<200000;k++) {
    r=lcg(r);unsigned op=(r>>16)%4;
    if(n==1024)op=2+(op&1);
    if(op<2){
      if(op==0){memmove(a+1,a,n*sizeof(*a));a[0]=r;}
      else a[n]=r;
      dq_push(&s,r,op==0);n++;
    }else{
      uint32_t want=n?(op==2?a[0]:a[n-1]):9;
      assert(dq_pop(&s,op==2)==want);
      if(n){n--;if(op==2)memmove(a,a+1,n*sizeof(*a));}
    }
    assert(s.len==n);
    uint32_t j=0,prev=NO_NODE;
    for(uint32_t id=s.head;id!=NO_NODE;id=s.nodes[id].next){
      assert(j<n&&s.nodes[id].value==a[j++]);assert(s.nodes[id].prev==prev);prev=id;
    }
    assert(j==n&&prev==s.tail);
  }
  dq_destroy(&s);dq_init(&s,0);
  const uint32_t occupancy=262144,steps=10000000;
  for(uint32_t i=0;i<occupancy;i++)dq_push(&s,i,0);
  for(uint32_t i=0;i<steps;i++){
    dq_push(&s,occupancy+i,0);assert(dq_pop(&s,1)==i);
    assert(s.len==occupancy&&s.used<=occupancy+1&&s.cap<=2*occupancy);
  }
  printf("PASS: 200000 differential operations; 10000000 constant-occupancy FIFO pairs; live=%u used=%u cap=%u storage_bytes=%zu\n",s.len,s.used,s.cap,(size_t)s.cap*sizeof(DqNode));
  dq_destroy(&s);
}
