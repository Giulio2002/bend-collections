/* XKCP-based C Keccak-256 (vendored XKCP plain-64bits opt64 permutation, benchmarks/native/xkcp/), the reference for benchmarks/bend/keccak256.bend. From bend-keccak. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "KeccakP-1600-SnP.h"
static void hash(const unsigned char *p,size_t n,unsigned char out[32]) {
 KeccakP1600_state s;KeccakP1600_Initialize(&s);
 while(n>=136){KeccakP1600_AddBytes(&s,p,0,136);KeccakP1600_Permute_24rounds(&s);p+=136;n-=136;}
 KeccakP1600_AddBytes(&s,p,0,(unsigned int)n);KeccakP1600_AddByte(&s,1,(unsigned int)n);KeccakP1600_AddByte(&s,128,135);KeccakP1600_Permute_24rounds(&s);KeccakP1600_ExtractBytes(&s,out,0,32);
}
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;}
int main(void){size_t n=strtoull(getenv("KECCAK_SIZE"),0,10),depth=strtoull(getenv("KECCAK_DEPTH"),0,10),count=strtoull(getenv("KECCAK_COUNT"),0,10);size_t cap=((size_t)1<<depth)*4;unsigned char *data=malloc(cap),*copy=malloc(cap);for(size_t i=0;i<cap/4;i++){uint32_t w=(uint32_t)i*2654435761u+42;for(int j=0;j<4;j++)data[i*4+j]=w>>(j*8);}unsigned char out[32];uint32_t sum=0;double start=now();for(size_t i=0;i<count;i++){memcpy(copy,data,cap);hash(copy,n,out);sum+=(uint32_t)out[0]|((uint32_t)out[1]<<8)|((uint32_t)out[2]<<16)|((uint32_t)out[3]<<24);}printf("BENCH_MS=%.6f\n%u\n",(now()-start)*1000,sum);for(int j=0;j<32;j++)printf("%02x",out[j]);printf("\n");free(copy);free(data);return 0;}
