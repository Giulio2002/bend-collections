/* C BLAKE2b-512 driver over the official portable reference (benchmarks/native/blake/blake2b-ref.c,
   CC0), the reference for benchmarks/bend/blake2b.bend. Build:
   cc -O3 -march=native -Ibenchmarks/native/blake benchmarks/native/blake2b.c benchmarks/native/blake/blake2b-ref.c */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "blake2.h"
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;}
int main(void){
  size_t n=strtoull(getenv("BLAKE_SIZE"),0,10),depth=strtoull(getenv("BLAKE_DEPTH"),0,10),count=strtoull(getenv("BLAKE_COUNT"),0,10);
  size_t cap=((size_t)1<<depth)*4;
  unsigned char *data=malloc(cap),*copy=malloc(cap);
  for(size_t i=0;i<cap/4;i++){uint32_t w=(uint32_t)i*2654435761u+42;for(int j=0;j<4;j++)data[i*4+j]=w>>(j*8);}
  unsigned char out[BLAKE2B_OUTBYTES];uint32_t sum=0;
  double start=now();
  for(size_t i=0;i<count;i++){
    memcpy(copy,data,cap);
    blake2b(out,BLAKE2B_OUTBYTES,copy,n,NULL,0);
    sum+=(uint32_t)out[0]|((uint32_t)out[1]<<8)|((uint32_t)out[2]<<16)|((uint32_t)out[3]<<24);
  }
  printf("BENCH_MS=%.6f\n%u\n",(now()-start)*1000,sum);
  for(int j=0;j<BLAKE2B_OUTBYTES;j++)printf("%02x",out[j]);
  printf("\n");free(copy);free(data);return 0;
}
