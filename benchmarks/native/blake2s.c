/* BLAKE2s-256 with the official portable C reference (benchmarks/native/blake/blake2s-ref.c,
   CC0), the reference for benchmarks/bend/blake2s.bend. Same protocol as keccak256.c:
   env BLAKE_SIZE, BLAKE_DEPTH, BLAKE_COUNT; the input is 2^DEPTH words w[i] = i*2654435761+42
   (little-endian bytes); each hash runs on a fresh copy; prints BENCH_MS=<ms>, the U32 sum of
   the first little-endian digest word over all hashes, and the last digest in hex. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "blake2.h"
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;}
int main(void){size_t n=strtoull(getenv("BLAKE_SIZE"),0,10),depth=strtoull(getenv("BLAKE_DEPTH"),0,10),count=strtoull(getenv("BLAKE_COUNT"),0,10);size_t cap=((size_t)1<<depth)*4;if(n>cap){printf("BENCH_MS=0\n0\ninvalid\n");return 0;}unsigned char *data=malloc(cap),*copy=malloc(cap);for(size_t i=0;i<cap/4;i++){uint32_t w=(uint32_t)i*2654435761u+42;for(int j=0;j<4;j++)data[i*4+j]=w>>(j*8);}unsigned char out[32];uint32_t sum=0;double start=now();for(size_t i=0;i<count;i++){memcpy(copy,data,cap);blake2s(out,32,copy,n,NULL,0);sum+=(uint32_t)out[0]|((uint32_t)out[1]<<8)|((uint32_t)out[2]<<16)|((uint32_t)out[3]<<24);}printf("BENCH_MS=%.6f\n%u\n",(now()-start)*1000,sum);for(int j=0;j<32;j++)printf("%02x",out[j]);printf("\n");free(copy);free(data);return 0;}
