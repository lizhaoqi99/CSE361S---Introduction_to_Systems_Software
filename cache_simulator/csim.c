/* Steve Li
 * wustl id: 464163
 * wustl key: zhaoqi.li
 * 
 * csim.c - A cache simulator that takes a valgrind memory trace as input,
 *          simulates the hit/miss behavior of a cache memory on this trace, and 
 *          outputs the total number of hits, misses, evictions, dirty bytes evicted, 
 *          dirty bytes active in the cache, and back-to-back references to the
 *          same address within a given set. Assume the replacement policy to 
 *          be LRU (least-recently-used).
 *
 */

#include "cachelab.h"

#include <stdio.h>
#include <limits.h>
#include <getopt.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h> 

int verbose_flag; 
int s, E, b, S;  // S = number of sets, s = number of bits for set index in the address (S=2^s), E = number of cache lines per set, b = number of block bits (B=2^b)
int hits_count, miss_count, eviction_count, dirty_eviction_bytes_count, dirty_active_bytes_count, double_ref_count; // summary statistics

char trace_fn[1000];    // the trace file name
char buf[1000];     // a buffer for input
typedef struct {
    int valid_bit, dirty_bit, tag, stamp;
}cache_line;

cache_line **cache = NULL;      // cache -> cache_sets -> cache_lines

/* 
 * update - update data at memory address "address".
 *   If it is already in cache, increast hits_count
 *   If it is not in cache, load it into cache, increase miss_count
 *   if it is evicted, also increase eviction_count
 */
void update(unsigned long long int address, int is_write)
{
    int max_stamp = INT_MIN, max_stamp_id = -1, min_stamp = INT_MAX, min_stamp_id = -1, is_double_ref = 0;
    int  address_tag, address_set_index; // the tag and set index of address
    address_set_index = (address << (64-s-b)) >> (64-s);
    address_tag = address >> (s + b);

    // Hit:
    //      check whether there is a hit
    for(int i = 0; i < E; i++) {
        if(cache[address_set_index][i].tag == address_tag) { // a hit
            if(is_write) {
                if(cache[address_set_index][i].dirty_bit == 0) {
                    cache[address_set_index][i].dirty_bit = 1;
                    dirty_active_bytes_count += (1 << b);
                }                       
            }
            
            for(int j = 0; j < E; j++) {
                if(cache[address_set_index][j].stamp < min_stamp && cache[address_set_index][j].stamp != -1) {   // see if it's double ref
                    min_stamp = cache[address_set_index][j].stamp;
                    min_stamp_id = j;
                }
            }
            
            if(i == min_stamp_id) {
                is_double_ref = 1;
                double_ref_count++;
            }

            if(verbose_flag) {
                if(is_double_ref) {
                    printf("hit-double_ref\n");
                } else {
                    printf("hit\n");
                }
            }
            cache[address_set_index][i].stamp = 0; // reset the timestamp 
            hits_count++;
            return ;        // return immediately
        }
    }

    // Miss: 
    //      check whether there is an empty line to copy the data at address
    for(int i = 0; i < E; i++) {
        if(cache[address_set_index][i].valid_bit == 0) {
            if(verbose_flag) {
                if (is_write) {
                    printf("dirty-miss\n");
                } else {
                    printf("miss\n");
                }
            }

            if(is_write) {
                cache[address_set_index][i].dirty_bit = 1;
                dirty_active_bytes_count += (1 << b);
            }
            cache[address_set_index][i].valid_bit = 1;
            cache[address_set_index][i].tag = address_tag;
            cache[address_set_index][i].stamp = 0;
            miss_count++;    // cold miss
            return;         // return immediately
        }
    }
    
    // Eviction:
    //      if there is not any empty line, then an eviction will occur
    eviction_count++;
    miss_count++;

    if(verbose_flag) {
        if (is_write) {
            printf("dirty-miss ");
        } else {
            printf("miss ");
        }
    }


    for(int i = 0; i < E; i++) {
        if(cache[address_set_index][i].stamp > max_stamp && cache[address_set_index][i].stamp != -1) {   // look for the largest stamp (LRU cache line)
            max_stamp = cache[address_set_index][i].stamp;
            max_stamp_id = i;
        }
    }
 
    if(cache[address_set_index][max_stamp_id].dirty_bit == 1) { // if it's previously dirty
        if(verbose_flag) printf("dirty_eviction\n");
        if(!is_write) {
            cache[address_set_index][max_stamp_id].dirty_bit = 0; 
            dirty_eviction_bytes_count += (1 << b);
            dirty_active_bytes_count -= (1 << b);
        } else {   // keep the dirty_bit 1 and dirty_active_bytes_count stays the same
            dirty_eviction_bytes_count += (1 << b);
        }
    } else {    // if it's previously not dirty
        if(verbose_flag) printf("eviction\n");
        if(is_write) {    
            cache[address_set_index][max_stamp_id].dirty_bit = 1; 
            dirty_active_bytes_count += (1 << b);
        }
    }
    cache[address_set_index][max_stamp_id].tag = address_tag;
    cache[address_set_index][max_stamp_id].stamp = 0;
    return;
}

/*
 * update_timestamp - update the timestamp of each cache line 
 */
void update_timestamp(void) 
{
    for(int i = 0; i < S; i++)
        for(int j = 0; j < E; j++)
            if(cache[i][j].valid_bit == 1) // only update valid cache lines 
                cache[i][j].stamp++;
}

/*
 * printUsage - print usage info
 */
void printUsage(char* argv[])
{
    printf("Usage: %s [-hv] -s <s> -E <E> -b <b> -t <tracefile>\n", argv[0]);
    printf("Options:\n");
    printf("  -h       Optional help flag that prints usage info.\n");
    printf("  -v       Optional verbose flag that displays trace info.\n");
    printf("  -s <s>   Number of set index bits (S = 2^s is the number of sets).\n");
    printf("  -E <E>   Associativity (number of lines per set).\n");
    printf("  -b <b>   Number of block bits (B = 2^b is the block size).\n");
    printf("  -t <tracefile>  Name of the valgrind trace to replay.\n");
    printf("\nExample:\n");
    printf("  linux> %s -s 4 -E 1 -b 4 -t traces/yi.trace\n", argv[0]);
}

/*
 * main
 */
int main(int argc, char* argv[])
{
    char opt; // command line argument
    int byte_len; 
    char type; // type of a single trace record
    unsigned long long int address;//address of memory
    hits_count = miss_count = eviction_count = dirty_eviction_bytes_count = dirty_active_bytes_count = double_ref_count = 0;//initialization
    while((opt = (getopt(argc, argv, "hvs:E:b:t:"))) != -1)
    {
        switch(opt)
        {
            case 'h':
                     printUsage(argv);
                     exit(0);
                     break;
            case 'v':
                     verbose_flag = 1;
                     break;
            case 's':
                     s = atoi(optarg);
                     break;
            case 'E':
                     E = atoi(optarg);
                     break;
            case 'b':
                     b = atoi(optarg);
                     break;
            case 't':
                     strcpy(trace_fn, optarg);
                     break;
            default:
                     printUsage(argv);
                     exit(1);
        }
    }
    
    FILE* fp = fopen(trace_fn,"r");
    if(fp == NULL) {
        fprintf(stderr,"The File is wrong!\n");
        exit(-1);
    }

    S = (1 << s); // S equals to 2^s
    cache = (cache_line**) calloc(S, sizeof(cache_line*));
    for(int i = 0; i < S; i++) {
        cache[i] = (cache_line*) calloc(E, sizeof(cache_line)); // calloc each row of cache
    }

    for(int i = 0; i < S; i++) {
        for(int j = 0; j < E; j++) {
            cache[i][j].valid_bit = cache[i][j].dirty_bit = 0;
            cache[i][j].tag = -1;
            cache[i][j].stamp = -1;
        } // cache lines initialization
    }

    while(fgets(buf,1000,fp)) // get a whole line
    {
        sscanf(buf," %c %llx,%d", &type, &address, &byte_len); // llx -> long long int hexdecimal
        if (verbose_flag) {     // verbose mode
            printf("%c %llx,%d ", type, address, byte_len);
        }
        switch(type)
        {
            case 'I':
                     break;
            case 'L':
                     update(address, 0);
                     break;
            case 'M':   // data modify: a load first, then save 
                     update(address, 0);
                     update(address, 1);
                     break;
            case 'S':
                     update(address, 1);                        
                     break;
            default:
                     break;
        }
        update_timestamp();     // update the timestamp of each cache line after each operation
    }

    for(int i = 0; i < S; i++) {
        free(cache[i]); // free allocated memory
    }
    free(cache);
    
    fclose(fp);
    printSummary(hits_count, miss_count, eviction_count, dirty_eviction_bytes_count, dirty_active_bytes_count, double_ref_count);
    return 0;
}
