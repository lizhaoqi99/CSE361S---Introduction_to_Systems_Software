/*
 ******************************************************************************
 *                               mm.c                                         *
 *           64-bit struct-based implicit free list memory allocator          *
 *                      without coalesce functionality                        *
 *                 CSE 361: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *                        Final implementation:                               *
 *  		   Segregated list with LIFO policy                           *
 * 									      *														  
 *     The segregated list is divided into 10 classes that each stores        *
 *     free blocks with corresponding size greater than 16 bytes. Since       *
 *     the minimum block size is 16 bytes by my design, for blocks that       *
 *     are 16 bytes, I created a small segregated list that is designated     *
 *     to store those free blocks with the smallest size. 		      *
 * 									      *															  *
 * 	 Structures:                                                          *
 *  Allocated blocks:      Free blocks=16 bytes:     Free blocks>16 bytes:    *
 *   |  header |	    |  header |			|  header |	      *
 *   ----------- 	    -----------			-----------	      *
 *   |         |	   | next ptr |			| next ptr |          *
 *   | payload |					| prev ptr |          *
 *   |         |                                        |  footer |           *
 * 									      *									  
 * header contains:						              *
 *  	1. size of the current block					      *
 *	2. previous block size < 16 bytes flag				      *
 * 	3. previous block allocation flag				      *
 *  	4. current block allocation flag				      *
 * 									      *									  
 *    data contains:							      *
 * 		Free blocks:						      *							  
 * 			1. Blocks in small_seg_list (total size=16 bytes):    *
 *				next_free pointer (8 bytes)		      *
 * 			2. Blocks in seg_list (total size>16 bytes):          *
 *				next_free pointer (8 bytes)                   *
 * 				prev_free pointer (8 bytes)                   *
 * 		Allocated blocks:					      *							  
 * 			payload only					      *
 * 									      *
 *     (The small segregated list only supports 1-directional search while    *
 *     the segregated list supports bi-directional search.                    *
 *     To distinguish 16-byte blocks with other blocks in the heap, I used    *
 *     a prev_sseg bit in header.)					      *
 *     									      *
 *  ************************************************************************  *
 *  ** ADVICE FOR STUDENTS. **                                                *
 *  Step 0: Please read the writeup!                                          *
 *  Step 1: Write your heap checker. Write. Heap. checker.                    *
 *  Step 2: Place your contracts / debugging assert statements.               *
 *  Good luck, and have fun!                                                  *
 *                                                                            *
 ******************************************************************************
 */

/* Do not change the following! */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined, enable printing on dbg_printf and contracts.
 * Debugging macros, with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
//#define DEBUG // uncomment this line to enable debugging

#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disnabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif

/* Extra macros */
#define seg_list_size 11 // size of segregated list for block sizes > 16 bytes
#define nth_fit 25		 // implementing 25th fit

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);				 // word and header size (bytes)
static const size_t dsize = 2 * sizeof(word_t);			 // double word size (bytes)
static const size_t min_block_size = 2 * sizeof(word_t); // Minimum block size
static const size_t chunksize = (1 << 12);				 // requires (chunksize % 16 == 0), minimum heap size to expand by

static const word_t alloc_mask = 0x1;
static const word_t size_mask = ~(word_t)0xF;
static const word_t prev_alloc_mask = 0x2;
static const word_t prev_sseg_mask = 0x4;

typedef struct block block_t;

struct block
{
	/* Use the least sig 4 bits of header to store necessary 
	 * information since alignment=16 bytes
     *
	 * header contains:
	 *  size of the current block	
	 *	previous block size < 16 bytes flag
	 *  previous block allocation flag
	 *  current block allocation flag
	 */
	word_t header; // 8 bytes

	/*
     * We don't know how big the payload will be.  Declaring it as an
     * array of size 0 allows computing its starting address using
     * pointer notation.
     *
	 * data contains:
	 * Free blocks:
	 * 	1. Blocks in small_seg_list (total size=16 bytes):
	 *		next_free pointer (8 bytes)
	 * 	2. Blocks in seg_list (total size>16 bytes):
	 *		next_free pointer (8 bytes)
	 * 		prev_free pointer (8 bytes)
	 * Allocated blocks:
	 * 	payload only
	 */
	union {
		struct
		{ // 16 bytes
			block_t *next;
			block_t *prev;
		} pointers;
		char payload[0];
	} data;
	/*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
};

/* Global variables 8+11*8+8=104 bytes */
/* Pointer to first block */
static block_t *heap_start = NULL;
/* Pointer to the root of the segregated list for block sizes > 16 bytes */
static block_t *seg_list[seg_list_size];
/* Pointer to the root of the list for small sized blocks */
static block_t *small_seg_list = NULL;

bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

/* Extra helper functions */
static block_t *find_prev_free(block_t *block);
static block_t *find_next_free(block_t *block);
static void insert_freeblock(block_t *block);
static void remove_freeblock(block_t *block);
static size_t get_prev_alloc(block_t *block);
static size_t get_prev_sseg(block_t *block);
static int get_seg_list(size_t size);

void print_seg_list(void);
void print_small_seg_list(void);
void print_heap(void);


/*
 * print_seg_list: print out the entire seg_list including size class index 
 * 				   number and its corresponding elements with block address.
 */
void print_seg_list(void)
{
	dbg_printf("seg_list:\n");
	block_t *block;
	unsigned int count = 1;
	int index;
	for (index = 0; index < seg_list_size; index++)
	{
		dbg_printf("index %d:\n", index);
		count = 1;
		for (block = seg_list[index]; block != NULL; block = find_next_free(block))
		{
			dbg_printf("  block %u at %p \n", count, block);
			count += 1;
		}
	}

	dbg_printf(" \n");
}

/*
 * print_small_seg_list: print out the entire small_seg_list with block address.
 * 				   
 */
void print_small_seg_list(void)
{
	dbg_printf("small_seg_list:\n");
	block_t *block;
	unsigned int count = 1;
	for (block = small_seg_list; block != NULL; block = find_next_free(block))
	{
		dbg_printf("  block %u at %p \n", count, block);
		count += 1;
	}
	dbg_printf(" \n");
}

/*
 * print_heap: print out the entire heap with block address.
 * 				   
 */
void print_heap(void)
{
	dbg_printf("heap blocks:\n");
	block_t *block;
	unsigned int count;
	count = 0;
	dbg_printf("   --Heap start at %p-- \n", mem_heap_lo());
	for (block = heap_start; get_size(block) > 0; block = find_next(block))
	{
		dbg_printf("   Heap block %u at %p %s (size=%zu)  \n", count, block, get_alloc(block) ? "allocated" : "free", get_size(block));
		count += 1;
	}
	dbg_printf("   --Heap end at %p-- \n\n", mem_heap_hi());
}

/* 
 * get_seg_list: given the size needed to allocate, return which size class it 
 * 				 belongs to. One class for each larger size: [(2^i)+1, 2^(i+1)].
 */
static int get_seg_list(size_t size)
{
	if ((size > 16) && (size <= 32))
	{
		return 0;
	}
	else if ((size > 32) && (size <= 64))
	{
		return 1;
	}
	else if ((size > 64) && (size <= 128))
	{
		return 2;
	}
	else if ((size > 128) && (size <= 256))
	{
		return 3;
	}
	else if ((size > 256) && (size <= 512))
	{
		return 4;
	}
	else if ((size > 512) && (size <= 1024))
	{
		return 5;
	}
	else if ((size > 1024) && (size <= 2048))
	{
		return 6;
	}
	else if ((size > 2048) && (size <= 4098))
	{
		return 7;
	}
	else if ((size > 4098) && (size <= 8192))
	{
		return 8;
	}
	else if ((size > 8192) && (size <= 16384))
	{
		return 9;
	}
	else if (size > 16384)
	{
		return 10;
	}
	else
	{
		dbg_printf("\nSmall block encountered!\n");
		return -1;
	}
}

/*
 * mm_init: at the start of the program when the heap is originally empty, call
 * 			this function to perform any necessary initializations such as
 * 			allocating the initial heap area, and initializing seg_list and
 * 			small_seg_list. 
 * 			Returns -1 if there is a problem during initialization, and returns
 * 			0 otherwise.
 */
bool mm_init(void)
{
	dbg_printf("\n----------------------------------INIT------------------------------------\n");
	// Create the initial empty heap
	word_t *start = (word_t *)(mem_sbrk(2 * wsize));

	if (start == (void *)-1)
	{
		return false;
	}

	start[0] = pack(0, true);	 // Prologue footer
	start[1] = pack(0, true);	 // Epilogue header
	start[1] |= prev_alloc_mask; // set previous alloc bit

	// Heap starts with first "block header", currently the epilogue footer
	heap_start = (block_t *)&(start[1]);

	int ite;
	// initialize seg_list and small_seg_list
	small_seg_list = NULL;
	for (ite = 0; ite < seg_list_size; ite++)
	{
		seg_list[ite] = NULL;
	}

	// Extend the empty heap with a free block of chunksize bytes
	if ((extend_heap(chunksize)) == NULL)
	{
		return false;
	}

	dbg_printf("\n------------------------------FINISHED INIT----------------------------------\n");
	return true;
}

/*
 * malloc: given the size to allocate on the heap by the user, the malloc routine
 * 		   adjusts the given size to conform to the alignment policy of 16 bytes
 * 		   and the minimum block size of 16 bytes. Then malloc searches the
 * 		   appropriate list for a fit. If no fit is found, request more memory,
 * 		   and then and place the block. 
 * 		   Returns a pointer to an allocated block payload with the user 
 * 		   designated size.
 */
void *malloc(size_t size)
{
	dbg_printf("\n-----------------------------MALLOC---------------------------requested size:%zu\n", size);
	dbg_requires(mm_checkheap(__LINE__));
	size_t asize;	   // Adjusted block size
	size_t extendsize; // Amount to extend heap if no fit is found
	block_t *block;
	void *bp = NULL;

	if (heap_start == NULL) // Initialize heap if it isn't initialized
	{
		mm_init();
	}

	if (size == 0) // Ignore spurious request
	{
		dbg_ensures(mm_checkheap(__LINE__));
		return bp;
	}

	asize = round_up(size + wsize, dsize);

	// Search the appropriate list for a fit
	block = find_fit(asize);

	// If no fit is found, request more memory, and then and place the block
	if (block == NULL)
	{
		extendsize = max(asize, chunksize);
		dbg_printf("\nextend_heap called in malloc at line: %d   expand by size: %zu\n", __LINE__, extendsize);
		block = extend_heap(extendsize);
		if (block == NULL) // extend_heap returns an error
		{
			return bp;
		}
	}

	place(block, asize);
	bp = header_to_payload(block);

	dbg_printf("\nMalloc size %zd on (payload) address %p \n", size, bp);
	dbg_printf("\n----------------------------FINISHED MALLOC--------------------------\n");
	dbg_ensures(mm_checkheap(__LINE__));
	return bp;
}

/*
 * free: the free routine frees the block pointed to by bp that it writes the
 * 		 appropriate header and footer with the prev_alloc and prev_sseg status
 * 		 of the block pointed to by bp. Then free zeroes out the prev_alloc bit
 * 		 of the current block's successor. Lastly, it calls coalesce on the 
 * 		 current block to merge any free neighbors. Note this routine is only
 * 		 guaranteed to work when the passed pointer bp was returned by an earlier
 * 		 call to malloc, calloc, or realloc and has not yet been freed. 
 * 		 Returns nothing.
 */
void free(void *bp)
{
	dbg_printf("\n---------------------------------FREE--------------------------------");

	if (bp == NULL)
	{
		return;
	}

	block_t *block = payload_to_header(bp);
	dbg_printf("At: %p\n", block);
	size_t size = get_size(block);

	// get the prev_alloc and prev_sseg status of the block
	size_t prev_alloc = get_prev_alloc(block);
	size_t prev_sseg = get_prev_sseg(block);
	size |= prev_alloc;
	size |= prev_sseg;

	write_header(block, size, false);
	write_footer(block, size, false);
	find_next(block)->header &= (~prev_alloc_mask); // zero out prev_alloc bit of the successor

	coalesce(block);
	dbg_printf("\n-------------------------------FINISHED FREE---------------------------------\n");
}

/*
 * realloc: the realloc routine returns a pointer to an allocated region of at 
 * 			least size bytes with the following constraints:
 * 			1. if ptr is NULL, the call is equivalent to malloc(size)
 * 			2. if size==0, the call is equivalent to free(ptr)
 * 			3. if ptr is not NULL, first call malloc(size), if malloc fails,
 * 			   return NULL while the original block pointed to by ptr is left
 * 			   untouched. Otherwise, copy the old data into the new block, 
 * 		       and call free(ptr) afterwards. Lastly, it returns the pointer
 * 			   pointing to the newly allocated block.
 */
void *realloc(void *ptr, size_t size)
{
	dbg_printf("\n---------------------------------REALLOC----------------------------------------");
	block_t *block = payload_to_header(ptr);
	size_t copysize;
	void *newptr;

	// If size == 0, then free block and return NULL
	if (size == 0)
	{
		free(ptr);
		return NULL;
	}

	// If ptr is NULL, then equivalent to malloc
	if (ptr == NULL)
	{
		return malloc(size);
	}

	// Otherwise, proceed with reallocation
	newptr = malloc(size);
	// If malloc fails, the original block is left untouched
	if (newptr == NULL)
	{
		return NULL;
	}

	// Copy the old data
	copysize = get_payload_size(block); // gets size of old payload
	if (size < copysize)
	{
		copysize = size;
	}
	memcpy(newptr, ptr, copysize);

	// Free the old block
	free(ptr);
	dbg_printf("\n-------------------------------FINISHED REALLOC---------------------------------\n");
	return newptr;
}

/*
 * calloc: the calloc routine first checks if elements*size overflows. If so,
 * 		   return NULL. Otherwise, proceed by first calling malloc(elements*size)
 * 		   and then initializing all bits in the newly allocated block to 0.
 * 		   Lastly it returns the pointer pointing to the newly allocated block.
 */
void *calloc(size_t elements, size_t size)
{
	dbg_printf("\n---------------------------------CALLOC-------------------------------------------");
	void *bp;
	size_t asize = elements * size;

	if (asize / elements != size)
	{
		// Multiplication overflowed
		return NULL;
	}

	bp = malloc(asize);
	if (bp == NULL)
	{
		return NULL;
	}
	// Initialize all bits to 0
	memset(bp, 0, asize);
	dbg_printf("\n--------------------------------FINISHED CALLOC--------------------------------\n");
	return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * extend_heap: extends the heap size by size and rounds up size to meet the 
 * 				alignment of 16 bytes. Then it initializes the or afterwards.iginal
 * 				epilogue to be a free block and creates new epilogue header. 
 * 				Lastly it calls coalesce. 
 * 				Returns NULL if mem_sbrk fails. Otherwise, returns coalesce(block).
 */
static block_t *extend_heap(size_t size)
{
	void *bp;
	block_t *epilogue;
	size_t prev_alloc, prev_sseg;

	// save prev_alloc and prev_sseg flags of the current epilogue (end block)
	// before extending heap
	epilogue = (block_t *)((char *)mem_heap_hi() - 7);
	prev_alloc = get_prev_alloc(epilogue);
	prev_sseg = get_prev_sseg(epilogue);

	// Allocate an even number of words to maintain alignment
	size = round_up(size, dsize);
	if ((bp = mem_sbrk(size)) == (void *)-1)
	{
		return NULL;
	}

	// Initialize free block header/footer
	block_t *block = payload_to_header(bp);
	// inherit the prev_alloc and prev_sseg status of the original epilogue header
	size |= prev_alloc;
	size |= prev_sseg;
	write_header(block, size, false);
	write_footer(block, size, false);

	// Create new epilogue header
	block_t *block_next = find_next(block);
	block_next->header = 0;
	write_header(block_next, 0, true);

	// Coalesce in case the previous block was free

	return coalesce(block);
}

/*
 * remove_freeblock: removes the free block from its corresponding seg_list 
 * 			 		 or small_seg_list, and sets up the next and prev pointers
 * 					 appropriately.
 */
static void remove_freeblock(block_t *block)
{
	block_t *prev_free, *next_free;

	size_t size = get_size(block);
	if (block)
	{
		if (size <= min_block_size) // block belongs to small_seg_list
		{
			block_t *b;
			// traverse small_seg_list to find the target block
			for (b = small_seg_list; b != NULL; b = find_next_free(b))
			{
				if (b == block)
				{
					if (b == small_seg_list)
					{ // block is the root of small_seg_list
						small_seg_list = find_next_free(b); // set the successor to be the root
					}
					else
					{	// link prev_free to next_free
						prev_free->data.pointers.next = find_next_free(b);
					}
					return;
				}
				prev_free = b; // need to keep track of prev_free since small_seg_list is a singly linkedlist
			}
		}
		else // block belongs to seg_list
		{
			int seg_list_index = get_seg_list(size);
			prev_free = find_prev_free(block);
			next_free = find_next_free(block);
			if (!prev_free && !next_free)
			{ // root of free list && current block is the only element in seg_list
				seg_list[seg_list_index] = NULL;
			}
			else if (prev_free && !next_free)
			{ // end of free list
				prev_free->data.pointers.next = NULL;  // prev_free becomes the new end
				block->data.pointers.prev = NULL;
			}
			else if (!prev_free && next_free)
			{ // root of free list
				next_free->data.pointers.prev = NULL;  // next_free becomes the new root
				block->data.pointers.next = NULL;
				seg_list[seg_list_index] = next_free;
			}
			else
			{
				prev_free->data.pointers.next = next_free;	// link prev_free and next_free
				next_free->data.pointers.prev = prev_free;
			}
			return;
		}
	}
}

/*
 * insert_freeblock: inserts the free block into its corresponding seg_list 
 * 			 		 or small_seg_list with LIFO policy, and sets up the next 
 * 					 and prev pointers appropriately. 
 */
static void insert_freeblock(block_t *block)
{
	size_t size = get_size(block);
	if (size <= min_block_size) // block belongs to small_seg_list
	{
		block->data.pointers.next = small_seg_list;
		small_seg_list = block;
		return;
	}
	else  // block belongs to seg_list
	{
		int seg_list_index = get_seg_list(size);
		if (!seg_list[seg_list_index])
		{ // originally empty list
			seg_list[seg_list_index] = block;
			seg_list[seg_list_index]->data.pointers.prev = NULL;
			seg_list[seg_list_index]->data.pointers.next = NULL;
		}
		else
		{
			seg_list[seg_list_index]->data.pointers.prev = block; // point the root to block
			block->data.pointers.next = seg_list[seg_list_index];
			block->data.pointers.prev = NULL;
			seg_list[seg_list_index] = block;
		}
		return;
	}
}

/*
 * coalesce: coalesces block with its predecessor block and its successor 
 * 			 block accordingly.
 * 			 Returns the pointer to the free block with the lowest address 
 * 			 after coalescing.
 */
static block_t *coalesce(block_t *block)
{
	dbg_printf("\n!!!!!!!!!COALESCE!!!!!!!!!!\n");
	block_t *next, *prev;
	next = find_next(block);
	bool next_alloc = get_alloc(next);
	bool prev_alloc = get_prev_alloc(block) ? true : false;
	if (!prev_alloc)
	{
		prev = find_prev(block);
	}
	else
	{
		prev = NULL;
	}

	size_t size = get_size(block);

	if (!prev_alloc && next_alloc)
	{ // case 3
		dbg_printf("\ncase 3");
		size += get_size(prev);	 // update size (will inherit prev_sseg status of prev)
		size |= prev_alloc_mask; // inherit prev_alloc bit from previous block
		remove_freeblock(prev);	 // remove prev from free list
		write_header(prev, size, false);
		write_footer(prev, size, false);

		// if block originally belongs to small_seg_list, zero out
		// the prev_sseg bit of the successor
		// (min size of two blocks: 2*16=32 bytes > 16 bytes)
		if (get_size(block) == min_block_size)
		{
			next->header &= (~prev_sseg_mask);
		}

		block = prev;
	}
	else if (prev_alloc && !next_alloc)
	{ // case 2
		dbg_printf("\ncase 2");
		size += get_size(next);
		size |= prev_alloc_mask;
		remove_freeblock(next);
		write_header(block, size, false);
		write_footer(block, size, false);

		if (get_size(next) == min_block_size)
		{
			find_next(next)->header &= (~prev_sseg_mask);
		}
	}
	else if (!prev_alloc && !next_alloc)
	{ // case 4
		dbg_printf("\ncase 4");
		size += get_size(prev) + get_size(next);
		size |= prev_alloc_mask;
		remove_freeblock(prev);
		remove_freeblock(next);

		write_header(prev, size, false);
		write_footer(prev, size, false);

		if (get_size(next) == min_block_size)
		{
			find_next(next)->header &= (~prev_sseg_mask);
		}

		block = prev;
	}
	else
	{ // case 1
		dbg_printf("\ncase 1");
	}

	insert_freeblock(block);

	return block;
}

/*
 * place: allocates a block of asize. If the remaining block size is greater than or
 * 		  equal to the minimum block size, remove the block from free_list, perform split, and 
 * 		  then insert block_next into free_list. Otherwise, only remove the block from free_list.
 */
static void place(block_t *block, size_t asize)
{
	dbg_printf("\nAllocated total size: %zu\n", asize);
	size_t csize, prev_alloc, prev_sseg, temp;
	csize = get_size(block);
	prev_alloc = get_prev_alloc(block);
	prev_sseg = get_prev_sseg(block);

	if ((csize - asize) >= min_block_size) // if the remaining block size >= min_block_size
	{
		remove_freeblock(block);
		block_t *block_next;
		temp = asize | prev_alloc | prev_sseg;
		write_header(block, temp, true);

		block_next = find_next(block); // perform split
		if (asize == min_block_size)   // if allocated size is the minimum, set the prev_sseg flag of the successor
		{
			temp = (csize - asize) | prev_sseg_mask | prev_alloc;
			write_header(block_next, temp, false);
			write_footer(block_next, temp, false);
		}
		else
		{
			temp = (csize - asize) | prev_alloc;
			write_header(block_next, temp, false);
			write_footer(block_next, temp, false);
		}

		if ((csize - asize) == min_block_size) 
		{  // if the splitted block has min size, set sseg flag of its successor
	  	find_next(block_next) -> header |= prev_sseg_mask;
		}

		insert_freeblock(block_next);
	}
	else
	{  // if the remaining block size > min_block_size, allocate the whole block
		remove_freeblock(block);
		temp = csize | prev_alloc | prev_sseg;
		write_header(block, temp, true);

		if (csize == min_block_size)
		{
			find_next(block)->header |= prev_sseg_mask;
		}
	}
}

/*
 * find_fit: traverse the appropriate list according to asize and find the closest 25th fit
 */
static block_t *find_fit(size_t asize)
{
	block_t *block;
	block_t *block_bestfit = NULL;
	int if_firstfit = 1;
	int n = 0;
	size_t size_diff;
	int class = get_seg_list(asize);
	int index;

	if (asize == min_block_size)
	{
		for (block = small_seg_list; block != NULL; block = find_next_free(block))
		{
			if (asize <= get_size(block))
			{
				block_bestfit = block;
				return block_bestfit;
			}
		}
		class = 0;
	}

	// traverse seg_list to find a fit
	for (index = class; index < seg_list_size; index++)
	{
		for (block = seg_list[index]; block != NULL; block = find_next_free(block))
		{

			if (asize == get_size(block))
			{ // same size -> best fit
				block_bestfit = block;
				return block_bestfit;
			}

			if (asize < get_size(block))
			{
				n += 1;
				if (if_firstfit)
				{
					block_bestfit = block;
					if_firstfit = 0;
					size_diff = get_size(block) - asize;
				}

				if (get_size(block) - asize < size_diff)
				{
					block_bestfit = block;
				}

				if (n == nth_fit)
				{
					return block_bestfit;
				}
			}
		}
	}

	return block_bestfit; // no fit found
}

/* 
 * mm_checkheap: runs a series of tests to check the validity and consistency
 * 				 of the heap.
 * 				 Returns false if any of the tests fail. Otherwise returns true.
 * 
 * A list of tests:
 * 		1. check if all blocks in seg_list are free
 * 	    2. check if all pointers in seg_list point to valid free blocks
 * 		3. check the size and alignment of each block in seg_list
 * 		4. check if each block in seg_list actually exists in the heap
 * 
 * 		5. check if all blocks in small_seg_list are free
 * 		6. check if all pointers in small_seg_list point to valid free blocks
 * 		7. check the size and alignment of each block in small_seg_list
 * 		8. check if each block in small_seg_list actually exists in the heap
 * 
 *   	9. check if all pointers in heap point to valid heap blocks
 *  	10. check if any contiguous free blocks escaped coalescing
 * 		11. check if every free block is actually in the seg_list or small_seg_list
 * 		12. check if there is any overlap in allocated blocks
 */
bool mm_checkheap(int line)
{
	dbg_printf("\n!!!!!!!!!CHECKHEAP AT LINE %d!!!!!!!!!!!\n", line);

	block_t *block, *prologue, *epilogue, *b;
	bool free_list_is_complete = 0;
	bool free_list_is_valid = 0;
	int index;

	prologue = (block_t *)mem_heap_lo();
	epilogue = (block_t *)mem_heap_hi();

	for (index = 0; index < seg_list_size; index++)
	{
		for (block = seg_list[index]; block != NULL; block = find_next_free(block))
		{
			// check if all blocks in seg_list are free
			if (get_alloc(block))
			{
				dbg_printf("\nConsistency error: allocated block in seg_list!!!\n");
				return false;
			}

			// check if all pointers in seg_list point to valid free blocks
			if (block < prologue || block > epilogue)
			{
				dbg_printf("\nConsistency error: block in seg_list out of bounds!!!\n");
				return false;
			}

			// check the size and alignment of each block
			if (get_size(block) % 16 != 0 || get_size(block) < 16)
			{
				dbg_printf("\nConsistency error: invalid size of seg_list block!!!\n");
				return false;
			}

			// check if each block actually exists in the heap
			for (b = heap_start; get_size(b) > 0; b = find_next(b))
			{
				if (b == block)
				{
					free_list_is_valid = 1;
					break;
				}
			}
			if (free_list_is_valid == 0)
			{
				dbg_printf("\nConsistency error: seg_list block doesn't exist in heap'!!!\n");
			}
		}
	}

	free_list_is_valid = 0;
	for (block = small_seg_list; block != NULL; block = find_next_free(block))
	{
		// check if all blocks in small_seg_list are free
		if (get_alloc(block))
		{
			dbg_printf("\nConsistency error: allocated block in small_seg_list!!!\n");
			return false;
		}

		// check if all pointers in small_seg_list point to valid free blocks
		if (block < prologue || block > epilogue)
		{
			dbg_printf("\nConsistency error: block in small_seg_list out of bounds!!!\n");
			return false;
		}

		// check the size and alignment of each block
		if (get_size(block) % 16 != 0 || get_size(block) < 16)
		{
			dbg_printf("\nConsistency error: invalid size of small_seg_list block!!!\n");
			return false;
		}

		// check if each block actually exists in the heap
		for (b = heap_start; get_size(b) > 0; b = find_next(b))
		{
			if (b == block)
			{
				free_list_is_valid = 1;
				break;
			}
		}
		if (free_list_is_valid == 0)
		{
			dbg_printf("\nConsistency error: small_seg_list block doesn't exist in heap'!!!\n");
		}
	}

	for (block = heap_start; get_size(block) > 0; block = find_next(block))
	{
		// check if all pointers in heap point to valid heap blocks
		if (block < prologue || block > epilogue)
		{
			dbg_printf("\nConsistency error: invalid heap block in heap!!!\n");
			return false;
		}
		if (get_size(block) % 16 != 0 || get_size(block) < 16)
		{
			dbg_printf("\nConsistency error: invalid size of heap block in heap!!!\n");
			return false;
		}

		if (!get_alloc(block))
		{
			// check if any contiguous free blocks escaped coalescing
			if (!get_prev_alloc(block) || !get_alloc(find_next(block)))
			{
				dbg_printf("\nConsistency error: uncoalesced free block!!!\n");
				return false;
			}

			// check if every free block is actually in the seg_list or small_seg_list
			for (index = 0; index < seg_list_size; index++)
			{
				for (b = seg_list[index]; b != NULL; b = find_next_free(b))
				{
					if (b == block)
					{
						free_list_is_complete = 1;
						break;
					}
				}
			}

			if (free_list_is_complete == 0)
			{
				for (b = small_seg_list; b != NULL; b = find_next_free(b))
				{
					if (b == block)
					{
						free_list_is_complete = 1;
						break;
					}
				}
			}

			if (free_list_is_complete == 0)
			{
				dbg_printf("\nConsistency error: incomplete free_list!!!\n");
				return false;
			}
		}

		// check if there is any overlap in allocated blocks
		if (get_alloc(block))
		{
			block_t *next;
			next = find_next(block);
			if ((block_t *)((char *)block + get_size(block)) > next)
			{
				dbg_printf("\nConsistency error: block overlap!!!\n");
				return false;
			}
		}
	}

	dbg_printf(" \n");

	return true;
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
	return (x > y) ? x : y;
}

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
	return (n * ((size + (n - 1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc)
{
	return alloc ? (size | alloc_mask) : size;
}

/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
	return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
	return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header size.
 */
static word_t get_payload_size(block_t *block)
{
	size_t asize = get_size(block);
	return asize - wsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
	return (bool)(word & alloc_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
	return extract_alloc(block->header);
}

/*
 * get_prev_alloc: get the prev_alloc bit of block by clearing all bits but the
 * 				   prev_alloc bit. Returns the prev_alloc bit.       
 */
static size_t get_prev_alloc(block_t *block)
{
	return (block->header & prev_alloc_mask);
}

/*
 * get_prev_sseg: get the prev_sseg bit of block by clearing all bits but the
 * 				  prev_sseg bit. Returns the prev_sseg bit.         
 */
static size_t get_prev_sseg(block_t *block)
{
	return (block->header & prev_sseg_mask);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc)
{
	block_t *next;
	if ((size & size_mask) <= min_block_size)
	{
		next = (block_t *)(((char *)block) + dsize);
		next->header |= prev_sseg_mask;
	}

	block->header = pack(size, alloc);

	if (alloc)
	{
		find_next(block)->header |= prev_alloc_mask; // if allocated, set prev_alloc of the successor
	}
}

/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
	if (size <= min_block_size)
	{
		return;
	} // don't write footer to small_seg_list blocks
	word_t *footerp = (word_t *)((block->data.payload) + get_size(block) - dsize);
	*footerp = pack(size, alloc);
}

/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
	dbg_requires(block != NULL);
	block_t *block_next = (block_t *)(((char *)block) + get_size(block));

	dbg_ensures(block_next != NULL);
	return block_next;
}

/*
 * find_next_free: returns the next consecutive block in the free list            
 */
static block_t *find_next_free(block_t *block)
{
	block_t *block_next_free;
	block_next_free = block->data.pointers.next;
	return block_next_free;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
	// Compute previous footer position as one word before the header
	return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
	size_t size;
	if (get_prev_sseg(block))
	{
		size = min_block_size;
	}
	else
	{
		word_t *footerp = find_prev_footer(block);
		size = extract_size(*footerp);
	}

	return (block_t *)((char *)block - size);
}

/*
 * find_prev_free: returns the previous consecutive block in the free list            
 */
static block_t *find_prev_free(block_t *block)
{
	block_t *block_prev_free;
	block_prev_free = block->data.pointers.prev;
	return block_prev_free;
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
	return (block_t *)(((char *)bp) - offsetof(block_t, data));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
	return (void *)(block->data.payload);
}
