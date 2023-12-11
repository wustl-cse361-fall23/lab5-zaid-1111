/*
 ******************************************************************************
 *                               mm.c                                         *
 *           64-bit struct-based implicit free list memory allocator          *
 *                      without coalesce functionality                        *
 *                 CSE 361: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *                     insert your documentation here. :)                     *
 *                                                                            *
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
#define NUM_FREE_LISTS 10

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*sizeof(word_t);       // double word size (bytes)
static const size_t min_block_size = 4*sizeof(word_t); // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t size_mask = ~(word_t)0xF;
typedef struct block {
    word_t header;
    union{
        struct{
            struct block *next_free;  // Pointer to next_free free block
            struct block *prev_free;
        };
      // Pointer to previous free block
    char payload[0];
    };          // Flexible array member for the payload
} block_t;



/* Global variables */
/* Pointer to first block */
static block_t *free_list_heads[NUM_FREE_LISTS];
static block_t *heap_start = NULL;

bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static int get_free_list_index(size_t size);

static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static void add_to_free_list(block_t *block); //added for modularity
static void remove_from_free_list(block_t *block);
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
/*
 * <what does mm_init do?>
 */
bool mm_init(void) 
{
    // Initialize all segregated free list heads to NULL
    int i;
    for (i = 0; i < NUM_FREE_LISTS; i++) {
        free_list_heads[i] = NULL;
    }

    // Create the initial empty heap 
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));
    dbg_printf("Heap start: %p\n", start);
    if (start == (void *)-1) {
        return false;
    }

    start[0] = pack(0, true); // Prologue header
    start[1] = pack(0, true); // Prologue footer
    heap_start = (block_t *) &(start[1]);

    // Extend the empty heap with a free block of chunksize bytes
    block_t *initial_block = extend_heap(chunksize);
    dbg_printf("Initial block: %p, Size: %zu\n", initial_block, get_size(initial_block));
    if (initial_block == NULL) {
        return false;
    }

    // Check heap consistency
    dbg_printf("Checking heap after init...\n");
    dbg_requires(mm_checkheap(__LINE__));
    dbg_printf("Heap initialized successfully\n");
    return true;
}


/*
 * <what does mmalloc do?>
 */
 // CHECKED
void *malloc(size_t size) 
{
    dbg_requires(mm_checkheap(__LINE__));
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_start == NULL) { // Initialize heap if it isn't initialized
        mm_init();
    }

    if (size == 0) { // Ignore this request
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + dsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {  
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) { // extend_heap returns an error
            return bp;
        }
    }
    dbg_printf("Place: block address = %p, payload address = %p, size = %zu\n", 
        (void*)block, header_to_payload(block), asize);
    place(block, asize);
    
    bp = header_to_payload(block);
    dbg_printf("Malloc: block address = %p, payload address = %p, size = %zu\n", 
        (void*)block, bp, asize);
    dbg_requires(mm_checkheap(__LINE__));
    return bp;
} 

//DIDN'T-CHECK!
static void remove_from_free_list(block_t *block) {
    size_t size = get_size(block);
    int index = get_free_list_index(size);  // Use the same function to find the correct list

    // If the block is the first in the list
    if (block->prev_free == NULL) {
        free_list_heads[index] = block->next_free;
    } else {
        block->prev_free->next_free = block->next_free;
    }

    // If the block is not the last in the list
    if (block->next_free != NULL) {
        block->next_free->prev_free = block->prev_free;
    }

    // Clear the next_free and prev_free pointers of the block
    block->next_free = NULL;
    block->prev_free = NULL;
}

/*
 * <what does free do?>
 */
void free(void *bp)
{
    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    write_header(block, size, false);
    write_footer(block, size, false);
    coalesce(block);
}


/*
 * <what does realloc do?>
 */
void *realloc(void *ptr, size_t size)
{
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
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/*
 * <what does calloc do?>
 */
void *calloc(size_t elements, size_t size)
{
    void *bp;
    size_t asize = elements * size;

    if (asize/elements != size)
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

    return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * <what does extend_heap do?>
 */
static block_t *extend_heap(size_t size) 
{
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    
    // Initialize free block header/footer 
    block_t *block = payload_to_header(bp);
    write_header(block, size, false);
    write_footer(block, size, false);
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true);

    // Coalesce in case the previous block was free
    return coalesce(block);
}

//DIDN'T CHECK
// Helper function to add a block to the free list
static void add_to_free_list(block_t *block) {
    size_t size = get_size(block);
    int index = get_free_list_index(size);  // Use the previously defined function to get the correct free list index

    // Insert block at the start of the appropriate free list
    block->next_free = free_list_heads[index];
    block->prev_free = NULL;

    // Update the next block's prev_free if the list is not empty
    if (free_list_heads[index] != NULL) {
        free_list_heads[index]->prev_free = block;
    }

    // Set the new head of the free list
    free_list_heads[index] = block;
}
/*
 * <what does coalesce do?>
 */
static block_t *coalesce(block_t *block) {
    block_t *prev_block = find_prev(block);
    block_t *next_block = find_next(block);
    bool prev_alloc = get_alloc(prev_block) || prev_block == block; // Check if previous block is allocated or if it is the same as the current block (at the start of the heap)
    bool next_alloc = get_alloc(next_block); // Check if next block is allocated
    size_t size = get_size(block);

    if (prev_alloc && next_alloc) {  // Case 1: No coalescing
        add_to_free_list(block);
        return block;
    }

    if (!prev_alloc) {  // Coalesce with previous block
        size += get_size(prev_block);
        remove_from_free_list(prev_block);
        block = prev_block;
    }

    if (!next_alloc) {  // Coalesce with next block
        size += get_size(next_block);
        remove_from_free_list(next_block);
    }

    write_header(block, size, false);
    write_footer(block, size, false);
    add_to_free_list(block);

    return block;
}
/*
 * <what does place do?>
 */
static void place(block_t *block, size_t asize) {
    size_t csize = get_size(block);

    remove_from_free_list(block);  // Remove block from its current free list

    if ((csize - asize) >= min_block_size) {  // Split the block
        write_header(block, asize, true);
        write_footer(block, asize, true);
        block_t *block_next = find_next(block);
        size_t remaining_size = csize - asize;
        write_header(block_next, remaining_size, false);
        write_footer(block_next, remaining_size, false);
        add_to_free_list(block_next);  // Add the remaining part to the free list
    } else {  // Don't split
        write_header(block, csize, true);
        write_footer(block, csize, true);
    }
}
/*
 * <what does find_fit do?>
 * find_fit - Find a fit for a block with asize bytes in the free list
 */
// Nth Fit Strategy with segregated free lists

static block_t *find_fit(size_t asize) {
    block_t *best_fit = NULL;
    size_t min_size_diff = SIZE_MAX;
    int search_iterations = 0;
    const int max_iterations = 12;  // Define a limit for search iterations

    int start_index = get_free_list_index(asize);
    int i;
    for (i = start_index; i < NUM_FREE_LISTS; i++) {
        block_t *block;
        for (block = free_list_heads[i]; block != NULL; block = block->next_free) {
            // Check if the block is free and large enough
            if (!get_alloc(block) && asize <= get_size(block)) {
                size_t size_diff = get_size(block) - asize;

                // Update best fit if this block is a better fit
                if (size_diff < min_size_diff) {
                    best_fit = block;
                    min_size_diff = size_diff;
                }

                // If the search has gone on for too long, return the current block if it's good enough
                if (++search_iterations >= max_iterations) {
                    if (best_fit != NULL) {
                        return best_fit;
                    }
                    // If we haven't found any fit yet, return this block
                    if (asize <= get_size(block)) {
                        return block;
                    }
                }
            }
        }
    }
    return best_fit; // Return the best fit found, or NULL if none found
}


/* 
 * <what does your heap checker do?>
 * Please keep modularity in mind when you're writing the heap checker!
 */
bool mm_checkheap(int line)  
{ 
    block_t *current = heap_start;
    // Check if the heap has been initialized
    if (current == NULL) {
        dbg_printf("Heap is not initialized.\n");
        return false;
    }
    while(get_size(current)==0)
    {
        current = find_next(current);
    }
    while (get_size(current) > 0) {
        // Check alignment of each block
        dbg_printf("checkHeap: Payload is at line %d, address: %p\n", line, header_to_payload(current));
        if (((size_t)header_to_payload(current) % dsize) != 0) {
            dbg_printf("Error: Block not aligned at line %d\n", line);
            return false;
        }

        // Check if each block's size meets the minimum block size requirement
        if (get_size(current) < min_block_size) {
            dbg_printf("Error: Block size is less than minimum at line %d\n", line);
            return false;
        }

        // For free blocks, check if headers and footers match
        if (!get_alloc(current)) {
            word_t *footerp = (word_t *)((current->payload) + get_size(current) - dsize);
            if (current->header != *footerp) {
                dbg_printf("Error: Header and footer do not match at line %d\n", line);
                return false;
            }
        }

        // Check for contiguous free blocks that have not been coalesced
        if (!get_alloc(current) && !get_alloc(find_next(current))) {
            dbg_printf("Error: Contiguous free blocks not coalesced at line %d\n", line);
            return false;
        }

        current = find_next(current);
    }

    // Check the final block for correctness
    if (!get_alloc(current) || get_size(current) != 0) {
        dbg_printf("Error: Final block is not correct at line %d\n", line);
        return false;
    }
    dbg_printf("check-heap passed\n");
    (void) line;
    return true;
}



static int get_free_list_index(size_t size) {
    if (size <= 64) return 0;
    else if (size <= 128) return 1;
    else if (size <= 256) return 2;
    else if (size <= 512) return 3;
    else {
        int index = 4;
        size_t current_size = 1024;
        while (size > current_size && index < (NUM_FREE_LISTS - 1)) {
            current_size *= 2;
            index++;
        }
        return index;
    }
}


/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

/*
 * round_up: Rounds size up to next_free multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
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
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - dsize;
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
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc)
{
    block->header = pack(size, alloc);
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, alloc);
}


/*
 * find_next: returns the next_free consecutive block on the heap by adding the
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
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload);
}
