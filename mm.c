/*
 * mm.c
 *
 * 罗骏 2200011351@stu.pku.edu.cn
 * 
 * free block:
 *      header | next | prev | (padding) | foot
 * allocated block:
 *      header | payload | (padding)
 * header:
 *      size | prev_alloc | cur_alloc
 *      prev_alloc: 1: in memory, previous block is allocated
 *      cur_alloc: 1：current block is allocated 
 * Foot's content is equal to header
 * My convention to refer to above thing:
 *      header : p
 *      next : bp
 *      prev : pp
 *      foot: fp 
 * 
 * Since heapsize is smaller than 2^32 bytes, we can use pointers of
 * 4 bytes. But there's not 4 byte pointer in 64bit machine, the workaround
 * is use unsigned int. I use unsigned int as type of header, next, prev
 * and foot. It's easy to convert it to actual 64bit pointer, just add to
 * the base address.
 * 
 * prologue: has header, next, prev, no foot, set as allocated 
 * epilogue: has header, next, prev, no foot, set as allocated
 * 
 * Each of them takes 3*WSIZE = 12 bytes, just after prologue block is
 * a valid block, we don't need any padding, this block's bp is 16 thus is 
 * aligned. I use circular double linked list, thus prologue's prev is epilogue, 
 * epilogue's next is prologue.
 * 
 * In general, my method is explicit free list + LIFO insert + best fit
 * 
 */ 
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h> /*I need uintptr to convert pointer to unsigned long*/

#include "mm.h"
#include "memlib.h"

//#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Double word size (bytes) */
/* Extend heap by this amount, and this is a magic number,
 * I acquired this by keep trying :) */
#define CHUNKSIZE  (1u<<14)-(1u<<12) 
#define HEAPSIZE (1lu<<32) 

#define MAX(x, y) ((x) > (y)? (x) : (y)) 

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* need this variable to quickly convert 4 byte unsigned pointer to 
 * actual 8 byte pointer */
static unsigned long base;
/* input unsigned, return void* */
#define EXTEND_PTR(p) ((void*)(base + (unsigned long)(p)))

/* get the last 32bit of a void*, return unsigned, this can be implemented 
 * by simply type casting */
#define SHRINK_PTR(p) ((unsigned)(uintptr_t)(p))

/* input: unsigned
 * return: content of this unsigned pointer */
#define GET(p)       (*(unsigned *)(EXTEND_PTR(p))) 

/* input an unsigned pointer, put an unsigned value into it */
#define PUT(p, val)  (*(unsigned *)(EXTEND_PTR(p)) = (val))

#define PACK(size, alloc)  ((size) | (alloc))

#define CUR_ALLOC(p) (GET(p) & 0x1)

/*convert p, bp, pp, fp with each other */
#define BP2P(bp) ((bp) - WSIZE) 
#define BP2FP(bp) ((bp) + GET_SIZE(BP2P(bp)) - DSIZE)
#define FP2BP(fp) ((fp) - GET_SIZE(fp) + DSIZE)
#define PP2BP(pp) ((pp) - WSIZE) 
#define BP2PP(bp) ((bp) + WSIZE)

/* size stored here is asize, which includes size of head and foot (if has) */
#define GET_SIZE(p)  (GET(p) & ~0x7)  

/* input: unsigned，return: unsigned */
#define LINK_NEXT_BP(bp)  (GET(bp))
/* input: unsigned，return: unsigned */
#define LINK_PREV_PP(pp)  (GET(pp))

/*MEM stands for previous block in memory, not in link list */
#define MEM_PREV_ALLOC(p) ((GET(p) & 0b10) >> 1) 
#define MEM_NEXT_BP(bp) ((bp) + GET_SIZE(BP2P(bp)))
#define MEM_PREV_FP(bp) ((bp) - DSIZE) 

void mm_checkheap(int lineno);

static unsigned prol_bp;
static unsigned epil_bp;

/* for debugging */
static void checkbp_content(unsigned bp) {
    dbg_printf("bp:%u\n",bp);
    dbg_printf("*p:%u\n",GET(BP2P(bp)));
    dbg_printf("*bp:%u\n",GET(bp));
    dbg_printf("*pp:%u\n",GET(BP2PP(bp)));
    if ((bp != prol_bp) && (bp != epil_bp)) {
        dbg_printf("*fp:%u\n",GET(BP2FP(bp)));
    }
    dbg_printf("------------\n");
}

/* delete a free block in link list */
static inline void link_delete(unsigned bp) {
    
    unsigned prev_pp = LINK_PREV_PP(BP2PP(bp));
    unsigned prev_bp = PP2BP(prev_pp);
    unsigned next_bp = LINK_NEXT_BP(bp);
    unsigned next_pp = BP2PP(next_bp);

    PUT(prev_bp,next_bp);
    PUT(next_pp,prev_pp);
    return;
}

/* insert a free block in link list by LIFO, it is just after prologue block */
static inline void link_LIFOinsert(unsigned bp) {

    unsigned next_bp = LINK_NEXT_BP(prol_bp);
    unsigned next_pp = BP2PP(next_bp);    
    unsigned prev_bp = prol_bp;
    unsigned prev_pp = BP2PP(prev_bp);

    PUT(prev_bp,bp);
    PUT(bp,next_bp);
    PUT(BP2PP(bp),prev_pp);
    PUT(next_pp,BP2PP(bp));
    return;
}

/* set next block in memory as previous block in memory is allocated */
static inline void set_mem_next_alloc1(unsigned bp) {
    unsigned next_bp = MEM_NEXT_BP(bp);
    unsigned next_alloc = CUR_ALLOC(BP2P(next_bp));
    unsigned next_size = GET_SIZE(BP2P(next_bp));
    PUT(BP2P(next_bp),PACK(next_size,2 + next_alloc));
    /* attention! allocated block doesn't have foot */
    if (!next_alloc) {
        PUT(BP2FP(next_bp),PACK(next_size,2 + next_alloc));
    }
}

/* set next block in memory as previous block in memory is not allocated */
static inline void set_mem_next_alloc0(unsigned bp) {
    unsigned next_bp = MEM_NEXT_BP(bp);
    unsigned next_alloc = CUR_ALLOC(BP2P(next_bp));
    unsigned next_size = GET_SIZE(BP2P(next_bp));
    PUT(BP2P(next_bp),PACK(next_size,next_alloc));
    /* attention! allocated block doesn't have foot */
    if (!next_alloc) {
        PUT(BP2FP(next_bp),PACK(next_size,next_alloc));
    }
}

/* set current block is allocated */
static inline void set_cur_alloc1(unsigned bp,unsigned size) {
    unsigned prev_alloc = MEM_PREV_ALLOC(BP2P(bp));
    PUT(BP2P(bp), PACK(size, 2*prev_alloc+1));
}

/* initialize a new free block, setting header and foot 
 * this is used for a block that is originally a block */
static inline void init_free_block(unsigned bp, unsigned size) {
    unsigned prev_alloc = MEM_PREV_ALLOC(BP2P(bp)); 

    PUT(BP2P(bp),PACK(size, 2*prev_alloc));
    PUT(BP2FP(bp),PACK(size, 2*prev_alloc));
    return;
}

/* return a multiple of DSIZE*/
static inline size_t round_size(size_t size) {
    size_t asize;
    /* minimum free block is 16bytes, and it at most store 12bytes */
    if (size <= 3*WSIZE) {
        asize = 2*DSIZE;
    }
    /* round up to a multiple of DSIZE 
     * size+WSIZE because allocated block needs a header */
    else {
        asize = DSIZE * ((size + WSIZE + (DSIZE-1)) / DSIZE); 
    }
    return asize;
}

/* coalesce free block */
static unsigned coalesce(unsigned bp) {
    unsigned prev_alloc = MEM_PREV_ALLOC(BP2P(bp));
    unsigned next_alloc = CUR_ALLOC(BP2P(MEM_NEXT_BP(bp)));
    unsigned size = GET_SIZE(BP2P(bp));

    if (prev_alloc && next_alloc) {
        return bp;
    }

    /* with next block in memory */
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(BP2P(MEM_NEXT_BP(bp)));
        link_delete(MEM_NEXT_BP(bp));
        init_free_block(bp,size);
        return bp;
    }    

    /* with previous block in memory */
    else if (!prev_alloc && next_alloc) {
        link_delete(bp);
        size += GET_SIZE(MEM_PREV_FP(bp));
        bp = FP2BP(MEM_PREV_FP(bp));
        link_delete(bp);
        init_free_block(bp,size);
        link_LIFOinsert(bp);
        return bp;
    }

    /* with both */
    else {
        link_delete(bp);
        size += GET_SIZE(BP2P(MEM_NEXT_BP(bp))) + GET_SIZE(MEM_PREV_FP(bp));
        link_delete(MEM_NEXT_BP(bp));
        bp = FP2BP(MEM_PREV_FP(bp));
        link_delete(bp);
        init_free_block(bp,size);
        link_LIFOinsert(bp);
        return bp;
    }
}

/* new block logically placed in beginning of link list */
static unsigned extend_heap(unsigned size) {

    /* extend heap here */
    unsigned temp_p = SHRINK_PTR(mem_sbrk(size)); 

    unsigned bp = temp_p - DSIZE;
    unsigned prev_pp = LINK_PREV_PP(BP2PP(bp));
    unsigned prev_bp = PP2BP(prev_pp);
    
    /* new epilogue, and it's previous block in memory is free */
    epil_bp = bp + (unsigned)size;
    PUT(BP2P(epil_bp),0b01);
    PUT(epil_bp,prol_bp);
    PUT(prev_bp,epil_bp);
    PUT(BP2PP(epil_bp),prev_pp);
    PUT(BP2PP(prol_bp),BP2PP(epil_bp));

    init_free_block(bp,size);
    link_LIFOinsert(bp);

    return coalesce(bp);
}

/* best fit, if succeed return unsigned bp, otherwise return 0 
 * to improve efficiency, if the size difference is below 20, we can stop.
 * 20 is a magic number too. get it by keep trying :) */
static unsigned find_fit(unsigned asize) {
    unsigned tar_bp = 0;
    unsigned tar_size = HEAPSIZE - 1;
    for (unsigned bp = LINK_NEXT_BP(prol_bp); 
            bp != prol_bp; bp = LINK_NEXT_BP(bp)) {
        if (asize <= GET_SIZE(BP2P(bp))) {
            if (GET_SIZE(BP2P(bp)) < tar_size) {
                tar_bp = bp;
                tar_size = GET_SIZE(BP2P(bp));
                if (tar_size - asize <= 20) {
                    return tar_bp;
                }
            }
        }
    }
    return tar_bp;
}

/* place a block and set as allocated */
static void place(unsigned bp, unsigned asize) {
    unsigned csize = GET_SIZE(BP2P(bp));
 
    unsigned next_bp = LINK_NEXT_BP(bp);
    unsigned next_pp = BP2PP(next_bp);
    unsigned prev_pp = LINK_PREV_PP(BP2PP(bp));
    unsigned prev_bp = PP2BP(prev_pp);

    link_delete(bp);

    if ((csize - asize) >= 2*DSIZE) {
        /* in memory, previous block of next block is still free */
        set_cur_alloc1(bp,asize);

        /* set the left as a free block */
        bp = MEM_NEXT_BP(bp);
        PUT(BP2P(bp), PACK(csize-asize,0b10));
        PUT(BP2FP(bp), PACK(csize-asize,0b10));

        /*insert it to link list */
        PUT(prev_bp,bp);
        PUT(bp,next_bp);
        PUT(BP2PP(bp),prev_pp);
        PUT(next_pp,BP2PP(bp));
    }

    else {
        set_cur_alloc1(bp,csize);

        /* in memory, previous block of next block changes 
         * from free to allocated, thus needing to update next block */
        set_mem_next_alloc1(bp);
    }
}

/* initialize link list */
int mm_init(void) 
{
    dbg_printf("\n");
    dbg_printf("line:%d,function:%s\n",__LINE__,__FUNCTION__);

    base = (unsigned long)mem_heap_lo();
    void* root = mem_sbrk(6*WSIZE);

    unsigned tmp_root = SHRINK_PTR(root);

    PUT(tmp_root,0b01); /* prologue header */

    PUT(tmp_root+WSIZE,tmp_root+4*WSIZE); /* prologue bp */
    PUT(tmp_root+2*WSIZE,tmp_root+5*WSIZE); /* prologue pp */
    PUT(tmp_root+3*WSIZE,0b11); /* epilogue header*/
    PUT(tmp_root+4*WSIZE,tmp_root+WSIZE); /* epilogue bp*/
    PUT(tmp_root+5*WSIZE,tmp_root+2*WSIZE); /* epilogue pp*/

    prol_bp = tmp_root + WSIZE;
    epil_bp = tmp_root + 4*WSIZE;

    extend_heap(CHUNKSIZE);

    return 0;
}

/* with helper functions above, malloc is easy */
void *malloc (size_t size) {
    
    size_t asize;
    size_t extend_size;
    unsigned bp,req_size;
    
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    asize = round_size(size);
    if (asize >=  HEAPSIZE) {
        printf("overfull heapsize\n");
        return NULL;
    }

    req_size = (unsigned)(asize);
    if ((bp = find_fit(req_size)) != 0u) {         
        place(bp, req_size);
        return EXTEND_PTR(bp);
    }
    else {
        /* No fit found. Get more memory and place the block */
        extend_size = MAX(asize,CHUNKSIZE);                 
        if ((bp = extend_heap(extend_size)) == 0) {  
            return NULL;    
        }
        place(bp, asize);                      
        return EXTEND_PTR(bp);
    }
}

/* with helper functions above, free is easy */
void free(void* ptr) {

    if (ptr == NULL) {
        return;
    }

    unsigned bp = SHRINK_PTR(ptr);
    unsigned size = GET_SIZE(BP2P(bp));

    init_free_block(bp,size);

    set_mem_next_alloc0(bp);
    
    link_LIFOinsert(bp);

    coalesce(bp);

    return;
}

/* three cases:
 * 1. new_size <= old_size, we may get new free block 
 * 2. next block in memory is free and the total size can hold new_size
 *    use these two block together
 * 3. malloc new block */
void *realloc(void *oldptr, size_t size) {

    if (size >=  HEAPSIZE) {
        printf("overfull heapsize\n");
        return NULL;
    }

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(oldptr);
        return NULL;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
        return malloc(size);
    }

    unsigned bp = SHRINK_PTR(oldptr);
    unsigned old_size = GET_SIZE(BP2P(bp));
    unsigned new_size = (unsigned)round_size(size);
    unsigned next_bp = MEM_NEXT_BP(bp);
    unsigned next_p = BP2P(next_bp);
    unsigned next_size = GET_SIZE(next_p);

    if (new_size <= old_size) {
        dbg_printf("line:%d,function:%s,bp:%u\n",__LINE__,__FUNCTION__,bp);
        if (old_size - new_size >= 2*DSIZE) {
            /* change current block's size */
            PUT(BP2P(bp), new_size + 2*MEM_PREV_ALLOC(BP2P(bp))+1);

            /* new free block */
            next_bp = MEM_NEXT_BP(bp);
            PUT(BP2P(next_bp),PACK(0,0b10));
            init_free_block(next_bp,old_size-new_size);
            link_LIFOinsert(next_bp);
            set_mem_next_alloc0(next_bp);
            coalesce(next_bp);
        }
        return EXTEND_PTR(bp);

    }

    else if (CUR_ALLOC(next_p)==0 && new_size <= old_size + next_size) {

        link_delete(next_bp);

        old_size = old_size + next_size;

        if (old_size - new_size >= 2*DSIZE) {
            PUT(BP2P(bp), PACK(new_size,2*MEM_PREV_ALLOC(BP2P(bp))+ 1));

            /* new free block */
            next_bp = MEM_NEXT_BP(bp);
            /* this is a must for init */
            PUT(BP2P(next_bp),PACK(0,0b10));

            init_free_block(next_bp,old_size-new_size);
            link_LIFOinsert(next_bp);
        }
        else {
            PUT(BP2P(bp), PACK(old_size ,2*MEM_PREV_ALLOC(BP2P(bp))+ 1));
            set_mem_next_alloc1(bp);
        }
        return EXTEND_PTR(bp);
    }
    else {
        dbg_printf("line:%d,function:%s,bp:%u\n",__LINE__,__FUNCTION__,bp);
        void* new_bp = malloc(new_size);
        
        memcpy(new_bp, oldptr, old_size);

        free(EXTEND_PTR(bp));

        return new_bp;
    }
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/* check heap for debugging */
void mm_checkheap(int lineno) {
    dbg_printf("heapsize:%lu line:%d\n",mem_heapsize(),lineno);

    unsigned iter_free_block = 0;
    unsigned trav_free_block = 0;
    unsigned epil_pp = BP2PP(epil_bp);

    /* check prologue and epilogue block */
    if (CUR_ALLOC(BP2P(prol_bp)) != 1) {
        printf("line:%d checkheap: prol_alloc != 1\n",lineno);
    }
    if (CUR_ALLOC(BP2P(epil_bp)) != 1) {
        printf("line:%d checkheap: epil_alloc != 1\n",lineno);
    }

    /* iterate backwards in link list*/
    for (unsigned bp = LINK_NEXT_BP(prol_bp);bp != prol_bp;bp = LINK_NEXT_BP(bp)) {
        iter_free_block ++;
        checkbp_content(bp);
        unsigned pp = BP2PP(bp);
        unsigned next_bp = LINK_NEXT_BP(bp);
        unsigned next_pp = BP2PP(next_bp);

        if (bp != epil_bp && GET(BP2P(bp)) != GET(BP2FP(bp))) {
            printf("line:%d checkheap: %d whose p != fp\n",lineno,bp);
        }

        if (!in_heap(EXTEND_PTR(bp))) {
            printf("line:%d checkheap: %d not in heap\n",lineno,bp);
        }

        if (LINK_PREV_PP(next_pp) != pp) {
            printf("line:%d checkheap: %d not consistent\n",lineno,bp);
        }
    }

    /* iterate conversely in link list */
    for (unsigned pp = LINK_PREV_PP(epil_pp);pp != epil_pp;pp = LINK_PREV_PP(pp)) {
        trav_free_block ++;
    }

    if (trav_free_block != iter_free_block) {
        printf("line:%d checkheap: trav != iter,%d,%d\n",
        lineno,trav_free_block,iter_free_block);
    }

    /*iterate by memory, not including prologue and epilogue */
    for (unsigned bp = prol_bp + 3*WSIZE; bp!=epil_bp ;bp=MEM_NEXT_BP(bp)) {

        dbg_printf(" ... %u\n",bp);
        
        if (!aligned(EXTEND_PTR(bp))) {
            printf("line:%d checkheap: %d not aligned\n",lineno,bp);
        }
        if (!in_heap(EXTEND_PTR(bp))) {
            printf("line:%d checkheap: %d not in heap\n",lineno,bp);
        }

        unsigned p = BP2P(bp);
        unsigned size = GET_SIZE(p);

        if (size < 2 * DSIZE) {
            printf("line:%d checkheap: %d size too small\n",lineno,bp);
        }
        if (size % DSIZE != 0) {
            printf("line:%d checkheap: %d size not aligned\n",lineno,bp);
        }

        if (CUR_ALLOC(p) != MEM_PREV_ALLOC((BP2P(MEM_NEXT_BP(bp))))) {
            printf("line:%d checkheap: %d prev_alloc not consistent\n",lineno,bp);
        }

        if (MEM_PREV_ALLOC(p) == 0 && CUR_ALLOC(p) == 0) {
            printf("line:%d checkheap: a free block just before %d\n",lineno,bp);
        }
    }
    return;
}

