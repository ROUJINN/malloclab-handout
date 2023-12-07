/*
 * mm.c
 *
 * 罗骏 2200011351@stu.pku.edu.cn
 * 
 * header的最后一位为1代表已经allocate,倒数第二位为1代表previous block allocated
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
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
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */ 

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

#define GET(p)       (*(unsigned int *)(p)) /*这是取了指针指向的内容的值*/
#define PUT(p, val)  (*(unsigned int *)(p) = (val))
#define PACK(size, alloc)  ((size) | (alloc))

#define CUR_ALLOC(p) (GET(p) & 0x1) /*1代表已经分配*/

#define BP2P(bp) ((char *)(bp) - WSIZE) /*由bp返回header的指针p*/
#define BP2FP(bp) ((char *)(bp) + GET_SIZE(BP2P(bp)) - DSIZE)
#define FP2BP(fp) ((char *)(fp) - GET_SIZE(fp) + DSIZE)
#define PP2BP(pp) ((char *)(pp) - WSIZE) 
#define BP2PP(bp) ((char *)(bp) + WSIZE)


#define GET_SIZE(p)  (GET(p) & ~0x7)  /*这个返回的size是asize，包含头尾*/

#define LINK_NEXT_BP(bp)  (GET(bp))
#define LINK_PREV_PP(pp)  (GET(pp))

#define MEM_PREV_ALLOC(p) ((GET(p) & 0b10) >> 1) /*MEM代表是物理内存上的前一个*/
#define MEM_NEXT_BP(bp) ((char*)(bp) + GET_SIZE(BP2P(bp)))
#define MEM_PREV_FP(bp) ((char*)(bp) - DSIZE) /*FP代表脚部指针，需要这个时前一个必定空闲，从而有脚部*/









static char *root = 0; /*先让这个一直指向序言块开始*/


/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) 
{
    

    /* Create the initial empty heap */
    root = mem_sbrk(2*WSIZE);
    PUT(root,PACK(0,1)); /* prologue header and only need header */
    PUT(root+WSIZE,PACK(0,1)); /* epilogue header*/

    extend_heap(CHUNKSIZE/WSIZE);
    PUT()
}

/*
 * malloc
 */
void *malloc (size_t size) {

    if (heap_listp == 0){
        mm_init();
    }
    
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;




    return NULL;
}

/*
 * free
 */
void free (void *bp) {

    size_t size = GET_SIZE(BP2P(bp));

    if (root == 0){
        mm_init();
    }


    coalesce(bp);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    return NULL;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {

    return NULL;
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

/*
 * mm_checkheap
 */
void mm_checkheap(int lineno) {

    void *bp,*heap_lo,*heap_hi;

    heap_lo = mem_heap_lo();
    heap_hi = mem_heap_hi();

    /*Check epilogue blocks.*/
    if (GET(heap_listp) != PACK(0,1)) {
        printf("epilogue error in line %d\n",lineno);
    }

    /*Check each block’s address alignment and .*/
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!aligned((void*)bp)) {
            printf("pointer not aligned in line %d\n",lineno);
        }
        if (!in_heap((void*)bp)) {
            printf("pointer not in heap in line %d\n",lineno);
        }
    }
}

static void *link_delete(void *bp) {
    
    void *prev_pp = LINK_PREV_PP(BP2PP(bp));
    void *prev_bp = PP2BP(prev_pp);
    void *next_bp = LINK_NEXT_BP(bp);
    void *next_pp = BP2PP(next_bp);

    PUT(prev_bp,next_bp);
    PUT(next_pp,prev_pp);
}

static void *link_LIFOinsert(void *bp) {
    void *next_bp = LINK_NEXT_BP(root);
    void *next_pp = BP2PP(next_bp);    

    PUT(root,bp);

    PUT(bp,next_bp);
    PUT(next_pp,BP2PP(bp));
}

static void *coalesce(void *bp) {
    unsigned prev_alloc = MEM_PREV_ALLOC(BP2P(bp));
    unsigned next_alloc = CUR_ALLOC(BP2P(MEM_NEXT_BP(bp)));
    unsigned prev_prev_alloc = MEM_PREV_ALLOC(MEM_PREV_FP(bp));
    size_t size = GET_SIZE(BP2P(p));

    if (prev_alloc && next_alloc) {
        link_LIFOinsert(bp);
        return bp;
    }

    /* 和后一个合并 */
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(BP2P(MEM_NEXT_BP(bp)));
        link_delete(MEM_NEXT_BP(bp));

        PUT(BP2P(bp), PACK(size, 0b10));
        PUT(BP2FP(bp), PACK(size, 0b10)); /*注意这里bp前的p的size已经更新了，所以可以直接BP2FP*/

        link_LIFOinsert(bp);
        return bp;
    }    

    /* 和前一个合并 */
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(MEM_PREV_FP(bp));
        PUT(BP2FP(bp),PACK(size, 2*prev_prev_alloc)); /*等价于pack 0b10或0b00*/
        bp = FP2BP(MEM_PREV_FP(bp));
        link_delete(bp);
        PUT(BP2P(bp),PACK(size, 2*prev_prev_alloc));
        link_LIFOinsert(bp);
    }

    /* 前后都合并 */
    else {
        size += GET_SIZE(BP2P(MEM_NEXT_BP(bp))) + GET_SIZE(MEM_PREV_FP(bp));
        link_delete(MEM_NEXT_BP(bp));
        bp = FP2BP(MEM_PREV_FP(bp));
        link_delete(bp);
        PUT(BP2P(bp),PACK(size, 2*prev_prev_alloc));
        PUT(BP2FP(bp), PACK(size, 2*prev_prev_alloc));
        link_LIFOinsert(bp);
        return bp;
    }
}

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 

    bp = mem_sbrk(size);
    
    
}

