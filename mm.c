/*
 * mm.c
 *
 * 罗骏 2200011351@stu.pku.edu.cn
 * 
 * header的最后一位为1代表已经allocate,倒数第二位为1代表MEM上previous block allocated，这个十分巧妙。
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

#define MAX(x, y) ((x) > (y)? (x) : (y)) 

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

 
static unsigned long base = (*(unsigned long *)mem_heap_lo()) & 0x00000000;

/* 给一个unsigned的指针返回unsigned long */
#define EXTEND_PTR(p) (base + (unsigned long)p) 

/* 拿void*指针的后32位作为unsigned，这里直接类型转换就是取后32位 */
#define SHRINK_PTR(p) ((unsigned)(p))

/*返回一个unsigned*/
#define GET(p)       (*(unsigned *)(EXTEND_PTR(p))) 

/*给unsigned的指针，往里放东西*/
#define PUT(p, val)  (*(unsigned *)(EXTEND_PTR(p)) = (val))
#define PACK(size, alloc)  ((size) | (alloc))

#define CUR_ALLOC(p) (GET(p) & 0x1)

/*由bp返回header的指针p，注意这里返回的是unsigned*/
#define BP2P(bp) ((bp) - WSIZE) 
#define BP2FP(bp) ((bp) + GET_SIZE(BP2P(bp)) - DSIZE)
#define FP2BP(fp) ((fp) - GET_SIZE(fp) + DSIZE)
#define PP2BP(pp) ((pp) - WSIZE) 
#define BP2PP(bp) ((bp) + WSIZE)

/*size是asize，包含头尾，类型是unsigned*/
#define GET_SIZE(p)  (GET(p) & ~0x7)  

/* 返回unsigned */
#define LINK_NEXT_BP(bp)  (GET(bp))
#define LINK_PREV_PP(pp)  (GET(pp))

/*MEM代表是物理内存上的前一个*/
#define MEM_PREV_ALLOC(p) ((GET(p) & 0b10) >> 1) 

#define MEM_NEXT_BP(bp) ((bp) + GET_SIZE(BP2P(bp)))

/*FP代表脚部指针，需要这个时前一个必定空闲，从而有脚部*/
#define MEM_PREV_FP(bp) ((bp) - DSIZE) 

// static void place(void *bp, size_t asize);
// static void *find_fit(size_t asize);
// static void *extend_heap(size_t words);
// static void *coalesce(void *bp);
// static void link_insert(void *bp);
// static void link_LIFOinsert(void *bp);
// static void link_delete(void *bp);

void mm_checkheap(int lineno);

static void *root = 0; /*prol的next*/

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) 
{
    root = mem_sbrk(6*WSIZE);
    unsigned tmp_root = SHRINK_PTR(root);

    PUT(tmp_root,PACK(0,0b01)); /* prologue header */
    PUT(tmp_root+WSIZE,tmp_root+3*WSIZE); /* prologue bp */
    PUT(tmp_root+2*WSIZE,NULL); /* prologue pp */
    PUT(tmp_root+WSIZE,PACK(0,0b11)); /* epilogue header*/
    PUT(tmp_root+WSIZE,NULL); /* epilogue bp*/
    PUT(tmp_root+WSIZE,tmp_root+2*WSIZE); /* epilogue pp*/

    root = root + WSIZE;

    extend_heap(CHUNKSIZE/WSIZE);
    return 0;
}

/*
 * malloc
 */
void *malloc (size_t size) {

    size_t asize;
    size_t extend_size;
    void *bp;

    if (root == 0){
        mm_init();
    }
    
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;
    
    /*空闲块最小16byte*/
    if (size <= 3*WSIZE) {
        asize = 2*DSIZE;
    }
    else {
        asize = DSIZE * ((size + WSIZE + (DSIZE-1)) / DSIZE); /*向上舍入到DSIZE的倍数，+WSIZE是因为已分配的块需要一个header*/
    }

    if ((bp = find_fit(asize)) != NULL) {  
        place(bp, asize);                  
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extend_size = MAX(asize,CHUNKSIZE);                 
    if ((bp = extend_heap(extend_size/WSIZE)) == NULL)  
        return NULL;                                  
    place(bp, asize);                                 
    return bp;
}

/*
 * free
 */
void free(void *bp) {

    size_t size = GET_SIZE(BP2P(bp));
    unsigned prev_alloc = MEM_PREV_ALLOC(BP2P(bp));

    if (root == 0){
        mm_init();
    }

    PUT(BP2P(bp), PACK(size,2*prev_alloc)); /*这里需要清除一下，因为后面coalesce有可能直接返回bp*/

    coalesce(bp);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    // size_t oldsize;
    // void *newptr;

    // /* If size == 0 then this is just free, and we return NULL. */
    // if(size == 0) {
    //     free(oldptr);
    //     return 0;
    // }

    // /* If oldptr is NULL, then this is just malloc. */
    // if(oldptr == NULL) {
    //     return malloc(size);
    // }
    // return NULL;

    /*要什么复制数据之类的，先不管*/
    return NULL;
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

/*
 * mm_checkheap
 */
void mm_checkheap(int lineno) {

    // void *bp,*heap_lo,*heap_hi;

    // heap_lo = mem_heap_lo();
    // heap_hi = mem_heap_hi();

    // /*Check epilogue blocks.*/
    // if (GET(heap_listp) != PACK(0,1)) {
    //     printf("epilogue error in line %d\n",lineno);
    // }

    // /*Check each block’s address alignment and .*/
    // for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    //     if (!aligned((void*)bp)) {
    //         printf("pointer not aligned in line %d\n",lineno);
    //     }
    //     if (!in_heap((void*)bp)) {
    //         printf("pointer not in heap in line %d\n",lineno);
    //     }
    // }
}

static void link_delete(void *bp) {
    
    void *prev_pp = LINK_PREV_PP(BP2PP(bp));
    void *prev_bp = PP2BP(prev_pp);
    void *next_bp = LINK_NEXT_BP(bp);
    void *next_pp = BP2PP(next_bp);

    PUT(prev_bp,next_bp);
    PUT(next_pp,prev_pp);
    return;
}

static void link_LIFOinsert(void *bp) {
    void *next_bp = LINK_NEXT_BP(root);
    void *next_pp = BP2PP(next_bp);    
    void *prev_bp = root;
    void *prev_pp = BP2PP(prev_bp);

    PUT(prev_bp,bp);
    PUT(bp,next_bp);
    PUT(BP2PP(bp),prev_pp);
    PUT(next_pp,BP2PP(bp));
    return;
}

static void link_insert(void *bp) {
    void *next_bp = LINK_NEXT_BP(bp);
    void *next_pp = BP2PP(next_bp);    
    void *prev_pp = LINK_PREV_PP(BP2PP(bp));
    void *prev_bp = PP2BP(prev_pp);

    PUT(prev_bp,bp);
    PUT(bp,next_bp);
    PUT(BP2PP(bp),prev_pp);
    PUT(next_pp,BP2PP(bp));
    return;
}

static void *coalesce(void *bp) {
    unsigned prev_alloc = MEM_PREV_ALLOC(BP2P(bp));
    unsigned next_alloc = CUR_ALLOC(BP2P(MEM_NEXT_BP(bp)));
    unsigned prev_prev_alloc = MEM_PREV_ALLOC(MEM_PREV_FP(bp));
    size_t size = GET_SIZE(BP2P(bp));

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
        return bp;
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

/* 新申请的块逻辑上放在链表最开始处 */
static void *extend_heap(size_t words) {

    /* Allocate an even number of words to maintain alignment */
    size_t size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 

    void *temp_p = mem_sbrk(size);
    void *bp = temp_p - DSIZE;
    void *epil_bp = bp + size;
    unsigned prev_alloc = MEM_PREV_ALLOC(BP2P(bp)); /* 看epil的MEM上前一个是否alloc */
    void *prev_pp = LINK_PREV_PP(BP2PP(bp));
    void *prev_bp = PP2BP(bp);
    
    /*新的epil*/
    PUT(epil_bp,NULL);
    PUT(BP2PP(epil_bp),prev_pp);
    PUT(prev_bp,epil_bp);

    /*新的块*/
    PUT(BP2P(bp),PACK(size, 2*prev_alloc));
    PUT(BP2FP(bp),PACK(size, 2*prev_alloc));

    /* 插入这个bp，新的块插在链表开始处 */
    link_LIFOinsert(bp);

    return coalesce(bp);
}

/* first fit */
static void* find_fit(size_t asize) {
    void *bp;
    for (bp = root; GET_SIZE(BP2P(bp)) > 0; bp = LINK_NEXT_BP(bp)) {
        if (asize <= GET_SIZE(BP2P(bp))) {
            return bp;
        }
    }
    return NULL;
}

static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(BP2P(bp));
    unsigned prev_alloc = MEM_PREV_ALLOC(BP2P(bp));

    if ((csize - asize) >= 2*DSIZE) {
        PUT(BP2P(bp), PACK(asize, 2*prev_alloc));
        bp = MEM_NEXT_BP(bp);
        PUT(BP2P(bp), PACK(csize-asize,0b10));
        PUT(BP2FP(bp), PACK(csize-asize,0b10));
    }

    else {
        PUT(BP2P(bp), PACK(csize, 2*prev_alloc));
        PUT(BP2FP(bp), PACK(csize, 2*prev_alloc));
    }
}