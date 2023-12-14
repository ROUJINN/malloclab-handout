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
#include <stdint.h> /*自己加的，因为要uintptr*/

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
#define CHUNKSIZE  (1u<<12)  /* Extend heap by this amount (bytes) */
#define HEAPSIZE (1lu<<32) 

#define MAX(x, y) ((x) > (y)? (x) : (y)) 

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)


static inline unsigned long base() {
    return ((unsigned long)mem_heap_lo());
}

/* 给一个unsigned的指针返回void* */
#define EXTEND_PTR(p) ((void*)(base() + (unsigned long)(p)))

/* 拿void*指针的后32位作为unsigned，这里直接类型转换就是取后32位 */
#define SHRINK_PTR(p) ((unsigned)(uintptr_t)(p))

/*给一个unsigned，返回一个unsigned，此宏被很多其他宏调用*/
#define GET(p)       (*(unsigned *)(EXTEND_PTR(p))) 

/*给unsigned的指针，往里放unsigned的值*/
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

/* 给unsigned，返回unsigned */
#define LINK_NEXT_BP(bp)  (GET(bp))
/* 给unsigned，返回unsigned */
#define LINK_PREV_PP(pp)  (GET(pp))

/*MEM代表是物理内存上的前一个*/
#define MEM_PREV_ALLOC(p) ((GET(p) & 0b10) >> 1) 

#define MEM_NEXT_BP(bp) ((bp) + GET_SIZE(BP2P(bp)))

/*FP代表脚部指针，需要这个时前一个必定空闲，从而有脚部*/
#define MEM_PREV_FP(bp) ((bp) - DSIZE) 

void mm_checkheap(int lineno);

static void *root = NULL; /*prol的next*/
static unsigned prol_bp;

static void check4bp(unsigned bp) {
    printf("%u\n",bp);
    printf("%u\n",LINK_NEXT_BP(bp));
    printf("%u\n",LINK_NEXT_BP(LINK_NEXT_BP(bp)));
    printf("%u\n",LINK_NEXT_BP(LINK_NEXT_BP(LINK_NEXT_BP(bp))));
    return;
}

static void check4pp(unsigned pp) {
    printf("%u\n",pp);
    printf("%u\n",LINK_PREV_PP(pp));
    printf("%u\n",LINK_PREV_PP(LINK_PREV_PP(pp)));
    printf("%u\n",LINK_PREV_PP(LINK_PREV_PP(LINK_PREV_PP(pp))));

    return;
}

static void checkbp_content(unsigned bp) {
    printf("bp:%u\n",bp);
    printf("*p:%u\n",GET(BP2P(bp)));
    printf("*bp:%u\n",GET(bp));
    printf("*pp:%u\n",GET(BP2PP(bp)));
    if ((bp != prol_bp) && (bp!=PP2BP(LINK_PREV_PP(BP2PP(prol_bp))))) {
        printf("*fp:%u\n",GET(BP2FP(bp)));
    }
    printf("------------\n");
}

static void link_delete(unsigned bp) {
    
    unsigned prev_pp = LINK_PREV_PP(BP2PP(bp));
    unsigned prev_bp = PP2BP(prev_pp);
    unsigned next_bp = LINK_NEXT_BP(bp);
    unsigned next_pp = BP2PP(next_bp);

    PUT(prev_bp,next_bp);
    PUT(next_pp,prev_pp);
    return;
}

static void link_LIFOinsert(unsigned bp) {
    //dbg_printf("line:%d,function:%s\n",__LINE__,__FUNCTION__);
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

static void link_insert(unsigned bp) {
    unsigned next_bp = LINK_NEXT_BP(bp);
    unsigned next_pp = BP2PP(next_bp);

    unsigned prev_pp = LINK_PREV_PP(BP2PP(bp));
    unsigned prev_bp = PP2BP(prev_pp);

    PUT(prev_bp,bp);
    PUT(bp,next_bp);
    PUT(BP2PP(bp),prev_pp);
    PUT(next_pp,BP2PP(bp));
    return;
}

/*设置内存上下一个块 为前一个块已经分配*/
static void set_mem_next_alloc(unsigned bp) {
    unsigned next_bp = MEM_NEXT_BP(bp);
    unsigned cur_alloc = CUR_ALLOC(BP2P(next_bp));
    unsigned cur_size = GET_SIZE(BP2P(next_bp));
    PUT(BP2P(next_bp),PACK(cur_size,2+cur_alloc));
    if (!cur_alloc) {
        PUT(BP2FP(next_bp),PACK(cur_size,2+cur_alloc));
    }
    
}

static size_t round_size(size_t size) {
    size_t asize;
    /* 空闲块最小16byte=2*DSIZE，最多能存12byte=3*WSIZE */
    if (size <= 3*WSIZE) {
        asize = 2*DSIZE;
    }
    /*向上舍入到DSIZE的倍数，+WSIZE是因为已分配的块需要一个header*/
    else {
        asize = DSIZE * ((size + WSIZE + (DSIZE-1)) / DSIZE); 
    }
    return asize;
}

/*要合并，一定是空闲块合并，空闲块一定在链表中*/
static unsigned coalesce(unsigned bp) {
    unsigned prev_alloc = MEM_PREV_ALLOC(BP2P(bp));
    unsigned next_alloc = CUR_ALLOC(BP2P(MEM_NEXT_BP(bp)));
    unsigned prev_prev_alloc = MEM_PREV_ALLOC(MEM_PREV_FP(bp));
    unsigned size = GET_SIZE(BP2P(bp));

    if (prev_alloc && next_alloc) {
        dbg_printf("line:%d,function:%s\n",__LINE__,__FUNCTION__);
        return bp;
    }

    /* 和后一个合并 */
    else if (prev_alloc && !next_alloc) {
        dbg_printf("line:%d,function:%s\n",__LINE__,__FUNCTION__);

        size += GET_SIZE(BP2P(MEM_NEXT_BP(bp)));
        link_delete(MEM_NEXT_BP(bp));

        PUT(BP2P(bp), PACK(size, 0b10));
        PUT(BP2FP(bp), PACK(size, 0b10)); /*注意这里bp前的p的size已经更新了，所以可以直接BP2FP*/

        return bp;
    }    

    /* 和前一个合并 */
    else if (!prev_alloc && next_alloc) {
        dbg_printf("line:%d,function:%s\n",__LINE__,__FUNCTION__);

        link_delete(bp);
        
        size += GET_SIZE(MEM_PREV_FP(bp));

        unsigned mem_prev_fp = MEM_PREV_FP(bp);        
        bp = FP2BP(mem_prev_fp);
        
        link_delete(bp);
        mm_checkheap(__LINE__);

        PUT(BP2P(bp),PACK(size, 2*prev_prev_alloc));
        PUT(BP2FP(bp),PACK(size, 2*prev_prev_alloc));
        
        link_LIFOinsert(bp);
        return bp;
    }

    /* 前后都合并 */
    else {
        dbg_printf("line:%d,function:%s\n",__LINE__,__FUNCTION__);

        link_delete(bp);
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
static unsigned extend_heap(size_t words) {
    //dbg_printf("line:%d,function:%s\n",__LINE__,__FUNCTION__);

    /* Allocate an even number of words to maintain alignment */
    size_t size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 

    /*在这开辟新的堆*/
    unsigned temp_p = SHRINK_PTR(mem_sbrk(size)); 

    unsigned bp = temp_p - DSIZE;
    unsigned epil_bp = bp + (unsigned)size;
    unsigned prev_alloc = MEM_PREV_ALLOC(BP2P(bp)); /* 看epil的MEM上前一个是否alloc */
    unsigned prev_pp = LINK_PREV_PP(BP2PP(bp));
    unsigned prev_bp = PP2BP(prev_pp);
    
    
    /*新的epil，MEM上前一个是free的*/
    PUT(BP2P(epil_bp),0b01);
    PUT(epil_bp,prol_bp);
    PUT(prev_bp,epil_bp);
    PUT(BP2PP(epil_bp),prev_pp);
    PUT(BP2PP(prol_bp),BP2PP(epil_bp));

    /*新的块*/
    PUT(BP2P(bp),PACK(size, 2*prev_alloc));
    PUT(BP2FP(bp),PACK(size, 2*prev_alloc));

    /* 插入这个bp，新的块插在链表开始处 */
    link_LIFOinsert(bp);

    return coalesce(bp);
}

/* first fit，成功返回unsigned bp，否则返回0*/
static unsigned find_fit(unsigned asize) {
    unsigned bp;
    for (bp = LINK_NEXT_BP(prol_bp); bp != prol_bp; bp = LINK_NEXT_BP(bp)) {
        if (asize <= GET_SIZE(BP2P(bp))) {
            return bp;
        }
    }
    return 0;
}

static void place(unsigned bp, unsigned asize) {
    unsigned csize = GET_SIZE(BP2P(bp));
    unsigned prev_alloc = MEM_PREV_ALLOC(BP2P(bp));

    unsigned next_bp = LINK_NEXT_BP(bp);
    unsigned next_pp = BP2PP(next_bp);
        
    unsigned prev_pp = LINK_PREV_PP(BP2PP(bp));
    unsigned prev_bp = PP2BP(prev_pp);

    link_delete(bp);

    if ((csize - asize) >= 2*DSIZE) {
        /*当前块设置为已分配*/
        PUT(BP2P(bp), PACK(asize, 2*prev_alloc+1));
        /*剩下的块设置为空闲块并且插入链表*/
        bp = MEM_NEXT_BP(bp);
        PUT(BP2P(bp), PACK(csize-asize,0b10));
        PUT(BP2FP(bp), PACK(csize-asize,0b10));

        PUT(prev_bp,bp);
        PUT(bp,next_bp);
        PUT(BP2PP(bp),prev_pp);
        PUT(next_pp,BP2PP(bp));
    }

    else {
        /*当前块设置为已分配*/
        PUT(BP2P(bp), PACK(csize, 2*prev_alloc+1));

        /*由于当前块从自由变成了已分配，则内存上下一个块要相应改一下*/
        set_mem_next_alloc(bp);
    }
}

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) 
{
    dbg_printf("\n");
    dbg_printf("line:%d,function:%s\n",__LINE__,__FUNCTION__);

    root = mem_sbrk(6*WSIZE);

    unsigned tmp_root = SHRINK_PTR(root);

    PUT(tmp_root,0b01); /* prologue header */

    PUT(tmp_root+WSIZE,tmp_root+4*WSIZE); /* prologue bp */
    PUT(tmp_root+2*WSIZE,tmp_root+5*WSIZE); /* prologue pp */
    PUT(tmp_root+3*WSIZE,0b11); /* epilogue header*/
    PUT(tmp_root+4*WSIZE,tmp_root+WSIZE); /* epilogue bp*/
    PUT(tmp_root+5*WSIZE,tmp_root+2*WSIZE); /* epilogue pp*/

    root = root + WSIZE;
    prol_bp = SHRINK_PTR(root);

    extend_heap(CHUNKSIZE/WSIZE);

    mm_checkheap(__LINE__);

    return 0;
}

/*
 * malloc
 */
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
        dbg_printf("line:%d,function:%s,req_size:%u,bp_loc:%p\n",__LINE__,__FUNCTION__,req_size,EXTEND_PTR(bp));

        place(bp, req_size);

        mm_checkheap(__LINE__); 

        return EXTEND_PTR(bp);
    }

    else {

        /* No fit found. Get more memory and place the block */
        extend_size = MAX(asize,CHUNKSIZE);                 
        if ((bp = extend_heap(extend_size/WSIZE)) == 0) {  
            return NULL;    
        }

        place(bp, asize);

        dbg_printf("line:%d,function:%s,req_size:%u,bp_loc:%p\n",__LINE__,__FUNCTION__,req_size,EXTEND_PTR(bp));        

        mm_checkheap(__LINE__);
                              
        return EXTEND_PTR(bp);
    }
}

/*
 * free
 */
void free(void* ptr) {
    dbg_printf("line:%d,function:%s,bp:%u\n",__LINE__,__FUNCTION__,SHRINK_PTR(ptr));
    //printf("%p\n",ptr);

    if (ptr == NULL) {
        return;
    }

    unsigned bp = SHRINK_PTR(ptr);
    unsigned size = GET_SIZE(BP2P(bp));
    unsigned mem_next_size = GET_SIZE(BP2P(MEM_NEXT_BP(bp)));
    unsigned mem_next_alloc = CUR_ALLOC(BP2P(MEM_NEXT_BP(bp)));
    unsigned mem_prev_alloc = MEM_PREV_ALLOC(BP2P(bp));

    PUT(BP2P(bp), PACK(size,2*mem_prev_alloc)); /*把当前块末尾的设成0*/
    
    PUT(BP2FP(bp), PACK(size,2*mem_prev_alloc));

    PUT(BP2P(MEM_NEXT_BP(bp)),PACK(mem_next_size,mem_next_alloc));
    if (!mem_next_alloc) {
        PUT(BP2FP(MEM_NEXT_BP(bp)),PACK(mem_next_size,mem_next_alloc));
    }
    
    link_LIFOinsert(bp);

    coalesce(bp);
    mm_checkheap(__LINE__);

    return;
}

/*
 * realloc - you may want to look at mm-naive.c
 */
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

    // unsigned old_bp = SHRINK_PTR(oldptr);
    // unsigned old_size = GET_SIZE(BP2P(old_bp));
    // unsigned new_size = (unsigned) size;
    // unsigned epil_bp = PP2BP(LINK_PREV_PP(BP2PP(prol_bp)));

    // if (new_size <= old_size) {
    //     if (old_size - new_size >= 2*DSIZE) {
    //         /*改变当前块的大小，不变后两位*/
    //         PUT(BP2P(bp), );
    //         (GET(p) & 0b11) + old_size - new_size
    //         /*剩下的块设置为空闲块并且插入链表*/
    //         bp = MEM_NEXT_BP(bp);
    //         PUT(BP2P(bp), PACK(csize-asize,0b10));
    //         PUT(BP2FP(bp), PACK(csize-asize,0b10));

    //         link_LIFOinsert(bp);
    //         /*设置内存上后一个块的pre_alloc*/
    //     }
    //     else {

    //     }
        
    //     PUT(old_bp,)
        
    // }
    // else if (MEM_NEXT_BP(bp) == epil_bp) {

    // }
    // else {
    //     void*bp = malloc(new_size);
    //     unsigned bp = SHRINK_PTR(bp);
        
    //     memcpy(bp, oldptr, oldsize);

    //     free(old_bp);
    // }
    unsigned old_bp = SHRINK_PTR(oldptr);
    void* newptr = malloc(size);
    unsigned oldsize = GET_SIZE(BP2P(old_bp));
    unsigned newsize = (unsigned) size;
    if(newsize < oldsize) oldsize = newsize;
    memcpy(newptr, oldptr, oldsize);

    /* Free the old block. */
    free(oldptr);

    return newptr;
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
 * • Checking the heap (implicit list, explicit list, segregated list):
– Check epilogue and prologue blocks.
– Check each block’s address alignment.
– Check heap boundaries.
– Check each block’s header and footer: size (minimum size, alignment), previous/next allocate/free bit consistency, header and footer matching each other.
– Check coalescing: no two consecutive free blocks in the heap.

• Checking the free list (explicit list, segregated list):
– All next/previous pointers are consistent (if A’s next pointer points to B, B’s previous pointer
should point to A).
– All free list pointers points between mem heap lo() and mem heap high().
– Count free blocks by iterating through every block and traversing free list by pointers and see if
they match.
– All blocks in each list bucket fall within bucket size range (segregated list)
 */
void mm_checkheap(int lineno) {
    dbg_printf("heapsize:%lu line:%d\n",mem_heapsize(),lineno);

    unsigned iter_free_block = 0;
    unsigned trav_free_block = 0;
    unsigned epil_pp = LINK_PREV_PP(BP2PP(prol_bp));

    /*检查序言*/
    //checkbp_content(prol_bp);

    /*链表，往后遍历*/
    for (unsigned bp = LINK_NEXT_BP(prol_bp);bp != prol_bp;bp = LINK_NEXT_BP(bp)) {
        iter_free_block ++;
        //checkbp_content(bp);
        unsigned pp = BP2PP(bp);
        unsigned next_bp = LINK_NEXT_BP(bp);
        unsigned next_pp = BP2PP(next_bp);

        if (!in_heap(EXTEND_PTR(bp))) {
            printf("line:%d checkheap: %d not in heap\n",lineno,bp);
        }

        if (LINK_PREV_PP(next_pp) != pp) {
            printf("line:%d checkheap: %d not consistent\n",lineno,bp);
        }
    }

    /*链表，往前遍历*/
    for (unsigned pp = LINK_PREV_PP(epil_pp);pp != epil_pp;pp = LINK_PREV_PP(pp)) {
        trav_free_block ++;
    }

    if (trav_free_block != iter_free_block) {
        printf("line:%d checkheap: trav != iter,%d,%d\n",lineno,trav_free_block,iter_free_block);
    }

    /*内存上一个个往后遍历*/
    for (unsigned bp = prol_bp + 3*WSIZE; bp!=PP2BP(epil_pp) ;bp=MEM_NEXT_BP(bp)) {
        //dbg_printf(" ... %u\n",bp);
        if (!aligned(EXTEND_PTR(bp))) {
            printf("line:%d checkheap: %d not aligned\n",lineno,bp);
        }
    }
    return;

}

