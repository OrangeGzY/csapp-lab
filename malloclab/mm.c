/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4           /* word  */

#define DSIZE 8           /* dword */

#define MAX(x,y)    ((x)>(y)?(x):(y))

#define GET(p)  (*(unsigned int *)(p))
#define PUT(p,val)  (*(unsigned int *)(p) = (val))  //4 bytes
#define PACK(size,alloc)    ((size) | (alloc))

#define HDRP(bp)    ((char *)(bp)-WSIZE)            //取chunk header
#define FTRP(bp)    ((char *)(bp)+GET_SIZE(HDRP(bp))-DSIZE)//取chunk footer

#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)              //是否为alloc状态，还是free状态

#define NEXT_BLKP(bp)   ((char *)(bp)+GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp)   ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

#define FD(bp)  ( (char *)(bp) )            //fd指针前指
#define BK(bp)  ( (char *)(bp) + WSIZE )    //bk指针后指

#define IDLE 1<<12

/* some useful static data */
static char *heap_listp = NULL;      /* our heap is put into the stack */
static char *bins_listp = NULL;
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t size);
static void place(void *bp,size_t asize);
static void unlink_free_chunk(char *bp);
static char *find_bin(size_t size);
static void insert_into_bin(char *bp);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(14*WSIZE))==(void *)-1) return -1;

    /* 采用伙伴系统，2的幂次划分bins */
    PUT(heap_listp,0);              
    PUT(heap_listp+(1*WSIZE),0);    
    PUT(heap_listp+(2*WSIZE),0);    
    PUT(heap_listp+(3*WSIZE),0);    
    PUT(heap_listp+(4*WSIZE),0);    
    PUT(heap_listp+(5*WSIZE),0);    
    PUT(heap_listp+(6*WSIZE),0);    
    PUT(heap_listp+(7*WSIZE),0);    
    PUT(heap_listp+(8*WSIZE),0);    
    PUT(heap_listp+(9*WSIZE),0);    
    PUT(heap_listp+(10*WSIZE),0);
    PUT(heap_listp+(11*WSIZE),PACK(DSIZE,1));
    PUT(heap_listp+(12*WSIZE),PACK(DSIZE,1));
    PUT(heap_listp+(13*WSIZE),PACK(0,1));

    bins_listp = heap_listp;
    heap_listp += (12*WSIZE);

    if((extend_heap(IDLE/DSIZE))==NULL) return -1;
    return 0;
}


/*
1.When we init the heap, extend_heap will be called.
2.When mm_malloc cannot find a suitable chunk.
*/
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words%2) ? (words+1)*DSIZE : words*DSIZE;       //对齐

    if((long)(bp=mem_sbrk(size))==(void *)-1)               //开堆，返回bp，此时bp指向chunk payload而非chunk header
        return NULL;

    PUT(HDRP(bp),PACK(size,0));                             //设置free chunk header：size/0
    PUT(FTRP(bp),PACK(size,0));                             //设置free chunk footer：size/0

    /*此时fd和bk指针都是空*/
    PUT(FD(bp),NULL);
    PUT(BK(bp),NULL);

    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));                     //设置此free chunk后面为新chunk的头部。
    
    return coalesce(bp);                                    //若上一个chunk也是free状态，那么我们需要合并上一个chunk
}


/*
chunk 合并,插入合并后的freechunnk
*/
static void *coalesce(void *bp)
{
    size_t pre_chunk = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_chunk = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    size_t tmp;

    if(pre_chunk && next_chunk) //前后都没有free chunk，不需要合并
    {
        //return bp;              //直接返回当前chunk
        insert_into_bin(bp);
        return bp;    
    }

    else if(!pre_chunk && next_chunk)//前一个chunk处于free状态，做前向合并
    {
       
        tmp = GET_SIZE(HDRP(PREV_BLKP(bp)));  //加上要合并的前一个chunk的size
        size += tmp;
        unlink_free_chunk(PREV_BLKP(bp));       //把上一个已经处于free状态的chunk unlink掉。
        PUT(FTRP(bp),PACK(size,0));             //设置当前chunk的footer为free
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        bp =  PREV_BLKP(bp);               
        insert_into_bin(bp);
        return bp;    
    }

    else if(pre_chunk && !next_chunk)//后一个chunk处于free状态，做后向合并
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        unlink_free_chunk(NEXT_BLKP(bp));
        PUT(HDRP(bp),PACK(size,0));
        //PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
        insert_into_bin(bp);
        return bp;
    }

    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))+GET_SIZE(FTRP(NEXT_BLKP(bp)));
        unlink_free_chunk(PREV_BLKP(bp));
        unlink_free_chunk(NEXT_BLKP(bp));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
        insert_into_bin(bp);
        return bp;
    }
    
}
static void unlink_free_chunk(char *bp)
{
    char *bin = find_bin(GET_SIZE(HDRP(bp)));
    char *fd = GET(FD(bp));
    char *bk = GET(BK(bp));
    if(fd == NULL)
    /*bin中第一个chunk unlink*/
    {
        if(bk!=NULL)
        {
            PUT((FD(bk)),0);
        }
        PUT(bin,bk);
    }
    else
    /*unlink bin的中间某个chunk*/
    {
        if(bk!=NULL)
        {
            /* simple unlink process */
            PUT(FD(bk),fd);
        }
        PUT(BK(fd),bk);
    }
    PUT(FD(bp),NULL);
    PUT(BK(bp),NULL);
}
static char *find_bin(size_t size)
{
    char *targetbin;
    int bin_index = 0;
    if(size<=8) 
        bin_index=0;
    else if(size<=16) 
        bin_index= 1;
    else if(size<=32) 
        bin_index= 2;
    else if(size<=64) 
        bin_index= 3;
    else if(size<=128) 
        bin_index= 4;
    else if(size<=256) 
        bin_index= 5;
    else if(size<=512) 
        bin_index= 6;
    else if(size<=2048) 
        bin_index= 7;
    else if(size<=4096) 
        bin_index= 8;
    else 
        bin_index= 9;

    targetbin =  bins_listp+(bin_index*WSIZE);
    return targetbin;
}
static insert_into_bin(char *bp)
{
    char *targetbin = find_bin(GET_SIZE(HDRP(bp)));
    char *traverse = GET(targetbin);
    char *old_first = GET(targetbin);
    char *pre=targetbin;

    /*扫描bin中的chunk*/
    while(traverse!=NULL)
    {
        
        if(GET_SIZE(HDRP(traverse))  >= GET_SIZE(HDRP(bp)) )
        {
            /*查找到了插入的位置，在bin的中间*/
            break; 
        }
        pre = traverse;
        traverse = GET(BK(traverse)); 
    }

    if(pre==targetbin)
    {
        /*在bin的头部插入*/
        PUT(targetbin,bp);//bin --> bp --> first
        PUT(BK(bp),traverse); //bp --> first
        PUT(FD(bp),NULL); //bin (<--) bp --> first
        if(traverse!=NULL)
        {
            /*当old first不空时*/
            PUT(FD(traverse),bp);  //bin --> bp --> <-- first
        }
    }
    else
    {
        /*在bin的中间插入*/
        PUT(BK(pre),bp);
        PUT(FD(bp),pre);
        PUT(BK(bp),traverse);
        if(traverse!=NULL)
        {
            /*如果此时不是最后一个chunk*/
            /*防止非法地址访问*/
            PUT(FD(traverse),bp);
        }
    }

}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    void *bp=NULL;
    size_t adjusted_size;
    if(size==0)
    {
        return;
    }
    else if(size<=DSIZE)
    {
        adjusted_size = DSIZE*2;    //对齐到0x10
    }
    else
    {
        adjusted_size = (
            DSIZE*(
                (size+(DSIZE)+(DSIZE-1))/DSIZE
            )
        );
    }
   
    if((bp = find_fit(adjusted_size))!=NULL)    //如果在free list中找到了合适的chunk
    {
        //printf("request size:0x%x,find size:0x%x",size,GET_SIZE(HDRP(bp)));
        place(bp,adjusted_size);
        return bp;
    }

    //在freelist中没找到对应的合适的chunk
    int extend_size = MAX(adjusted_size,IDLE);
    if((bp = extend_heap(extend_size/DSIZE))==NULL)
    {
        return NULL;
    }
    place(bp,adjusted_size);
    return bp;
}

static void *find_fit(size_t size)
{
    char *bin = find_bin(size);
    //char *p;

    /* 扫描bins */
    for(bin;bin!=(heap_listp-2*WSIZE);bin+=WSIZE)
    {
        /* 扫描bins中的freechunk */
        char *p = GET(bin);
        while(p != NULL)
        {
            if(GET_SIZE(HDRP(p))>=size) return p;
            p = GET(BK(p));
        }
    }
    return NULL;    /*没找到orz*/
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    //printf("mm_free:0x%x\n",GET_SIZE(HDRP(ptr)));
    if(ptr==NULL)
    {
        return ;
    }
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr),PACK(size,0));
    PUT(FTRP(ptr),PACK(size,0));
    //free当前chunk之后处理合并相关情况。
    PUT(FD(ptr),NULL);
    PUT(BK(ptr),NULL);
    coalesce(ptr);      //在处理合并时插入freelist
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    size_t oldSize;
    
    if(size==0)
    {
        //size=0时等价于调用free
        mm_free(ptr);
        return 0;
    }
    
    if(ptr==NULL)
    {
        //ptr为0时等价于调用malloc
        return mm_malloc(size);
    }

    oldSize = GET_SIZE(HDRP(ptr));; //保存oldsize

    /* 重新对齐size */
    if(size<=DSIZE){
        size = 2*DSIZE;
    }else{
        size = DSIZE*((size+DSIZE+(DSIZE-1))/DSIZE);
    }

    /*如果调整之后size没变，相当于还是当前的chunk*/
    if(oldSize==size)
    {
        return ptr;
    }

    /*调整后的size大于oldsize*/
    if(oldSize<size)
    {
        
         if( (newptr = mm_malloc(size)) == NULL)
        {
            return -1;
        }
        memcpy(newptr,ptr,oldSize);
        mm_free(ptr);
        return newptr;
    }    
}

static void place(void *bp,size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    unlink_free_chunk(bp);
    if((csize-asize)>=(2*DSIZE))    //计算我们申请的size和返回的chunksize的差值
    {
        /* 如果差值大于2 DSIZE，那么进行切割 */
        PUT(HDRP(bp),PACK(asize,1));
        PUT(FTRP(bp),PACK(asize,1));
        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp),PACK(csize-asize,0));
        PUT(FTRP(bp),PACK(csize-asize,0));
        /*切割后处理fd、bk指针*/
        PUT(FD(bp),0);
        PUT(BK(bp),0);
        /*将切割后的freechunk插入freelist*/
        coalesce(bp);
    }
    else
    {
        /* 否则直接返回整个chunk */
        PUT(HDRP(bp),PACK(csize,1));
        PUT(FTRP(bp),PACK(csize,1));
    }
}














