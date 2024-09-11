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
#include <limits.h>

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
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)
#define CLASSSIZE (8) 

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (unsigned int)(val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) (((char *)(bp) + GET_SIZE((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) (((char *)(bp) - GET_SIZE((char *)(bp)-DSIZE)))

// 추가된 선언
/* Given ptr in free list, get next and previous ptr in the list */
#define SUCC(bp) (*(void **)(char *)(bp + WSIZE))
#define PRED(bp) (*(void **)(bp))

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void putFreeBlock(void *bp, size_t size);
static void removeBlock(void *bp);
static int get_class_idx(size_t size);
static char **get_class(int idx);
static char *prologue_bp;

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// 해당 size에 맞는 클래스 인덱스 찾기
static int get_class_idx(size_t size)
{
    if (size == 0) {
        return -1;
    }
    size >>= 5;     // 32bit 위치부터 찾기 (블록의 최소 크기가 32bit)
    for (int i=0; i<CLASSSIZE; i++) {
        size >>= 1;
        if (size == 0) {
            return i;
        }
    }
    return CLASSSIZE-1;
}

// 해당 클래스 인덱스에 맞는 클래스 찾기
static char **get_class(int idx)
{
    return (char **)(prologue_bp + idx * WSIZE);
}

static void putFreeBlock(void *bp, size_t size)
{
    char **free_listp;

    free_listp = get_class(get_class_idx(size));
    SUCC(bp) = *free_listp;
    PRED(bp) = NULL;
    if (*free_listp != NULL) {
        PRED(*free_listp) = bp;
    }
    *free_listp = bp;
}

static void removeBlock(void *bp)
{
    if (PRED(bp)) {     // 이전 블록이 있는 경우
        SUCC(PRED(bp)) = SUCC(bp);
    } else {            // 이전 블록이 없으면 free_listp를 업데이트
        char **free_listp = get_class(get_class_idx(GET_SIZE(HDRP(bp))));
        *free_listp = SUCC(bp);
    }
    if (SUCC(bp)) {     // 다음 블록이 있는 경우
        PRED(SUCC(bp)) = PRED(bp);
    }
    SUCC(bp) = NULL;
    PRED(bp) = NULL;
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    //  LIFO 방식
    if (prev_alloc && next_alloc)
    { }
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));      // 다음 블록과 합침
        removeBlock(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));      // 이전 블록과 합침
        removeBlock(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else if (!prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        removeBlock(NEXT_BLKP(bp));
        removeBlock(PREV_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    putFreeBlock(bp, size);

    return bp;
}

/*
    extend_heap이 사용되는 경우 2가지
        1. 힙이 초기화될 때,
        2. mm_malloc이 적당한 fit을 찾지 못했을 때
*/
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    }
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *find_fit(size_t asize)
{
    char *min_bp = NULL;
    size_t min_size = ULONG_MAX;
    for (int i = get_class_idx(asize); i<CLASSSIZE; i++) {
        if (min_size != ULONG_MAX) {
            return min_bp;
        }
        char **free_listp = get_class(i);
        for (char *bp = *free_listp; bp != NULL; bp = SUCC(bp)) {
            if (asize <= GET_SIZE(HDRP(bp)) && GET_SIZE(HDRP(bp)) < min_size) {
                min_size = GET_SIZE(HDRP(bp));
                min_bp = bp;
            }
        }
    }
    return min_bp;
}

static void place(void *bp, size_t asize)
{
    removeBlock(bp);
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        coalesce(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((prologue_bp = mem_sbrk((CLASSSIZE+4)*WSIZE)) == (void *)-1) {
        return -1;
    }
    PUT(prologue_bp + 0*WSIZE, PACK(0, 0));                                 // 미사용 패딩
    PUT(prologue_bp + 1*WSIZE, PACK((CLASSSIZE+2)*WSIZE, 1));               // 프롤로그 헤더
    for (int i=2; i<CLASSSIZE+2; i++) {                                     // 블록 분할 관리 클래스
        PUT(prologue_bp + i*WSIZE, NULL);
    }
    PUT(prologue_bp + (CLASSSIZE+2)*WSIZE, PACK((CLASSSIZE+2)*WSIZE, 1));   // 프롤로그 풋터
    PUT(prologue_bp + (CLASSSIZE+3)*WSIZE, PACK(0, 1));                     // 에필로그 헤더
    prologue_bp += DSIZE;

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;       /* Adjusted block size */
    size_t extendsize;  /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    if (bp == NULL)
        return;

    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

