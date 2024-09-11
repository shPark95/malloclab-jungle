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

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)
#define CLASSSIZE 14

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (unsigned int)(val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define GET_ROOT(class) (*(void **)((char *)(prologue_bp) + (WSIZE * class)))
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 다음과 이전 블록의 블록 포인터를 각각 리턴
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))   // (다음 블록 포인터) = (현재 블록 포인터) + (현재 블록 사이즈)
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))  // (이전 블록 포인터) = (현재 블록 포인터) - (이전 블록 사이즈)

// 추가된 선언
/* Given ptr in free list, get next and previous ptr in the list */
#define SUCC(bp) (*(void **)(char *)(bp + WSIZE))
#define PRED(bp) (*(void **)(bp))

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *prologue_bp;

// 추가된 함수
static void putFreeBlock(void *bp);
static void removeBlock(void *bp);
static int find_bitposition(unsigned int size);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((prologue_bp = mem_sbrk((CLASSSIZE + 4) * WSIZE)) == (void *)-1)
        return -1;
    PUT(prologue_bp, 0);
    PUT(prologue_bp + (1 * WSIZE), PACK((CLASSSIZE + 2) * WSIZE, 1));
    for (int i = 2; i < CLASSSIZE+2; i++)
        PUT(prologue_bp + (i * WSIZE), NULL);
    PUT(prologue_bp + ((CLASSSIZE+2) * WSIZE), PACK((CLASSSIZE + 2) * WSIZE, 1));
    PUT(prologue_bp + ((CLASSSIZE+3) * WSIZE), PACK(0, 1));
    prologue_bp = prologue_bp + DSIZE;
    if (extend_heap(CLASSSIZE/WSIZE) == NULL)
        return -1;
    return 0;
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
        return NULL;
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    //  LIFO 방식
    if (prev_alloc && !next_alloc)
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
    putFreeBlock(bp);

    return bp;
}

static void putFreeBlock(void *bp)
{
    int class = find_bitposition(GET_SIZE(HDRP(bp)));
    void *ptr = GET_ROOT(class);
    SUCC(bp) = ptr;                // 가용리스트 첫번째 값 바꿈
    PRED(ptr) = bp;                // free_listp의 이전블록 가리키는 값 바꿔줌
    PRED(bp) = NULL;               // bp의 이전블록 가리키는 값 NULL로 수정
    ptr = bp;                      // free_listp 가리키는값 수정
}

static void removeBlock(void *bp)
{
    int class = find_bitposition(GET_SIZE(HDRP(bp)));
    void *ptr = GET_ROOT(class);
    if (PRED(bp) == NULL) {
        ptr = SUCC(bp);
        PRED(SUCC(bp)) = PRED(bp);        // 다음블록의 succesoor의 predecesor를 이전블록의 predecesor로 설정
        PRED(bp) = NULL;
    }
    else {
        PRED(SUCC(bp)) = PRED(bp);        // 다음블록의 succesoor의 predecesor를 이전블록의 predecesor로 설정
        SUCC(PRED(bp)) = SUCC(bp);        // 이전블록의 predecesor의 successor를 다음븥록의 successor로 설정
        SUCC(bp) = NULL;
        PRED(bp) = NULL;
    }
}

static void *find_fit(size_t asize)
{
    int class = find_bitposition(asize);
    void *ptr = GET_ROOT(class);
    /* First-fit search */
    void *bp;
    for (bp = ptr; !GET_ALLOC(HDRP(bp)); bp = SUCC(bp)) {
        if (asize <= (size_t)GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }
    return NULL;    /* No fit */
}

int find_bitposition(unsigned int size) {
    int position = -1; // 비트 위치는 0부터 시작하므로 -1로 초기화
    // 비트를 오른쪽으로 시프트하면서 위치를 찾음
    while (size > 0) {
        size >>= 1;    // 오른쪽으로 1비트씩 시프트
        position++;    // 시프트할 때마다 위치를 증가
        if (position >= 13)
            return position;
    }

    return position;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        removeBlock(bp);

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        putFreeBlock(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        removeBlock(bp);
    }
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
