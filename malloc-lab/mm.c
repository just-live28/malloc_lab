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
#include <stddef.h>

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
    ""};

#define ALIGNMENT 8

/* 사이즈를 8의 배수로 올림 */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))              // 인자 p가 참조하는 워드를 읽어서 리턴
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 인자 p가 가리키는 워드에 val 저장

#define GET_SIZE(p) (GET(p) & ~0x7) // 헤더 or 푸터의 size 비트 리턴
#define GET_ALLOC(p) (GET(p) & 0x1) // 헤더 or 푸터의 할당 비트 리턴

#define HDRP(bp) ((char *)(bp) - WSIZE)                      // 헤더를 가리키는 포인터 리턴
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 푸터를 가리키는 포인터 리턴

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 다음 블록의 시작 포인터 리턴
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록의 시작 포인터 리턴

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static char *heap_listp;

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    // 짝수 워드 배수 size만큼 힙 메모리 할당
    if (words % 2) {
        size = (words + 1) * WSIZE;
    } else {
        size = words * WSIZE;
    }

    if ((long)(bp = mem_sbrk(size)) == -1) {
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0));           // Free block 헤더
    PUT(FTRP(bp), PACK(size, 0));           // Free block 푸터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   // 새 에필로그 헤더

    return coalesce(bp);
}

static void *coalesce(void *bp) {
    size_t prev_alloc = (GET_ALLOC(FTRP(PREV_BLKP(bp))));
    size_t next_alloc = (GET_ALLOC(HDRP(NEXT_BLKP(bp))));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        return bp;
    }

    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

static void *find_fit(size_t asize) // first fit 구현
{
    char *bp = heap_listp + 8;                               // heap_listp는 항상 프롤로그 블록의 중간
    while ((GET_SIZE(HDRP(bp)) | !GET_ALLOC(HDRP(bp))) != 0) // bp가 에필로그 블록이 아니면
    {
        size_t bp_size = GET_SIZE(HDRP(bp));
        int alloc = GET_ALLOC(HDRP(bp));
        if (alloc == 1 || bp_size < asize)
        {
            bp += bp_size;
            continue;
        }

        return bp;
    }

    return NULL;
}

static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    if (csize - asize >= 2 * DSIZE) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // 4Word의 초기 힙을 만들고, PADDING, PROLOGUE_HEADER, PROLOGUE_FOOTER, EPILOGUE_HEADER 할당
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) {
        return -1;
    }
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));
    heap_listp += (2*WSIZE);

    // 최초 Free Block 공간을 위한 힙 확장
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0) {
        return NULL;
    }

    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL)
        return mm_malloc(size);
    if (size == 0)
    {
        mm_free(ptr);
        return NULL;
    }

    size_t old_block = GET_SIZE(HDRP(ptr)); // 헤더+푸터 포함
    size_t old_payload = old_block - DSIZE; // 페이로드의 크기 -> 옮겨야 할 데이터
    size_t new_asize;
    if (size <= DSIZE) {
        new_asize = 2 * DSIZE;
    } else {
        new_asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    // Case1: 새 크기가 더 작거나 같으면 해당 블록에 그대로 배치
    if (new_asize <= old_block) 
    {
        place(ptr, new_asize);
        return ptr; /* in-place, 주소 유지 */
    }

    // Case2: 다음 블록이 Free block이고 해당 블록을 합친 크기가 새 크기를 수용 가능할 때
    if (!(GET_ALLOC(HDRP(NEXT_BLKP(ptr)))) &&
        old_block + (GET_SIZE(HDRP(NEXT_BLKP(ptr)))) >= new_asize)
    {

        size_t total = old_block + (GET_SIZE(HDRP(NEXT_BLKP(ptr))));
        PUT(HDRP(ptr), PACK(total, 0));
        PUT(FTRP(ptr), PACK(total, 0));

        place(ptr, new_asize);
        return ptr; /* 역시 in-place */
    }

    // Case3: 다음 블록이 할당된 상태이거나, Free더라도 합친 크기가 새 크기를 수용 불가능할 때
    void *new_ptr = mm_malloc(size);
    if (new_ptr == NULL)
        return NULL;

    size_t copy;
    if (old_payload < size) {
        copy = old_payload;
    } else {
        copy = size;
    }

    memmove(new_ptr, ptr, copy);    // 겹치지 않는 복사

    mm_free(ptr);
    return new_ptr;
}
