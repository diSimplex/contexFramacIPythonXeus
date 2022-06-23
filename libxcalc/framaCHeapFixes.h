
#ifndef FRAMAC_HEAP_FIXES_H
#define FRAMAC_HEAP_FIXES_H


#ifdef __FRAMAC__

// The following is modelled on Frama-C's share/libc/stdlib.h definition
// of calloc.
//     ensures initialization: \initialized(((char *)\result)+(0..nmemb*sizeof(TokenObj)-1));
//     ensures zero_initialization: \subset(((char *)\result)[0..nmemb*sizeof(TokenObj)-1], {0});
/*@
  allocates \result;
  assigns __fc_heap_status \from indirect:nmemb, __fc_heap_status;
  assigns \result \from indirect:nmemb, indirect:__fc_heap_status;

  behavior allocation:
    assumes can_allocate: is_allocable(nmemb * sizeof(TokenObj));
    ensures allocation: \fresh(\result, nmemb * sizeof(TokenObj));
    ensures initialization: \initialized(((TokenObj *)\result)+(0..nmemb-1));
    ensures validPtrs: \valid((TokenObj*)\result[0..nmemb-1]);
    ensures zeroInitType: \subset(((TokenObj*)\result[0..nmemb-1])->type, {0});


  behavior no_allocation:
    assumes cannot_allocate: !is_allocable(nmemb * sizeof(TokenObj));
    assigns \result \from \nothing;
    allocates \nothing;
    ensures null_result: \result == \null;

  complete behaviors;
  disjoint behaviors;
 */
extern TokenObj *TokenObjCalloc(size_t nmemb);

#else

#define TokenObjCalloc(numItems) (TokenObj*)calloc(numItems, sizeof(TokenObj))

#endif

#endif