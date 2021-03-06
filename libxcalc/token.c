
#include <string.h>
#include <ctype.h>
#include <stdlib.h>

#include "xeus-calc/token.h"
#include "framaCHeapFixes.h"

char *operators    = "-+/*^()";
int   precedence[] = {10, 10, 20, 20, 30, 40, 40};

  //ensures \result==\null || \fresh{Old,Here}(\result, \block_length{Here}(\result));
  //assigns \result \from theToken;

/*
  allocates \result;
  behavior allocation:
    assumes can_allocate: is_allocable(sizeof(TokenObj));
    ensures \fresh{Old,Here}(\result, sizeof(TokenObj));
    ensures \result != \null;
    assigns \result;

  behavior no_allocation:
    assumes cannot_allocate: !is_allocable(sizeof(TokenObj));
    ensures \result==\null;
    assigns \result \from \nothing;

  complete behaviors no_allocation, allocation;
  disjoint behaviors no_allocation, allocation;
 */
 /*@
  requires valid_read_string(theToken);
  requires 0 <= tokenLen < \block_length(theToken);
  requires 0 <= tokenType < TOKEN_VAL+1;
  assigns \result \from theToken, tokenLen, tokenType, indirect:__fc_heap_status;
  */
TokenObj *newTokenObj(const char* theToken, size_t tokenLen, int tokenType) {
  TokenObj *newTObj = TokenObjCalloc(1);
  if (newTObj == NULL) return NULL;

  //@ assert \valid(newTObj);
  newTObj->type     = tokenType;
  newTObj->len      = tokenLen;
  newTObj->value    = 0;
  //if (tokenType == TOKEN_VAL) newTObj->value = atof(newTObj->token);
  if (tokenType == TOKEN_VAL) newTObj->value = atof(theToken);
  newTObj->token    = strndup(theToken, tokenLen);
  return newTObj;
}


#ifdef FALSE0

/*
  ensures ???
 */
void updatePrecedence(TokenObj *aToken) {
  if (aToken->type != TOKEN_OP ) return ;

  int index = strstr(operators, aToken->token) - operators;
  if (!index) return ;

  aToken->precedence = precedence[index];
}

/*@
  requires \valid(pubList);
  ensures \valid(\result);
 */
char *publishPubList(TokenObj *pubList) {
	size_t pubListLen = 10;
	TokenObj *nextPubItem = pubList;
	/*
	  loop assigns nextPutItem;
	  loop assigns pubListLen;
	 */
	while (nextPubItem) {
		pubListLen += strlen(nextPubItem->token);
		nextPubItem = nextPubItem->next;
	}

	char *result = calloc(1, pubListLen);
	nextPubItem = pubList;
  while (nextPubItem)	{
  	strcat(result, nextPubItem->token);
		nextPubItem = nextPubItem->next;
  }

  return result;
}

/*
  ensures ???
 */
void freeThisTokenObj(TokenObj *aToken) {

	if (aToken->token) free(aToken->token);
	aToken->token      = NULL;

  aToken->next       = NULL;
	aToken->len        = 0;
  aToken->type       = 0;
  aToken->precedence = 0;
	aToken->value      = 0;

  free((void*)aToken);
}

/*
  ensures ???
 */
void freeAllTokenObjs(TokenObj *aToken) {
	if (!aToken) return;

	if (aToken->next)  freeAllTokenObjs(aToken->next);
	freeThisTokenObj(aToken);
}


#endif
