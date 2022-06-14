
#include <string.h>
#include <ctype.h>
#include <stdlib.h>

#include "xeus-calc/token.h"

char *operators    = "-+/*^()";
int   precedence[] = {10, 10, 20, 20, 30, 40, 40};

TokenObj *newTokenObj(const char* theToken, size_t tokenLen, int tokenType) {
  TokenObj *newTObj = (TokenObj*)calloc(sizeof(TokenObj), 1);
  newTObj->token    = strndup(theToken, tokenLen);
  newTObj->len      = tokenLen;
  newTObj->type     = tokenType;
  newTObj->value    = 0;
  if (tokenType == TOKEN_VAL) newTObj->value = atof(newTObj->token);
  return newTObj;
}

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

void freeAllTokenObjs(TokenObj *aToken) {
	if (!aToken) return;

	if (aToken->next)  freeAllTokenObjs(aToken->next);
	freeThisTokenObj(aToken);
}


