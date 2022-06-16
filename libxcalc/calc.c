
#include <string.h>
#include <ctype.h>
#include <stdlib.h>
#include <stdio.h>
#include <math.h>

#include "xeus-calc/token.h"

TokenObj *tokenized(
  const char  *exp,
  char       **errMsg
) {
  size_t expLen = strlen(exp);
  const char *expEnd       = exp + expLen;
  const char *lastItr      = NULL;
  const char *lastValue    = NULL;
  size_t      lastValueLen = 0;
  TokenObj   *tListRoot    = newTokenObj("", 0, TOKEN_NIL);
  TokenObj   *tList        = tListRoot;

  for (const char* itr = exp; itr < expEnd ; lastItr = itr, itr++ ) {
    char* op = strchr(operators, *itr);

    if (op || *itr == ' ') {
      if (lastValue && (0 < lastValueLen) ) {
        tList->next = newTokenObj(lastValue, lastValueLen, TOKEN_VAL);
        tList       = tList->next;
      }
      lastValue    = NULL;
      lastValueLen = 0;
    }

    if (op) {
      tList->next = newTokenObj(itr, 1, TOKEN_OP);
      updatePrecedence(tList->next);
      tList       = tList->next;
    } else if (isdigit(*itr) ||
      (lastItr && isdigit(*lastItr) && *itr == '.')) {
      if (!lastValue) lastValue = itr;
      lastValueLen++;
    } else if (*itr == ' ') {
      continue;
    } else {
      char* anErrMsg = strdup("Syntax error :\none of the characters presents an issue : [ ]");
      anErrMsg[strlen(anErrMsg) - 2] = *itr;
      *errMsg = anErrMsg;
      return NULL;
    }
  }
  TokenObj *result = tListRoot->next;
  freeThisTokenObj(tListRoot);
  return result;
}

/////////////////////////////////////////////////////////////////////

#define publish(...)                         \
  snprintf(publishBuffer, 250, __VA_ARGS__); \
  pubList->next = newTokenObj(               \
    strdup(publishBuffer),                   \
    strlen(publishBuffer),                   \
    TOKEN_NIL                                \
  );                                         \
  pubList       = pubList->next;

////////////////////////////////////////////////////////////////////////

TokenObj *parsedRPN(
  TokenObj  *expTokens,
  TokenObj **pubListOut,
  char     **errMsg
) {
  char publishBuffer[260];
  if (*pubListOut) freeAllTokenObjs(*pubListOut);
  *pubListOut = NULL;

  TokenObj *pubListRoot = newTokenObj("", 0, TOKEN_NIL);
  TokenObj *pubList = pubListRoot;
  publish("RPN = ");

  int numParenthesis    = 0;
  TokenObj *rpnListRoot = newTokenObj("", 0, TOKEN_NIL);
  TokenObj *rpnList     = rpnListRoot;
  TokenObj *opListRoot  = NULL;

  if (!expTokens) return NULL;

  TokenObj *nextToken   = expTokens->next;

  while (nextToken) {

    if (nextToken->type == TOKEN_VAL) {
      publish("%s ", nextToken->token);
      rpnList->next = nextToken;
      rpnList       = rpnList->next;
      nextToken     = nextToken->next;
    } else if (nextToken->type == TOKEN_OP) {
      if (opListRoot->precedence < nextToken->precedence) {
        TokenObj *nextNextToken = nextToken->next;
        nextToken->next         = opListRoot;
        opListRoot              = nextToken;
        nextToken               = nextNextToken;
      } else {
        while(opListRoot) {
          if (strcmp(opListRoot->token, "(") != 0) {
            opListRoot = opListRoot->next;
            numParenthesis++;
          } else if (strcmp(opListRoot->token, ")") != 0) {
            numParenthesis--;
            if (numParenthesis < 0) {
            	*errMsg = strdup("Syntax error:\nmissing or misplaced parenthesis (too few opening '(' found)");
            	return NULL;
            }
          } else {
            publish("%s ", opListRoot->token);
        	  rpnList->next = opListRoot;
        	  rpnList       = rpnList->next;
        	  opListRoot    = opListRoot->next;
        	}
        }
        opListRoot = nextToken;
        nextToken  = nextToken->next;
      }
    }
  }

  if (opListRoot) {
  	*errMsg = strdup("Syntax error:\nmissing or misplaced parenthesis (no closing ')' found)");
   	return NULL;
  }

  TokenObj *result = rpnListRoot->next;
  freeThisTokenObj(rpnListRoot);
  *pubListOut = pubListRoot;
  return result;
}

/////////////////////////////////////////////////////////////////////

#define popTo(aVal) {                      \
  if (0 < dataLen) {                       \
	  dataLen--;                             \
	  aVal = dataStack[dataLen];             \
	} else {                                 \
		*errMsg = strdup("Empty data stack!"); \
		return 0;                              \
	}                                        \
}

#define pushFrom(aVal) {                      \
  if (dataLen < 250) {                        \
  	dataStack[dataLen] = aVal;                \
   dataLen++;                                 \
  } else {                                    \
   *errMsg = strdup("Data stack too small!"); \
   return 0;                                  \
  }                                           \
}

double interpretedRPN(
  TokenObj  *rpnTokens,
  TokenObj **pubListOut,
  char     **errMsg
) {
  char publishBuffer[260];
  if (*pubListOut) freeAllTokenObjs(*pubListOut);
  *pubListOut = NULL;

  TokenObj *pubListRoot = newTokenObj("", 0, TOKEN_NIL);
  TokenObj *pubList = pubListRoot;
  publish("\nInput\tOperation\tStack after\n")

  double dataStack[250];
  int    dataLen = 0;

  TokenObj *nextToken = rpnTokens;

  while (nextToken) {
    publish("%s\t", nextToken->token);
    if (nextToken->type == TOKEN_VAL) {
      publish("Push\t\t");
      pushFrom(nextToken->value);
      TokenObj *oldToken = nextToken;
    	nextToken          = nextToken->next;
    	freeThisTokenObj(oldToken);
    } else if (nextToken->type == TOKEN_OP) {
      double rhs;
      popTo(rhs);
      double lhs;
      popTo(lhs);
      publish("Operate\t\t")
      switch(*(nextToken->token)) {
    	  case '+' : pushFrom(lhs+rhs); break;
    	  case '-' : pushFrom(lhs-rhs); break;
    	  case '*' : pushFrom(lhs*rhs); break;
    	  case '/' : pushFrom(lhs/rhs); break;
        case '^' : pushFrom(pow(lhs,rhs)); break;
        default  :
          *errMsg = strdup("Unknown operator!");
          return 0;
      }
    }
    publish("%f\n", dataStack[dataLen-1]);
  }
  if (dataLen != 1) {
    *errMsg = strdup("Unbalanced RPN expression!");
    return 0;
  }
  *pubListOut = pubListRoot;
  return dataStack[0];
}
