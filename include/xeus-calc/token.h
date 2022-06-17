
#ifndef TOKEN_H
#define TOKEN_H


#ifdef __cplusplus
extern "C" {
#endif

// We will implement trees/linked-lists as well as stacks using "tokens"
// on the heap. To do this we will have a standard token structure:

#define TOKEN_NIL 0
#define TOKEN_OP  1
#define TOKEN_VAL 2

extern char *operators;

typedef struct tokenObjStruct {
  int                    type;
  const char            *token;
  size_t                 len;
  double                 value;
  int                    precedence;
  struct tokenObjStruct *next;
} TokenObj;

TokenObj *newTokenObj(
  const char* theToken, size_t tokenLen,
  int tokenType
);

void updatePrecedence(TokenObj *theToken);

char *publishPubList(TokenObj *aPubList);

void freeThisTokenObj(TokenObj *aToken);

void freeAllTokenObjs(TokenObj *aToken);

#ifdef __cplusplus
}
#endif

#endif