#include <string.h>
#include "fcTest.h"
#include "xeus-calc/token.h"

static void testNewTokenObj(FCTestCase *tc, void*) {
  TokenObj *nilTObj =  newTokenObj("aToken", strlen("aToken"), TOKEN_NIL);
  fcTestNotNull(tc, nilTObj, "the nil token obj should not be NULL", FALSE);

  TokenObj *opTObj =  newTokenObj("+", strlen("+"), TOKEN_OP);
  fcTestNotNull(tc, opTObj, "the op token obj should not be NULL", FALSE);

  TokenObj *valTObj = newTokenObj("10.2", strlen("10.2"), TOKEN_VAL);
  fcTestNotNull(tc, valTObj, "the val token obj should not be NULL", FALSE);

  TokenObj *longTObj = newTokenObj("token token1", strlen("token"), TOKEN_NIL);
  fcTestNotNull(tc, longTObj, "the long token obj should not be NULL", FALSE);
}

void addTokenTests(void) {
  fcAddTest(TRUE, "Tokens", "newTokenObj", testNewTokenObj, NULL, NULL, NULL);
}
