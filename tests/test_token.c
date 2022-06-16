#include <string.h>
#include "fcTest.h"
#include "xeus-calc/token.h"

static void testNewTokenObj(FCTestCase *tc, void*) {
  TokenObj *newTObj =  newTokenObj("aToken", strlen("aToken"), TOKEN_NIL);
  fcTestNotNull(tc, newTObj, "the new token obj should not be NULL", FALSE);
}

void addTokenTests(void) {
  fcAddTest(TRUE, "Tokens", "newTokenObj", testNewTokenObj, NULL, NULL, NULL);
}
