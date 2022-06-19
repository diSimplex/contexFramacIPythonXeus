#include <stdio.h>

#include "fcTest.h"

void addTokenTests(void);

int main(int argc, const char *argv[]) {

  addTokenTests();

  return fcTestRunner(argc, argv);
}

#ifdef __FRAMAC__

int evaMain(void) {
  char *argv[3];
  argv[0] = "evaMain";
  argv[1] = "Tokens";
  argv[2] = NULL;

  return main(2, argv);
}

#endif