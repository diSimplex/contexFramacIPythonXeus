#include <stdlib.h>
#include "ctest.h"

CTEST(suite1, test1) {
	ASSERT_EQUAL(1,1);
}

CTEST(suite1, test2) {
	ASSERT_EQUAL(1,3);
}
