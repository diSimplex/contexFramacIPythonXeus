
#ifndef CALC_H
#define CALC_H

#include "xeus-calc/token.h"

#ifdef __cplusplus
extern "C" {
#endif

TokenObj *tokenized(
  const char  *expr,
  char       **errMsg
);

TokenObj *parsedRPN(
  TokenObj  *expTokens,
  TokenObj **pubListOut,
  char     **errMsg
);

double interpretedRPN(
  TokenObj  *rpnTokens,
  TokenObj **pubListOut,
  char     **errMsg
);

#ifdef __cplusplus
}
#endif

#endif