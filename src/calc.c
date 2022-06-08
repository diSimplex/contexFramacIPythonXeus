
#include <string.h>
#include <ctype.h>

char operators[] = "-+/*^()";

char* formated_expr(const char* expression, char* spaced_expression) {
  char* expressionEnd = expression + strlen(expression);
  char* lastItr = NULL;
  for (char* itr = expression; itr < expressionEnd ; lastItr = itr, itr++ ) {
    char* op = strchr(operators, *itr);
    if (op) {
      *spaced_expression =  ' '; spaced_expression++;
      *spaced_expression = *itr; spaced_expression++;
      *spaced_expression =  ' '; spaced_expression++;
    } else if (isdigit(*itr) ||
      (lastItr && isdigit(*lastItr) && *itr == '.')) {
      *spaced_expression = *itr; spaced_expression++;
    } else if (*itr == ' ') {
      continue;
    } else {
      char errMsg[] = "Syntax error :\none of the characters presents an issue :  ";
      errMsg[strlen(errMsg)-1] = *itr;
      return strdup(errMsg);
    }
  }
  return NULL;
}
