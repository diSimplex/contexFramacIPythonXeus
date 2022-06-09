
#include <string.h>
#include <ctype.h>
#include <stdlib.h>
char operators[] = "-+/*^()";

// at the moment this interpreter is architected to pass strings between
// stages.... we will re-architect this to pass a linked list of tokens.

// we return non-zero if there was an error...
// the spaced_expression if non-NULL should be free'd by the receiver.
// the errMsg if non-NULL should be free'd by the receiver.
//
int spaced_expr(
  const char* exp,
  char** spaced_expression,
  char** errMsg
) {
  size_t expLen = strlen(exp);
  if (*errMsg) free(*errMsg);
  *errMsg = NULL;
  if (*spaced_expression) free(*spaced_expression);
  *spaced_expression = calloc(expLen*3, sizeof(char));
  char* spacedExp = *spaced_expression;
  const char* expEnd = exp + expLen;
  const char* lastItr = NULL;
  for (const char* itr = exp; itr < expEnd ; lastItr = itr, itr++ ) {
    char* op = strchr(operators, *itr);
    if (op) {
      *spacedExp =  ' '; spacedExp++;
      *spacedExp = *itr; spacedExp++;
      *spacedExp =  ' '; spacedExp++;
    } else if (isdigit(*itr) ||
      (lastItr && isdigit(*lastItr) && *itr == '.')) {
      *spacedExp = *itr; spacedExp++;
    } else if (*itr == ' ') {
      continue;
    } else {
      char* anErrMsg = strdup("Syntax error :\none of the characters presents an issue : [ ]");
      anErrMsg[strlen(anErrMsg) - 2] = *itr;
      *errMsg = anErrMsg;
      if (*spaced_expression) free(*spaced_expression);
      *spaced_expression = NULL;
      return 1;
    }
  }
  return 0;
}

////////////////////////////////////////////////////////////////////////

char[] precedenceOps  = "+-*/^";
int[]  precedenceVals = {0, 0, 10, 10, 20};

std::string parse_rpn(
  const std::string& formated_expression,
  publish_type publish
) {
  std::stringstream input(formated_expression);
  std::string token;
  std::stringstream output_queue;
  std::stack<std::string> operators_stack;
  static precedence_map_type precedence_map = build_precedence_map();
  int parenthesis_counter = 0;
  while (input >> token) {
    char first_token_char = token[0];
    auto it = precedence_map.find(token);
    if (std::isdigit(first_token_char)) {
      output_queue << token << ' ';
    } else if (it != precedence_map.end()) {
      while (!operators_stack.empty() && operators_stack.top() != "(") {
        auto stack_it = precedence_map.find(operators_stack.top());
        if (stack_it->second >= it->second) {
          output_queue << operators_stack.top() << ' ';
          operators_stack.pop();
        } else {
          break;
        }
      }
      operators_stack.push(token);
    } else if (first_token_char == '(') {
      operators_stack.push(token);
      ++parenthesis_counter;
    } else if (first_token_char == ')') {
      while (!operators_stack.empty() && operators_stack.top() != "(") {
        output_queue << operators_stack.top() << ' ';
        operators_stack.pop();
      }
      if (operators_stack.empty()) {
        throw std::runtime_error("Syntax error:\nmissing or misplaced parenthesis");
      } else {
        --parenthesis_counter;
        operators_stack.pop();
      }
    }
  }
  while (!operators_stack.empty()) {
    if (parenthesis_counter == 0) {
      output_queue << operators_stack.top() << ' ';
      operators_stack.pop();
    } else {
      throw std::runtime_error("Syntax error:\nmissing or misplaced parenthesis");
    }
  }
  std::string result = "RPN = ";
  result += output_queue.str();
  publish("stdout", result);
  return output_queue.str();
}

/////////////////////////////////////////////////////////////////////

using operators_map_type = std::map<std::string, std::function<double(double first_argument, double second_argument)>>;

operators_map_type build_operators_map()
{
    operators_map_type operators_map;
    operators_map["+"] = std::plus<double>();
    operators_map["-"] = std::minus<double>();
    operators_map["*"] = std::multiplies<double>();
    operators_map["/"] = std::divides<double>();
    operators_map["^"] = [](double first_argument, double second_argument) {
        return std::pow(first_argument, second_argument);
    };

    return operators_map;
}

double compute_rpn(
  const std::string& rpn_expression,
  publish_type publish
) {
  publish("stdout", "\nInput\tOperation\tStack after\n");
  std::istringstream input(rpn_expression);
  std::vector<double> evaluation;
  std::string token;
  // the map is initialized only once
  static operators_map_type operators_map = build_operators_map();
  while (input >> token) {
    publish("stdout", token + "\t");
    double token_num;
    if (std::istringstream(token) >> token_num) {
      publish("stdout", "Push\t\t");
      evaluation.push_back(token_num);
    } else {
      // if less than 2 entries in the stack -> missing operand
      if (evaluation.size() >= 2) {
        publish("stdout", "Operate\t\t");
        auto it = operators_map.find(token);
        if (it != operators_map.end()) {
          double second_argument = evaluation.back();
          evaluation.pop_back();
          double first_argument = evaluation.back();
          evaluation.pop_back();
          evaluation.push_back((it->second)(first_argument, second_argument));
        } else {
          throw std::runtime_error("\nSyntax error:\noperator or function not recognized");
        }
      } else {
        throw std::runtime_error("\nSyntax error:\nmissing operand");
      }
    }
    std::stringstream result;
    std::copy(evaluation.begin(), evaluation.end(), std::ostream_iterator<double>(result, " "));
    publish("stdout", result.str() + "\n");
  }
  return evaluation.back();
}

