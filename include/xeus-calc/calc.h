
#ifndef CALC_H
#define CALC_H


#ifdef __cplusplus
extern "C" {
#endif

  int spaced_expr(
    const char* expr,
    char** spaced_expression,
    char** errMsg
  );

using publish_type = std::function<void(const std::string& name, const std::string& text)>;

XEUS_CALC_API std::string parse_rpn(
  const std::string& infix,
  publish_type publish = [](const std::string& /*name*/, const std::string& /*text*/){}
);

XEUS_CALC_API double compute_rpn(
  const std::string &expr,
  publish_type publish = [](const std::string& /*name*/, const std::string& /*text*/){}
);

#ifdef __cplusplus
}
#endif

#endif