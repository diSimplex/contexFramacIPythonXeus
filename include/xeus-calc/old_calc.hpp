/***************************************************************************
* Copyright (c) 2019, Sylvain Corlay, Johan Mabille, Wolf Vollprecht       *
* Copyright (c) 2019, QuantStack                                           *
*                                                                          *
* Distributed under the terms of the BSD 3-Clause License.                 *
*                                                                          *
* The full license is in the file LICENSE, distributed with this software. *
****************************************************************************/

#ifndef OLD_CALC_HPP
#define OLD_CALC_HPP

#include "xeus/xinterpreter.hpp"

#include "nlohmann/json.hpp"

#include "xeus_calc_config.hpp"

using publish_type = std::function<void(const std::string& name, const std::string& text)>;

XEUS_CALC_API std::string parse_rpn(const std::string& infix, publish_type publish = [](const std::string& /*name*/, const std::string& /*text*/){});

XEUS_CALC_API double compute_rpn(const std::string &expr, publish_type publish = [](const std::string& /*name*/, const std::string& /*text*/){});

#endif
