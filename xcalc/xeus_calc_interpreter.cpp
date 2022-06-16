/***************************************************************************
* Copyright (c) 2019, Sylvain Corlay, Johan Mabille, Wolf Vollprecht       *
* Copyright (c) 2019, QuantStack                                           *
*                                                                          *
* Distributed under the terms of the BSD 3-Clause License.                 *
*                                                                          *
* The full license is in the file LICENSE, distributed with this software. *
****************************************************************************/

#include <iostream>
#include <vector>
#include <sstream>
#include <stack>
#include <cctype>

#include "xeus/xinterpreter.hpp"

#include "xeus-calc/xeus_calc_interpreter.hpp"
#include "xeus-calc/calc.h"

namespace xeus_calc
{
    void interpreter::configure_impl()
    {
    }

    nl::json interpreter::execute_request_impl(int execution_counter,
                                               const std::string& code,
                                               bool /*silent*/,
                                               bool /*store_history*/,
                                               nl::json /*user_expressions*/,
                                               bool /*allow_stdin*/)
    {
        // You can use the C-API of your target language for executing the code,
        // e.g. `PyRun_String` for the Python C-API
        //      `luaL_dostring` for the Lua C-API

        // Use this method for publishing the execution result to the client,
        // this method takes the ``execution_counter`` as first argument,
        // the data to publish (mime type data) as second argument and metadata
        // as third argument.
        // Replace "Hello World !!" by what you want to be displayed under the execution cell

        nl::json pub_data;
        std::string result = "Result = ";
        try
        {
            char     *errMsg    = NULL;
            TokenObj *tokenList = tokenized(code.c_str(), &errMsg);
            if (!tokenList) {
              if (!errMsg) errMsg = strdup("Unknown error from tokenizer");
            	throw std::runtime_error(errMsg);
            }
            TokenObj *pubList = NULL;
                      errMsg  = NULL;
            TokenObj *rpnList = parsedRPN(tokenList, &pubList, &errMsg);
            if (!rpnList) {
              if (!errMsg) errMsg = strdup("Unknown error from parse RPN");
            	throw std::runtime_error(errMsg);
            }
            char *pubStr = publishPubList(pubList);
            this->publish_stream("stdout", pubStr);
            if (pubStr) free(pubStr);
            freeAllTokenObjs(pubList);

            pubList = NULL;
            errMsg  = NULL;
            double resultVal = interpretedRPN(rpnList, &pubList, &errMsg);
            if (errMsg) {
            	throw std::runtime_error(errMsg);
            }

            result += std::to_string(resultVal);
            pub_data["text/plain"] = result;
            publish_execution_result(execution_counter, std::move(pub_data), nl::json::object());
            nl::json jresult;
            jresult["status"] = "ok";
            jresult["payload"] = nl::json::array();
            jresult["user_expressions"] = nl::json::object();
            return jresult;
        }
        catch (const std::runtime_error& err)
        {
            nl::json jresult;
            publish_stream("stderr", err.what());
            jresult["status"] = "error";
            return jresult;
        }
        // You can also use this method for publishing errors to the client, if the code
        // failed to execute
        // publish_execution_error(error_name, error_value, error_traceback);
        // publish_execution_error("TypeError", "123", {"!@#$", "*(*"});
    }

    nl::json interpreter::complete_request_impl(const std::string& /*code*/, int /*cursor_pos*/)
    {
        nl::json jresult;
        jresult["status"] = "ok";
        return jresult;
    };

    nl::json interpreter::inspect_request_impl(const std::string& /*code*/,
                                               int /*cursor_pos*/,
                                               int /*detail_level*/)
    {
        nl::json jresult;
        jresult["status"] = "ok";
        return jresult;
    };

    nl::json interpreter::is_complete_request_impl(const std::string& /*code*/)
    {
        nl::json jresult;
        jresult["status"] = "complete";
        return jresult;
    };

    nl::json interpreter::kernel_info_request_impl()
    {
        nl::json result;
        result["implementation"] = "xcalc";
        result["implementation_version"] = "0.1.0";
        std::string banner = ""
        " **     ** ******** **     **  ********         ******      **     **         ****** \n"
        "//**   ** /**///// /**    /** **//////         **////**    ****   /**        **////** \n"
        " //** **  /**      /**    /**/**              **    //    **//**  /**       **    // \n"
        "  //***   /******* /**    /**/********* *****/**         **  //** /**      /**       \n"
        "   **/**  /**////  /**    /**////////**///// /**        **********/**      /**       \n"
        "  ** //** /**      /**    /**       /**      //**    **/**//////**/**      //**    ** \n"
        " **   //**/********//*******  ********        //****** /**     /**/******** //****** \n"
        "//     // ////////  ///////  ////////          //////  //      // ////////   ////// \n"
        "\n"
        " Implementation of a calculator based on RPN through Xeus";
        result["banner"] = banner;
        result["language_info"]["name"] = "calc";
        result["language_info"]["version"] = "";
        result["language_info"]["mimetype"] = "";
        result["language_info"]["file_extension"] = "";
        return result;
    }

    void interpreter::shutdown_request_impl()
    {
    }
}
