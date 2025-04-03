/* Test Pass
        Jeff Yau, Seneca Polytechnic College
        Student ID :142466234
        Modelled on tree-nrv.cc and tree-ctyler.cc by Chris Tyler, Seneca Polytechnic College, 2024-11

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

GCC is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

#include <map>
#include <vector>
#include <string>
#include <stdlib.h>
#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "backend.h"
#include "tree.h"
#include "gimple.h"
#include "tree-pass.h"
#include "ssa.h"
#include "tree-pretty-print.h"
#include "gimple-iterator.h"
#include "gimple-walk.h"
#include "internal-fn.h"
#include "gimple-pretty-print.h"
#include "cgraph.h"
#include "gimple-ssa.h"
#include "attribs.h"
#include "pretty-print.h"
#include "tree-inline.h"
#include "intl.h"
#include "function.h"
#include "basic-block.h"
#include "gcc-plugin.h"

namespace {
const pass_data pass_data_jeff =
{
  GIMPLE_PASS, /* type */
  "jeff", /* name */
  OPTGROUP_NONE, /* optinfo_flags */
  TV_NONE, /* tv_id */
  PROP_cfg, /* properties_required */
  0, /* properties_provided */
  0, /* properties_destroyed */
  0, /* todo_flags_start */
  0, /* todo_flags_finish */
};

class pass_jeff : public gimple_opt_pass
{
public:
  pass_jeff (gcc::context *ctxt)
    : gimple_opt_pass (pass_data_jeff, ctxt)
  {}

  /* opt_pass methods: */
  bool gate (function *) final override { return 1; }

  unsigned int execute (function *) final override;

}; // class pass_jeff


int process_gimple_variables(std::map<tree, int>& refMap, int index, gimple* stmt, std::map<int, int>& resultMap) {
    std::vector<tree> vars;

    switch (gimple_code(stmt)) {
        case GIMPLE_ASSIGN: {
            tree lhs = gimple_assign_lhs(stmt);
            vars.push_back(lhs);

            int rhs_ops = gimple_num_ops(stmt) - 1;
            for (int i = 1; i <= rhs_ops; ++i) {
                tree op = gimple_op(stmt, i);
                vars.push_back(op);
            }
            break;
        }

        case GIMPLE_DEBUG_BIND: {
            tree var = gimple_debug_bind_get_var(stmt);
            tree val = gimple_debug_bind_get_value(stmt);
            if (var)
                vars.push_back(var);
            if (val)
                vars.push_back(val);
            break;
        }

        case GIMPLE_COND: {
            tree lhs = gimple_cond_lhs(stmt);
            tree rhs = gimple_cond_rhs(stmt);
            if (lhs)
                vars.push_back(lhs);
            if (rhs)
                vars.push_back(rhs);
            break;
        }
        default:
            break;
    }

    for (tree var : vars) {
        std::map<tree, int>::iterator it = refMap.find(var);
        if (it != refMap.end()) {
            resultMap[index] = it->second;
        } else {
            refMap[var] = index;
            resultMap[index] = index;
        }
        ++index;
    }

    return index;
}

unsigned int pass_jeff::execute(function *func)
{
        static std::string base_function;
        static int var1_bb_count = 0;
        static int var1_stmt_count = 0;
        static std::vector<enum gimple_code> var1_gimple_code;
        static std::vector<unsigned> var1_operands_count;
        static std::vector<enum tree_code> var1_operandsType;
        static std::map<int,int> var1_variableMap;
        struct cgraph_node *node;
        if (!dump_file ||!func || !func ->cfg)
                return 0;

        FOR_EACH_FUNCTION_WITH_GIMPLE_BODY(node)
        {
                if (!base_function.empty())
                    break;     //resolver already found

                function *fun =node->get_fun();
                if (!fun)
                    continue;  //ignore no function with no body

                const char *fname = node->name();
                if (!fname)
                    continue;   //ignore function with no name

                std::string name(fname);

                if (base_function.empty() && name.find(".resolver") != std::string::npos)
                {
                    base_function = name.substr(0, name.find(".resolver"));
                    fprintf(dump_file, "Found base function: %s\n", base_function.c_str());
                    break;       //resolver found
                }

        }
        node = cgraph_node::get(func->decl);
        if (!node){
                fprintf(dump_file, "ERROR: cgraph_node::get(func->decl)\n");
        }
        const char *fname = node->name();
        std::string name(fname);
        if (name.find(base_function) != 0 || name.find(".resolver") !=std::string::npos)
                return 0;

        int bb_count = 0;
        int stmt_count = 0;
        basic_block bb;
        int index = 0;
        std::map<tree,int> refMap;
        FOR_EACH_BB_FN(bb, func)
        {
                bb_count++;
                for (gimple_stmt_iterator gsi = gsi_start_bb(bb); !gsi_end_p(gsi); gsi_next(&gsi)){
                        stmt_count++;
                }
        }

        if (var1_bb_count == 0 && var1_stmt_count == 0)
        {
                var1_bb_count = bb_count;
                var1_stmt_count = stmt_count;
                FOR_EACH_BB_FN(bb,func){
                        for (gimple_stmt_iterator gsi = gsi_start_bb(bb); !gsi_end_p(gsi); gsi_next(&gsi)){
                                index = process_gimple_variables(refMap, index, gsi_stmt(gsi), var1_variableMap);
                                var1_gimple_code.push_back(gimple_code(gsi_stmt(gsi)));
                                var1_operands_count.push_back(gimple_num_ops(gsi_stmt(gsi)));
                                if (is_gimple_assign(gsi_stmt(gsi)))
                                        var1_operandsType.push_back(gimple_assign_rhs_code(gsi_stmt(gsi)));
                        }
                }
        }
        else
        {
                if (bb_count != var1_bb_count || stmt_count != var1_stmt_count){
                        fprintf(dump_file, " NOPRUNE: %s\n",base_function.c_str());
                        return 0;
                }
                std::vector<enum gimple_code>::iterator it = var1_gimple_code.begin();
                std::vector<unsigned>::iterator count_it = var1_operands_count.begin();
                std::vector<enum tree_code>::iterator optype_it = var1_operandsType.begin();
                std::map<int,int> var2_variableMap;
                index = 0;
                FOR_EACH_BB_FN(bb, func){
                        for (gimple_stmt_iterator gsi = gsi_start_bb(bb); !gsi_end_p(gsi); gsi_next(&gsi)){
                                index = process_gimple_variables(refMap, index, gsi_stmt(gsi), var2_variableMap);
                                if (gimple_code(gsi_stmt(gsi)) != *it
                                        ||gimple_num_ops(gsi_stmt(gsi))!= *count_it)
                                {
                                        fprintf(dump_file, " NOPRUNE: %s\n",base_function.c_str());
                                        return 0;
                                }
                                if( *it == GIMPLE_ASSIGN && *(optype_it++) != gimple_assign_rhs_code(gsi_stmt(gsi)))
                                {
                                        fprintf(dump_file, " NOPRUNE: %s\n",base_function.c_str());
                                        return 0;
                                }
                                ++it;
                                ++count_it;
                        }
                }
                std::map<int, int>::const_iterator it1 = var1_variableMap.begin();
                std::map<int, int>::const_iterator it2 = var2_variableMap.begin();

                while (it1 != var1_variableMap.end()) {
                        if (it1->first != it2->first || it1->second != it2->second)
                        {
                                fprintf(dump_file, " NOPRUNE: %s\n",base_function.c_str());
                                return 0;
                        }
                        ++it1;
                        ++it2;
                }
           fprintf(dump_file, " PRUNE: %s\n",base_function.c_str());

        }

    return 0;
}


} // anon namespace

gimple_opt_pass *
make_pass_jeff (gcc::context *ctxt)
{
  return new pass_jeff (ctxt);
}
