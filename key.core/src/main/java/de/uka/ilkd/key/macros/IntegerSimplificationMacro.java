/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.util.Set;

/**
 * This macro performs simplification of integers and terms with integers. It applies only
 * non-splitting simplification rules.
 *
 * @author Michael Kirsten
 *
 */
public class IntegerSimplificationMacro extends AbstractPropositionalExpansionMacro {

    @Override
    public String getName() {
        return "Integer Simplification";
    }

    @Override
    public String getCategory() {
        return "Simplification";
    }

    @Override
    public String getScriptCommandName() {
        return "simp-int";
    }

    @Override
    public String getDescription() {
        return "This macro performs simplification of integers and terms with integers.\n"
            + "It applies only non-splitting simplification rules.";
    }

    private static final Set<String> ADMITTED_RULES_SET = asSet("add_eq_back",
        "add_eq_back_2", "add_eq_back_2_fst_comm", "add_eq_back_3", "add_less_back",
        "add_less_back_zero_1", "add_less_back_zero_1_comm", "add_less_back_zero_2",
        "add_less_back_zero_2_comm", "add_literals", "add_sub_elim_left", "add_sub_elim_right",
        "add_zero_left", "add_zero_right", "binaryAndOne", "binaryAndZeroLeft",
        "binaryAndZeroRight", "binaryOrNeutralLeft", "binaryOrNeutralRight",
        "bprod_lower_equals_upper", "bprod_one", "bprod_zero", "bsum_lower_equals_upper",
        "bsum_zero", "castDel", "castDel2", "castDel3",
        // "castedGetAny",
        "div_literals", "double_unary_minus_literal", "equal_literals", "greater_literals",
        "i_minus_i_is_zero", "inChar", "inByte", "inInt", "inLong", "inShort", "le1_add1_eq_le",
        "leq_diff1_eq", "leq_diff_1", "leq_literals", "less_base", "less_literals", "lt_diff_1",
        "lt_to_leq_1", "lt_to_leq_2", "minus_distribute_1", "minus_distribute_2",
        "moduloByteIsInByte", "moduloCharIsInChar", "moduloIntIsInInt", "moduloLongIsInLong",
        "moduloShortIsInShort", "mul_literals", "neg_literal", "polySimp_addAssoc",
        "polySimp_addLiterals", "polySimp_elimOne", "polySimp_elimOneLeft0", "polySimp_mulAssoc",
        "polySimp_mulLiterals", "pow_literals", "precOfInt", "precOfIntPair", "precOfPairInt",
        "prod_empty", "prod_one", "qeq_literals", "square_nonneg", "sub", "sub_literals",
        "sub_sub_elim", "sub_zero_1", "sub_zero_2", "sum_empty", "sum_zero", "times_minus_one_1",
        "times_minus_one_2", "times_one_1", "times_one_2", "times_zero_1", "times_zero_2",
        "translateJavaAddInt", "translateJavaAddLong", "translateJavaCastByte",
        "translateJavaCastChar", "translateJavaCastInt", "translateJavaCastLong",
        "translateJavaCastShort", "translateJavaDivInt", "translateJavaDivLong", "translateJavaMod",
        "translateJavaMulInt", "translateJavaMulLong", "translateJavaSubInt",
        "translateJavaSubLong", "translateJavaUnaryMinusInt", "translateJavaUnaryMinusLong");

    @Override
    protected Set<String> getAdmittedRuleNames() {
        return ADMITTED_RULES_SET;
    }

    @Override
    protected boolean allowOSS() {
        return true;
    }
}
