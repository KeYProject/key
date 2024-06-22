/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.macros;

import java.util.Set;

import de.uka.ilkd.key.macros.AbstractBlastingMacro;
import de.uka.ilkd.key.proof.rulefilter.RuleFilter;
import de.uka.ilkd.key.rule.Rule;

import org.jspecify.annotations.Nullable;

/**
 * @author mihai
 */
public final class SemanticsBlastingMacro extends AbstractBlastingMacro {
    private static final Set<String> EMPTY_RULES = Set.of(
        "equalityToElementOf", "equalityToSelect", "equalityToSeqGetAndSeqLen");

    private static final Set<String> SEMANTIC_RULES = Set.of(
        "selectOfStore",
        "selectOfCreate",
        "selectOfAnon",
        "selectOfMemset",

        "elementOfEmpty",
        "elementOfAllLocs",
        "elementOfSingleton",
        "elementOfUnion",
        "elementOfIntersect",
        "elementOfSetMinus",
        "elementOfAllFields",
        "elementOfAllObjects",
        "elementOfArrayRange",
        "elementOfFreshLocs",
        "elementOfInfiniteUnion",
        "subsetToElementOf",
        "disjointToElementOf",
        "createdInHeapToElementOf",


        "getOfSeqDef",
        "getOfSeqSingleton",
        "getOfSeqConcat",
        "getOfSeqSub",
        "getOfSeqReverse",
        "lenOfSeqDef",
        "lenOfSeqSingleton",
        "lenOfSeqConcat",
        "lenOfSeqSub",
        "lenOfSeqReverse",

        // some int rules
        "inByte",
        "inChar",
        "inShort",
        "inInt",
        "inLong",
        "translateJavaUnaryMinusInt",
        "translateJavaUnaryMinusLong",
        "translateJavaAddInt",
        "translateJavaAddLong",
        "translateJavaSubInt",
        "translateJavaSubLong",
        "translateJavaMulInt",
        "translateJavaMulLong",
        "translateJavaMod",
        "translateJavaDivInt",
        "translateJavaDivLong",
        "translateJavaCastByte",
        "translateJavaCastShort",
        "translateJavaCastInt",
        "translateJavaCastLong",
        "translateJavaCastChar",
        "jdiv_axiom_inline",

        // other rules
        "array_store_known_dynamic_array_type",
        // non null
        "nonNull",
        "nonNullZero",
        "sub_literals",
        "equal_literals"
    // "applyEq",
    );

    private final NameRuleFilter semanticsFilter = new NameRuleFilter(SEMANTIC_RULES);
    private final NameRuleFilter equalityRuleFilter = new NameRuleFilter(EMPTY_RULES);
    private final Set<String> allowedPullOut =
        Set.of("store", "create", "anon", "memset", "empty", "allLocs", "singleton", "union",
            "intersect", "setMinus", "allFields", "allObjects", "arrayRange", "freshLocs", "seqDef",
            "seqReverse", "seqSub", "seqConcat", "seqSingleton", "infiniteUnion");

    @Override
    protected RuleFilter getSemanticsRuleFilter() {
        return semanticsFilter;
    }

    @Override
    protected RuleFilter getEqualityRuleFilter() {
        return equalityRuleFilter;
    }

    @Override
    protected Set<String> getAllowedPullOut() {
        return allowedPullOut;
    }

    @Override
    public String getName() {
        return "Semantics Blasting";
    }

    @Override
    @Nullable
    public String getCategory() {
        return null;
    }

    @Override
    public String getDescription() {
        return "Semantics Blasting";
    }


    private record NameRuleFilter(Set<String> rules) implements RuleFilter {

    @Override
    public boolean filter(Rule rule) {
        return rules.contains(rule.name().toString());
    }
}}
