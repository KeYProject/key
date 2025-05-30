/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.util.HashSet;
import java.util.Set;

import org.key_project.prover.proof.rulefilter.RuleFilter;
import org.key_project.prover.rules.Rule;

/**
 * @author mihai
 *
 */
public final class SemanticsBlastingMacro extends AbstractBlastingMacro {


    private final SemanticsRuleFilter semanticsFilter;
    private final EqualityRuleFilter equalityRuleFilter;
    private final HashSet<String> allowedPullOut;

    public SemanticsBlastingMacro() {
        super();
        semanticsFilter = new SemanticsRuleFilter();
        equalityRuleFilter = new EqualityRuleFilter();
        allowedPullOut = new HashSet<>(20);

        allowedPullOut.add("store");
        allowedPullOut.add("create");
        allowedPullOut.add("anon");
        allowedPullOut.add("memset");
        allowedPullOut.add("empty");
        allowedPullOut.add("allLocs");
        allowedPullOut.add("singleton");
        allowedPullOut.add("union");
        allowedPullOut.add("intersect");
        allowedPullOut.add("setMinus");
        allowedPullOut.add("allFields");
        allowedPullOut.add("allObjects");
        allowedPullOut.add("arrayRange");
        allowedPullOut.add("freshLocs");
        allowedPullOut.add("seqDef");
        allowedPullOut.add("seqReverse");
        allowedPullOut.add("seqSub");
        allowedPullOut.add("seqConcat");
        allowedPullOut.add("seqSingleton");
        allowedPullOut.add("infiniteUnion");
    }

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
    public String getCategory() {
        return null;
    }

    @Override
    public String getDescription() {
        // TODO Auto-generated method stub
        return "Semantics Blasting";
    }



    private static class SemanticsRuleFilter implements RuleFilter {
        protected final HashSet<String> allowedRulesNames;
        {
            allowedRulesNames = new HashSet<>(100);
            allowedRulesNames.add("selectOfStore");
            allowedRulesNames.add("selectOfCreate");
            allowedRulesNames.add("selectOfAnon");
            allowedRulesNames.add("selectOfMemset");

            allowedRulesNames.add("elementOfEmpty");
            allowedRulesNames.add("elementOfAllLocs");
            allowedRulesNames.add("elementOfSingleton");
            allowedRulesNames.add("elementOfUnion");
            allowedRulesNames.add("elementOfIntersect");
            allowedRulesNames.add("elementOfSetMinus");
            allowedRulesNames.add("elementOfAllFields");
            allowedRulesNames.add("elementOfAllObjects");
            allowedRulesNames.add("elementOfArrayRange");
            allowedRulesNames.add("elementOfFreshLocs");
            allowedRulesNames.add("elementOfInfiniteUnion");
            allowedRulesNames.add("subsetToElementOf");
            allowedRulesNames.add("disjointToElementOf");
            allowedRulesNames.add("createdInHeapToElementOf");



            allowedRulesNames.add("getOfSeqDef");
            allowedRulesNames.add("getOfSeqSingleton");
            allowedRulesNames.add("getOfSeqConcat");
            allowedRulesNames.add("getOfSeqSub");
            allowedRulesNames.add("getOfSeqReverse");
            allowedRulesNames.add("lenOfSeqDef");
            allowedRulesNames.add("lenOfSeqSingleton");
            allowedRulesNames.add("lenOfSeqConcat");
            allowedRulesNames.add("lenOfSeqSub");
            allowedRulesNames.add("lenOfSeqReverse");

            // some int rules
            allowedRulesNames.add("inByte");
            allowedRulesNames.add("inChar");
            allowedRulesNames.add("inShort");
            allowedRulesNames.add("inInt");
            allowedRulesNames.add("inLong");
            allowedRulesNames.add("translateJavaUnaryMinusInt");
            allowedRulesNames.add("translateJavaUnaryMinusLong");
            allowedRulesNames.add("translateJavaAddInt");
            allowedRulesNames.add("translateJavaAddLong");
            allowedRulesNames.add("translateJavaSubInt");
            allowedRulesNames.add("translateJavaSubLong");
            allowedRulesNames.add("translateJavaMulInt");
            allowedRulesNames.add("translateJavaMulLong");
            allowedRulesNames.add("translateJavaMod");
            allowedRulesNames.add("translateJavaDivInt");
            allowedRulesNames.add("translateJavaDivLong");
            allowedRulesNames.add("translateJavaCastByte");
            allowedRulesNames.add("translateJavaCastShort");
            allowedRulesNames.add("translateJavaCastInt");
            allowedRulesNames.add("translateJavaCastLong");
            allowedRulesNames.add("translateJavaCastChar");
            allowedRulesNames.add("jdiv_axiom_inline");

            // other rules
            allowedRulesNames.add("array_store_known_dynamic_array_type");
            // non null
            allowedRulesNames.add("nonNull");
            allowedRulesNames.add("nonNullZero");
            allowedRulesNames.add("sub_literals");
            allowedRulesNames.add("equal_literals");
            // allowedRulesNames.add("applyEq");
        }

        @Override
        public boolean filter(Rule rule) {
            return allowedRulesNames.contains(rule.name().toString());
        }
    }

    private static class EqualityRuleFilter implements RuleFilter {
        private final HashSet<String> allowedRulesNames;
        {
            allowedRulesNames = new HashSet<>();
            allowedRulesNames.add("equalityToElementOf");
            allowedRulesNames.add("equalityToSelect");
            allowedRulesNames.add("equalityToSeqGetAndSeqLen");
        }

        @Override
        public boolean filter(Rule rule) {
            return allowedRulesNames.contains(rule.name().toString());
        }
    }



}
