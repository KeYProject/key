/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.merge.CloseAfterMergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.smt.SMTRuleApp;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstSeq;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.sequent.PosInOccurrence;

/**
 * Utilities for working with rule applications.
 *
 * @author Arne Keller
 */
public final class RuleAppUtil {
    private RuleAppUtil() {

    }

    /**
     * Compute the sequent formulas used by the provided rule application (if-instantiations):
     *
     * @param ruleApp the rule application
     * @param node proof node which contains that rule application
     * @return sequent formulas used
     */
    public static Set<PosInOccurrence> assumesInstantiationsOfRuleApp(
            RuleApp ruleApp, Node node) {
        // replayer requires that assumesFormulaInstantiations are provided in order (!)
        Set<PosInOccurrence> inputs = new LinkedHashSet<>();
        // taclets with \find or similar
        if (ruleApp instanceof PosTacletApp posTacletApp) {

            if (posTacletApp.assumesFormulaInstantiations() != null) {
                for (AssumesFormulaInstantiation x : posTacletApp.assumesFormulaInstantiations()) {

                    if (x instanceof AssumesFormulaInstSeq assumes) {
                        boolean antec = assumes.inAntecedent();
                        inputs.add(new PosInOccurrence(assumes.getSequentFormula(),
                            PosInTerm.getTopLevel(), antec));
                    }
                }
            }
        }
        // built-ins need special treatment:
        // record if instantiations
        if (ruleApp instanceof AbstractBuiltInRuleApp builtIn) {
            builtIn.assumesInsts().forEach(inputs::add);
        }

        // State Merging: add all formulas as inputs
        // TODO: this is not enough, as the State Merge processes every formula in the sequent
        // (-> if more formulas are present after slicing, a different result will be produced!)

        // SMT application: add all formulas as inputs
        if (ruleApp instanceof MergeRuleBuiltInRuleApp
                || ruleApp instanceof CloseAfterMergeRuleBuiltInRuleApp
                || ruleApp instanceof SMTRuleApp) {
            node.sequent().antecedent().iterator().forEachRemaining(
                it -> inputs.add(new PosInOccurrence(it, PosInTerm.getTopLevel(), true)));
            node.sequent().succedent().iterator().forEachRemaining(
                it -> inputs.add(new PosInOccurrence(it, PosInTerm.getTopLevel(), false)));
        }
        return inputs;
    }
}
