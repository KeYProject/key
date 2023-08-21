/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.merge.CloseAfterMergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.smt.SMTRuleApp;

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
    public static Set<PosInOccurrence> ifInstsOfRuleApp(RuleApp ruleApp, Node node) {
        // replayer requires that ifInsts are provided in order (!)
        Set<PosInOccurrence> inputs = new LinkedHashSet<>();
        // taclets with \find or similar
        if (ruleApp instanceof PosTacletApp) {
            PosTacletApp posTacletApp = (PosTacletApp) ruleApp;

            if (posTacletApp.ifFormulaInstantiations() != null) {
                for (IfFormulaInstantiation x : posTacletApp.ifFormulaInstantiations()) {

                    if (x instanceof IfFormulaInstSeq) {
                        boolean antec = ((IfFormulaInstSeq) x).inAntec();
                        inputs.add(new PosInOccurrence(x.getConstrainedFormula(),
                            PosInTerm.getTopLevel(), antec));
                    }
                }
            }
        }
        // built-ins need special treatment:
        // record if instantiations
        if (ruleApp instanceof AbstractBuiltInRuleApp) {
            AbstractBuiltInRuleApp builtIn = (AbstractBuiltInRuleApp) ruleApp;
            builtIn.ifInsts().forEach(inputs::add);
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
