/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.join;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.delayedcut.ApplicationCheck;
import de.uka.ilkd.key.proof.delayedcut.DelayedCut;

import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.SequentFormula;

/**
 * Input inspection logic for decision predicates of the delayed-cut join rule. Counter-part of
 * {@code de.uka.ilkd.key.gui.InspectorForDecisionPredicates} in the Swing module {@code key.ui}
 * (InspectorForDecisionPredicates.java:22-86); only the check logic is ported — the Swing class
 * is UI-independent in exactly the same way, it merely implements the Swing-internal
 * {@code CheckedUserInputInspector} interface (here replaced by
 * {@link DecisionPredicateInputF.InspectorF}).
 * <p>
 * The check rejects empty input, non-formulae and formulae that already occur in the target
 * semisequent of the given node, and runs the additional {@link ApplicationCheck}s (the checks
 * of the delayed-cut mechanism).
 */
public final class InspectorForDecisionPredicatesF implements DecisionPredicateInputF.InspectorF {

    private final Services services;
    private final Node node;
    private final int cutMode;
    private final List<ApplicationCheck> additionalChecks = new LinkedList<>();

    public InspectorForDecisionPredicatesF(Services services, Node node, int cutMode,
            List<ApplicationCheck> additionalChecks) {
        this.services = services;
        this.node = node;
        this.cutMode = cutMode;
        this.additionalChecks.addAll(additionalChecks);
    }

    /** Swing InspectorForDecisionPredicates.check (InspectorForDecisionPredicates.java:42-76). */
    @Override
    public String check(String toBeChecked) {
        if (toBeChecked.isEmpty()) {
            return DecisionPredicateInputF.InspectorF.NO_USER_INPUT;
        }
        JTerm term = translate(services, toBeChecked);

        Semisequent semisequent =
            cutMode == DelayedCut.DECISION_PREDICATE_IN_ANTECEDENT ? node.sequent().antecedent()
                    : node.sequent().succedent();
        String position =
            cutMode == DelayedCut.DECISION_PREDICATE_IN_ANTECEDENT ? "antecedent" : "succedent";

        for (SequentFormula sf : semisequent) {
            if (sf.formula() == term) {
                return "Formula already exists in " + position + ".";
            }
        }

        if (term == null || term.sort() != JavaDLTheory.FORMULA) {
            return "Not a formula.";
        }
        for (ApplicationCheck check : additionalChecks) {
            String result = check.check(node, term);
            if (result != null) {
                return result;
            }
        }
        return null;
    }

    /**
     * Translates the given user input into a term; {@code null} if the input cannot be parsed
     * (Swing InspectorForDecisionPredicates.translate, InspectorForDecisionPredicates.java:78-84;
     * same static helper as {@code InspectorForFormulas.translate}).
     */
    public static JTerm translate(Services services, String toBeChecked) {
        try {
            return new KeyIO(services).parseExpression(toBeChecked);
        } catch (Throwable e) {
            return null;
        }
    }
}
