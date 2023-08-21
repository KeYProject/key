/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.gui.utilities.CheckedUserInput.CheckedUserInputInspector;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.delayedcut.ApplicationCheck;
import de.uka.ilkd.key.proof.delayedcut.DelayedCut;

public class InspectorForDecisionPredicates implements CheckedUserInputInspector {

    private final Services services;
    private final Node node;
    private final int cutMode;
    private final List<ApplicationCheck> additionalChecks = new LinkedList<>();



    public InspectorForDecisionPredicates(Services services, Node node, int cutMode,
            List<ApplicationCheck> additionalChecks) {
        super();
        this.services = services;
        this.node = node;
        this.cutMode = cutMode;
        this.additionalChecks.addAll(additionalChecks);
    }



    @Override
    public String check(String toBeChecked) {
        if (toBeChecked.isEmpty()) {
            return CheckedUserInputInspector.NO_USER_INPUT;
        }
        Term term = translate(services, toBeChecked);

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

        // if(term == null){
        // return NO_USER_INPUT;
        // }

        if (term == null || term.sort() != Sort.FORMULA) {
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

    public static Term translate(Services services, String toBeChecked) {
        try {
            return new KeyIO(services).parseExpression(toBeChecked);
        } catch (Throwable e) {
            return null;
        }
    }

}
