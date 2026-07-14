/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termfeature.BinaryTermFeature;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;


/**
 *
 * The comment below was the description used in the variable condition:
 * <p>
 * <quote>In the taclet language the variable condition is called "\isInductVar". This variable
 * condition checks if a logical variable is marked as an induction variable. A variable is marked
 * as such if its name has the suffix is "Ind" or "IND" and the name has length>3.
 *
 * @author gladisch</quote>
 */
public class IsInductionVariable extends BinaryTermFeature {

    public static final TermFeature INSTANCE = new IsInductionVariable();

    private IsInductionVariable() {}

    @Override
    protected boolean filter(Term term, MutableState mState, LogicServices services) {
        // this has been copied from the former InductionVariableCondition
        // TODO: use termlabels instead of names?
        final String name = term.op().toString();
        if (name.length() > 3) {
            final String suffix = name.substring(name.length() - 3);
            return suffix.equals("Ind") || suffix.equals("IND");
        }
        return false;
    }

}
