/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.termfeature;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.prover.strategy.costbased.MutableState;

/// return zero cost if given term does not contain any free variables.
public class ClosedExpressionTermFeature extends BinaryTermFeature {

    public static final TermFeature INSTANCE = new ClosedExpressionTermFeature();

    private ClosedExpressionTermFeature() {}

    protected boolean filter(Term term, MutableState mState, LogicServices services) {
        return term.freeVars().isEmpty();
    }
}
