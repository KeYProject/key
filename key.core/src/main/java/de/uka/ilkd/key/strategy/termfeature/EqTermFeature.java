/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termProjection.TermBuffer;
import org.key_project.prover.strategy.costbased.termfeature.BinaryTermFeature;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;

/**
 * Term feature for testing equality of two terms. The feature returns zero iff it is invoked on a
 * term that is equal to the current value of <code>pattern</code>.
 * <p>
 * NB: it is not possible to use general <code>ProjectionToTerm</code> here, because the information
 * necessary to evaluate a <code>ProjectionToTerm</code> is not available in a term feature
 */
public class EqTermFeature extends BinaryTermFeature {

    private final TermBuffer<Goal> pattern;

    public static TermFeature create(TermBuffer<Goal> pattern) {
        return new EqTermFeature(pattern);
    }

    private EqTermFeature(TermBuffer<Goal> pattern) {
        this.pattern = pattern;
    }

    @Override
    protected boolean filter(Term term, MutableState mState, LogicServices services) {
        return RENAMING_TERM_PROPERTY.equalsModThisProperty(term, pattern.getContent(mState));
    }
}
