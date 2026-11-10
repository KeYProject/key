/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.termfeature;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Property;
import org.key_project.logic.Term;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termProjection.TermBuffer;

/// Term feature for testing equality of two terms. The feature returns zero iff it is invoked on a
/// term that is equal modulo `equalsProp` to the current value of `pattern`.
///
/// NB: it is not possible to use general `ProjectionToTerm` here, because the information
/// necessary to evaluate a `ProjectionToTerm` is not available in a term feature
public class EqTermFeature extends BinaryTermFeature {
    private final TermBuffer pattern;
    private final Property<Term> equalsProp;

    public static TermFeature create(TermBuffer pattern, Property<Term> equalsProp) {
        return new EqTermFeature(pattern, equalsProp);
    }

    private EqTermFeature(TermBuffer pattern, Property<Term> equalsProp) {
        this.pattern = pattern;
        this.equalsProp = equalsProp;
    }

    @Override
    protected boolean filter(Term term, MutableState mState, LogicServices services) {
        final Term patternTerm = pattern.getContent(mState);
        assert patternTerm != null : "@AssumeAssertion(nullness): pattern should not be null";
        return equalsProp.equalsModThisProperty(term, patternTerm);
    }
}
