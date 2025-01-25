/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import java.util.function.Predicate;

import de.uka.ilkd.key.logic.label.TermLabel;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termfeature.BinaryTermFeature;

/**
 * A termfeature that can be used to check whether a term has a specific label
 * {@link #create(Predicate<Term>)}.
 */
public class TermPredicateTermFeature extends BinaryTermFeature {


    public static BinaryTermFeature create(Predicate<Term> predicate) {
        return new TermPredicateTermFeature(predicate);
    }

    private Predicate<Term> property;

    private TermLabel label;

    protected TermPredicateTermFeature(Predicate<Term> property) {
        this.property = property;
    }

    @Override
    protected boolean filter(Term t, MutableState mState, LogicServices services) {
        return property.test(t);
    }
}
