/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termgenerator;

import java.util.Iterator;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.feature.MutableState;

/**
 * Term generator that enumerates the formulas of the current sequent/antecedent/succedent.
 */
public abstract class SequentFormulasGenerator implements TermGenerator {

    protected SequentFormulasGenerator() {}

    public static SequentFormulasGenerator antecedent() {
        return new SequentFormulasGenerator() {
            protected Iterator<Term> generateForIt(Goal goal) {
                return goal.sequent().antecedent().iterator();
            }
        };
    }

    public static SequentFormulasGenerator succedent() {
        return new SequentFormulasGenerator() {
            protected Iterator<Term> generateForIt(Goal goal) {
                return goal.sequent().succedent().iterator();
            }
        };
    }

    public static SequentFormulasGenerator sequent() {
        return new SequentFormulasGenerator() {
            protected Iterator<Term> generateForIt(Goal goal) {
                return goal.sequent().iterator();
            }
        };
    }

    protected abstract Iterator<Term> generateForIt(Goal goal);

    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal,
            MutableState mState) {
        return generateForIt(goal);
    }

}
