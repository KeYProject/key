/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.api;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.prover.sequent.SequentFormula;

/**
 * Created by sarah on 5/2/17.
 */
public final class SearchNode {
    private final org.key_project.prover.sequent.SequentFormula[] pattern;
    private final int pos;
    private final int succAntPos;
    private final MatchConditions mc;


    public SearchNode(SequentFormula[] pattern, int succAntPos) {
        this.pattern = pattern;
        this.pos = 0;
        this.succAntPos = succAntPos;
        this.mc = MatchConditions.EMPTY_MATCHCONDITIONS;
    }

    public SearchNode(SearchNode parent, MatchConditions cond) {
        this.pattern = parent.pattern;
        this.succAntPos = parent.succAntPos;
        int parentPos = parent.pos;
        this.pos = parentPos + 1;
        mc = cond;
    }

    public boolean isAntecedent() {
        return pos < succAntPos;
    }

    public Term getPatternTerm() {
        return (Term) pattern[pos].formula();
    }

    public boolean isFinished() {
        return pos >= pattern.length;
    }

    public SVInstantiations getInstantiations() {
        return mc == null ? null : mc.getInstantiations();
    }

    public MatchConditions getMatchConditions() {
        return mc;
    }
}
