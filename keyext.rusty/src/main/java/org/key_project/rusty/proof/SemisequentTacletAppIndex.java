/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import java.util.Iterator;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.Sequent;
import org.key_project.rusty.logic.SequentFormula;
import org.key_project.rusty.rule.NoPosTacletApp;
import org.key_project.rusty.rule.TacletApp;
import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;

public class SemisequentTacletAppIndex {
    private final Sequent seq;
    private final boolean antec;
    private ImmutableMap<SequentFormula, TermTacletAppIndex> termIndices =
        DefaultImmutableMap.nilMap();

    /**
     * Create an index object for the semisequent determined by <code>s</code> and
     * <code>antec</code> that contains term indices for each formula.
     *
     * @param antec iff true create an index for the antecedent of <code>s</code>, otherwise for the
     *        succedent
     */
    SemisequentTacletAppIndex(Sequent s, boolean antec, Services services,
            TacletIndex tacletIndex) {
        this.seq = s;
        this.antec = antec;
        addTermIndices((antec ? s.antecedent() : s.succedent()).asList(), services, tacletIndex);
    }

    private SemisequentTacletAppIndex(SemisequentTacletAppIndex orig) {
        this.seq = orig.seq;
        this.antec = orig.antec;
        this.termIndices = orig.termIndices;
    }

    /**
     * Add indices for the given formulas to the map <code>termIndices</code>. Existing entries are
     * replaced with the new indices. Note: destructive, use only when constructing new index
     */
    private void addTermIndices(ImmutableList<? super SequentFormula> cfmas, Services services,
            TacletIndex tacletIndex) {
        while (!cfmas.isEmpty()) {
            final SequentFormula cfma = (SequentFormula) cfmas.head();
            cfmas = cfmas.tail();
            addTermIndex(cfma, services, tacletIndex);
        }
    }

    /**
     * Add an index for the given formula to the map <code>termIndices</code>. An existing entry is
     * replaced with the new one. Note: destructive, use only when constructing new index
     */
    private void addTermIndex(SequentFormula cfma, Services services,
            TacletIndex tacletIndex) {
        final PosInOccurrence pos = new PosInOccurrence(cfma, PosInTerm.getTopLevel(), antec);
        termIndices = termIndices.put(cfma, TermTacletAppIndex.create(pos, services, tacletIndex));
    }

    public SemisequentTacletAppIndex copy() {
        return new SemisequentTacletAppIndex(this);
    }

    /**
     * @return all taclet apps for the given position
     */
    public ImmutableList<NoPosTacletApp> getTacletAppAt(PosInOccurrence pos) {
        TermTacletAppIndex termIndex = getTermIndex(pos);
        return termIndex.getTacletAppAt(pos);
    }

    /**
     * Get term index for the formula to which position <code>pos</code> points
     */
    private TermTacletAppIndex getTermIndex(PosInOccurrence pos) {
        return termIndices.get((SequentFormula) pos.sequentFormula());
    }

    /**
     * @return all taclet apps for or below the given position
     */
    public ImmutableList<TacletApp> getTacletAppAtAndBelow(PosInOccurrence pos,
            Services services) {
        return getTermIndex(pos).getTacletAppAtAndBelow(pos, services);
    }

    /**
     * Create an index that additionally contains the taclet
     */
    public SemisequentTacletAppIndex addTaclet(NoPosTacletApp newTaclet, Services services,
            TacletIndex tacletIndex) {
        final SemisequentTacletAppIndex result = copy();
        final Iterator<SequentFormula> it = termIndices.keyIterator();

        while (it.hasNext()) {
            result.addTaclet(newTaclet, it.next(), services, tacletIndex);
        }

        return result;
    }

    /**
     * Update the index for the given formula, which is supposed to be an element of the map
     * <code>termIndices</code>, by adding the taclets that are selected by <code>filter</code>
     * Note: destructive, use only when constructing new index
     */
    private void addTaclet(NoPosTacletApp newTaclet, SequentFormula cfma, Services services,
            TacletIndex tacletIndex) {
        final TermTacletAppIndex oldIndex = termIndices.get(cfma);
        assert oldIndex != null : "Term index that is supposed to be updated " + "does not exist";

        final PosInOccurrence pos = new PosInOccurrence(cfma, PosInTerm.getTopLevel(), antec);

        termIndices = termIndices.put(cfma,
            oldIndex.addTaclet(newTaclet, pos, services, tacletIndex));
    }
}
