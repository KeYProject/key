/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.concurrent.atomic.AtomicLong;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.rulefilter.RuleFilter;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.util.collection.*;

/**
 * This class holds <code>TermTacletAppIndex</code>s for all formulas of a semisequent.
 */
public class SemisequentTacletAppIndex {
    public static final AtomicLong PERF_UPDATE = new AtomicLong();
    public static final AtomicLong PERF_ADD = new AtomicLong();
    public static final AtomicLong PERF_REMOVE = new AtomicLong();

    private ImmutableMap<SequentFormula, TermTacletAppIndex> termIndices =
        DefaultImmutableMap.nilMap();

    private TermTacletAppIndexCacheSet indexCaches;

    private final RuleFilter ruleFilter;

    private final Sequent seq;
    private final boolean antec;

    /**
     * Add indices for the given formulas to the map <code>termIndices</code>. Existing entries are
     * replaced with the new indices. Note: destructive, use only when constructing new index
     */
    private void addTermIndices(ImmutableList<SequentFormula> cfmas, Services services,
            TacletIndex tacletIndex, NewRuleListener listener) {
        while (!cfmas.isEmpty()) {
            final SequentFormula cfma = cfmas.head();
            cfmas = cfmas.tail();
            addTermIndex(cfma, services, tacletIndex, listener);
        }
    }

    /**
     * Add an index for the given formula to the map <code>termIndices</code>. An existing entry is
     * replaced with the new one. Note: destructive, use only when constructing new index
     */
    private void addTermIndex(SequentFormula cfma, Services services,
            TacletIndex tacletIndex, NewRuleListener listener) {
        final PosInOccurrence pos = new PosInOccurrence(cfma, PosInTerm.getTopLevel(), antec);
        termIndices = termIndices.put(cfma, TermTacletAppIndex.create(pos, services, tacletIndex,
            listener, ruleFilter, indexCaches));
    }

    /**
     * Update the index for the given formula, which is supposed to be an element of the map
     * <code>termIndices</code>, by adding the taclets that are selected by <code>filter</code>
     * Note: destructive, use only when constructing new index
     */
    private void addTaclets(RuleFilter filter, SequentFormula cfma, Services services,
            TacletIndex tacletIndex, NewRuleListener listener) {
        final TermTacletAppIndex oldIndex = termIndices.get(cfma);
        assert oldIndex != null : "Term index that is supposed to be updated " + "does not exist";

        final PosInOccurrence pos = new PosInOccurrence(cfma, PosInTerm.getTopLevel(), antec);

        termIndices = termIndices.put(cfma,
            oldIndex.addTaclets(filter, pos, services, tacletIndex, listener));
    }

    /**
     * Remove the indices for the given formulas from the map <code>termIndices</code>. Note:
     * destructive, use only when constructing new index
     */
    private void removeTermIndices(ImmutableList<SequentFormula> cfmas) {
        for (SequentFormula cfma : cfmas) {
            removeTermIndex(cfma);
        }
    }

    /**
     * Remove the index for the given formula from the map <code>termIndices</code>. Note:
     * destructive, use only when constructing new index
     */
    private void removeTermIndex(SequentFormula cfma) {
        termIndices = termIndices.remove(cfma);
    }

    /**
     * Remove the formulas that are listed as modified by <code>infos</code>
     *
     * @return the old indices in the same order as the list <code>infos</code> Note: destructive,
     *         use only when constructing new index
     */
    private List<TermTacletAppIndex> removeFormulas(ImmutableList<FormulaChangeInfo> infos) {
        var oldIndices = new ArrayList<TermTacletAppIndex>(infos.size());

        for (FormulaChangeInfo info : infos) {
            final SequentFormula oldFor = info.getOriginalFormula();

            oldIndices.add(termIndices.get(oldFor));
            removeTermIndex(oldFor);
        }

        return oldIndices;
    }

    /**
     * Update the given list of term indices according to the list <code>infos</code> of
     * modification information. Both lists have to be compatible, i.e. same length and same order.
     * The new indices are inserted in the map <code>termIndices</code>. Note: destructive, use only
     * when constructing new index
     */
    private void updateTermIndices(List<TermTacletAppIndex> oldIndices,
            ImmutableList<FormulaChangeInfo> infos, Services services, TacletIndex tacletIndex,
            NewRuleListener listener) {
        final Iterator<FormulaChangeInfo> infoIt = infos.iterator();
        final Iterator<TermTacletAppIndex> oldIndexIt = oldIndices.iterator();

        while (infoIt.hasNext()) {
            final FormulaChangeInfo info = infoIt.next();
            final SequentFormula newFor = info.getNewFormula();
            final TermTacletAppIndex oldIndex = oldIndexIt.next();

            if (oldIndex == null)
            // completely rebuild the term index
            {
                addTermIndex(newFor, services, tacletIndex, listener);
            } else {
                final PosInOccurrence oldPos = info.getPositionOfModification();
                final PosInOccurrence newPos = oldPos.replaceConstrainedFormula(newFor);
                termIndices = termIndices.put(newFor,
                    oldIndex.update(newPos, services, tacletIndex, listener, indexCaches));
            }
        }
    }

    private void updateTermIndices(ImmutableList<FormulaChangeInfo> infos,
            Services services, TacletIndex tacletIndex, NewRuleListener listener) {

        // remove original indices
        final List<TermTacletAppIndex> oldIndices = removeFormulas(infos);

        updateTermIndices(oldIndices, infos, services, tacletIndex, listener);
    }

    /**
     * Create an index object for the semisequent determined by <code>s</code> and
     * <code>antec</code> that contains term indices for each formula.
     *
     * @param antec iff true create an index for the antecedent of <code>s</code>, otherwise for the
     *        succedent
     */
    SemisequentTacletAppIndex(Sequent s, boolean antec, Services services, TacletIndex tacletIndex,
            NewRuleListener listener, RuleFilter ruleFilter,
            TermTacletAppIndexCacheSet indexCaches) {
        this.seq = s;
        this.antec = antec;
        this.ruleFilter = ruleFilter;
        this.indexCaches = indexCaches;
        addTermIndices((antec ? s.antecedent() : s.succedent()).asList(), services, tacletIndex,
            listener);
    }

    private SemisequentTacletAppIndex(SemisequentTacletAppIndex orig) {
        this.seq = orig.seq;
        this.antec = orig.antec;
        this.ruleFilter = orig.ruleFilter;
        this.termIndices = orig.termIndices;
        this.indexCaches = orig.indexCaches;
    }

    public SemisequentTacletAppIndex copy() {
        return new SemisequentTacletAppIndex(this);
    }

    /**
     * Get term index for the formula to which position <code>pos</code> points
     */
    private TermTacletAppIndex getTermIndex(PosInOccurrence pos) {
        return termIndices.get(pos.sequentFormula());
    }

    /**
     * @return all taclet apps for the given position
     */
    public ImmutableList<NoPosTacletApp> getTacletAppAt(PosInOccurrence pos, RuleFilter filter) {
        return getTermIndex(pos).getTacletAppAt(pos, filter);
    }

    /**
     * @return all taclet apps for or below the given position
     */
    public ImmutableList<TacletApp> getTacletAppAtAndBelow(PosInOccurrence pos, RuleFilter filter,
            Services services) {
        return getTermIndex(pos).getTacletAppAtAndBelow(pos, filter, services);
    }

    /**
     * called if a formula has been replaced
     *
     * @param sci SequentChangeInfo describing the change of the sequent
     */
    public SemisequentTacletAppIndex sequentChanged(SequentChangeInfo sci, Services services,
            TacletIndex tacletIndex, NewRuleListener listener) {
        if (sci.hasChanged(antec)) {
            final SemisequentTacletAppIndex result = copy();

            var time = System.nanoTime();
            result.removeTermIndices(sci.removedFormulas(antec));
            PERF_REMOVE.getAndAdd(System.nanoTime() - time);

            time = System.nanoTime();
            result.updateTermIndices(sci.modifiedFormulas(antec), services, tacletIndex, listener);
            PERF_UPDATE.getAndAdd(System.nanoTime() - time);

            time = System.nanoTime();
            result.addTermIndices(sci.addedFormulas(antec), services, tacletIndex, listener);
            PERF_ADD.getAndAdd(System.nanoTime() - time);
            return result;
        }

        return this;
    }


    /**
     * Create an index that additionally contains the taclets that are selected by
     * <code>filter</code>
     *
     * @param filter The taclets that are supposed to be added
     */
    public SemisequentTacletAppIndex addTaclets(RuleFilter filter, Services services,
            TacletIndex tacletIndex, NewRuleListener listener) {
        final SemisequentTacletAppIndex result = copy();
        final Iterator<SequentFormula> it = termIndices.keyIterator();

        while (it.hasNext()) {
            result.addTaclets(filter, it.next(), services, tacletIndex, listener);
        }

        return result;
    }

    /**
     * Reports all cached rule apps. Calls ruleAdded on the given NewRuleListener for every cached
     * taclet app.
     */
    void reportRuleApps(NewRuleListener l) {
        for (final ImmutableMapEntry<SequentFormula, TermTacletAppIndex> entry : termIndices) {
            final SequentFormula cfma = entry.key();
            final TermTacletAppIndex index = entry.value();
            final PosInOccurrence pio = new PosInOccurrence(cfma, PosInTerm.getTopLevel(), antec);

            index.reportTacletApps(pio, l);
        }
    }

    void setIndexCache(TermTacletAppIndexCacheSet indexCaches) {
        this.indexCaches = indexCaches;
    }
}
