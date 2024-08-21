/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.PIOPathIterator;
import org.key_project.rusty.logic.PosInOccurrence;
import org.key_project.rusty.rule.NoPosTacletApp;
import org.key_project.rusty.rule.RuleApp;
import org.key_project.rusty.rule.Taclet;
import org.key_project.rusty.rule.TacletApp;
import org.key_project.util.collection.*;

/**
 * Class whose objects represent an index of taclet apps for one particular position within a
 * formula, and that also contain references to the indices of direct subformulas
 */
public class TermTacletAppIndex {
    /** the term for which NoPosTacletApps are kept in this index node */
    private final Term term;
    /** NoPosTacletApps for this term */
    private final ImmutableList<NoPosTacletApp> localTacletApps;
    /** indices for subterms */
    private final ImmutableArray<TermTacletAppIndex> subtermIndices;

    /**
     * Create a TermTacletAppIndex
     */
    private TermTacletAppIndex(Term term, ImmutableList<NoPosTacletApp> localTacletApps,
            ImmutableArray<TermTacletAppIndex> subtermIndices) {
        this.term = term;
        this.subtermIndices = subtermIndices;
        this.localTacletApps = localTacletApps;
    }

    public static TermTacletAppIndex create(PosInOccurrence pos, Services services,
            TacletIndex tacletIndex) {
        assert pos.isTopLevel() : "Someone tried to create a term index for a real subterm";

        return createHelp(pos, services, tacletIndex);
    }

    private static TermTacletAppIndex createHelp(PosInOccurrence pos, Services services,
            TacletIndex tacletIndex) {
        final Term localTerm = pos.subTerm();

        final ImmutableList<NoPosTacletApp> localApps =
            getFindTaclet(pos, services, tacletIndex);

        final ImmutableArray<TermTacletAppIndex> subIndices =
            createSubIndices(pos, services, tacletIndex);

        final TermTacletAppIndex res =
            new TermTacletAppIndex(localTerm, localApps, subIndices);

        return res;
    }

    private TermTacletAppIndex getSubIndex(int subterm) {
        return subtermIndices.get(subterm);
    }

    /**
     * @return the sub-index for the given position
     */
    private TermTacletAppIndex descend(PosInOccurrence pos) {
        if (pos.isTopLevel()) {
            return this;
        }

        final PIOPathIterator it = pos.iterator();
        TermTacletAppIndex res = this;

        while (true) {
            final int child = it.next();
            if (child == -1) {
                return res;
            }

            res = res.getSubIndex(child);
        }
    }

    /**
     * collects all RewriteTacletInstantiations for the given heuristics in a subterm of the
     * constrainedFormula described by a PosInOccurrence
     *
     * @param pos the {@link PosInOccurrence} to focus
     * @param services the {@link Services} object encapsulating information about the Rust
     *        datastructures like (static)types etc.
     * @return list of all possible instantiations
     */
    private static ImmutableList<NoPosTacletApp> getRewriteTaclet(PosInOccurrence pos,
            Services services, TacletIndex tacletIndex) {

        return tacletIndex.getRewriteTaclet(pos, services);
    }

    /**
     * collects all FindTaclets with instantiations for the given heuristics and position
     *
     * @param pos the PosInOccurrence to focus
     * @param services the Services object encapsulating information about the Rust datastructures
     *        like (static)types etc.
     * @return list of all possible instantiations
     */
    private static ImmutableList<NoPosTacletApp> getFindTaclet(PosInOccurrence pos,
            Services services, TacletIndex tacletIndex) {
        ImmutableList<NoPosTacletApp> tacletInsts = ImmutableSLList.nil();
        if (pos.isTopLevel()) {
            if (pos.isInAntec()) {
                tacletInsts = tacletInsts.prepend(antecTaclet(pos, services, tacletIndex));
            } else {
                tacletInsts = tacletInsts.prepend(succTaclet(pos, services, tacletIndex));
            }
        } else {
            tacletInsts = tacletInsts.prepend(getRewriteTaclet(pos, services, tacletIndex));
        }
        return tacletInsts;
    }

    /**
     * collects all AntecedentTaclet instantiations for the given heuristics and SequentFormula
     *
     * @param pos the PosInOccurrence of the SequentFormula the taclets have to be connected to (pos
     *        must point to the top level formula, i.e. <tt>pos.isTopLevel()</tt> must be true)
     * @param services the Services object encapsulating information about the Rust datastructures
     *        like (static)types etc.
     * @return list of all possible instantiations
     */
    private static ImmutableList<NoPosTacletApp> antecTaclet(PosInOccurrence pos,
            Services services, TacletIndex tacletIndex) {
        return tacletIndex.getAntecedentTaclet(pos, services);
    }

    /**
     * collects all SuccedentTaclet instantiations for the given heuristics and SequentFormula
     *
     * @param pos the PosInOccurrence of the SequentFormula the taclets have to be connected to (pos
     *        must point to the top level formula, i.e. <tt>pos.isTopLevel()</tt> must be true)
     * @param services the Services object encapsulating information about the Rust datastructures
     *        like (static)types etc.
     * @return list of all possible instantiations
     */
    private static ImmutableList<NoPosTacletApp> succTaclet(PosInOccurrence pos,
            Services services, TacletIndex tacletIndex) {
        return tacletIndex.getSuccedentTaclet(pos, services);
    }

    /**
     * Descend and create indices for each of the direct subterms of the given term
     *
     * @param pos pointer to the term/formula for whose subterms indices are to be created
     * @return list of the index objects
     */
    private static ImmutableArray<TermTacletAppIndex> createSubIndices(PosInOccurrence pos,
            Services services, TacletIndex tacletIndex) {
        final Term localTerm = pos.subTerm();
        final TermTacletAppIndex[] result = new TermTacletAppIndex[localTerm.arity()];

        for (int i = 0; i < result.length; i++) {
            result[i] = createHelp(pos.down(i), services, tacletIndex);
        }

        return new ImmutableArray<>(result);
    }

    /**
     * @return all taclet apps for the given position
     */
    public ImmutableList<NoPosTacletApp> getTacletAppAt(PosInOccurrence pos) {
        final TermTacletAppIndex index = descend(pos);
        return filter(index.localTacletApps);
    }

    /**
     * @param taclets the list of {@link Taclet}s to be filtered
     * @return filtered list
     */
    public static ImmutableList<NoPosTacletApp> filter(ImmutableList<NoPosTacletApp> taclets) {
        ImmutableList<NoPosTacletApp> result = ImmutableSLList.nil();

        for (final NoPosTacletApp app : taclets) {
            result = result.prepend(app);
        }

        return result;
    }

    /**
     * @return all taclet apps for or below the given position
     */
    public ImmutableList<TacletApp> getTacletAppAtAndBelow(PosInOccurrence pos, Services services) {
        return descend(pos).collectTacletApps(pos, services);
    }

    /**
     * Collect all taclet apps that are stored by <code>this</code> (and by the sub-indices of
     * <code>this</code>). <code>NoPosTacletApp</code>s are converted to <code>PosTacletApp</code>s
     * using the parameter <code>pos</code>
     *
     * @param pos The position of this index
     * @return a list of all taclet apps
     */
    private ImmutableList<TacletApp> collectTacletApps(PosInOccurrence pos,
            Services services) {

        ImmutableList<TacletApp> result = ImmutableSLList.nil();

        final ImmutableList<Pair<PosInOccurrence, ImmutableList<NoPosTacletApp>>> allTacletsHereAndBelow =
            collectAllTacletAppsHereAndBelow(pos, ImmutableSLList.nil());

        for (final Pair<PosInOccurrence, ImmutableList<NoPosTacletApp>> pair : allTacletsHereAndBelow) {
            result = convert(pair.second, pair.first, result, services);
        }

        return result;
    }

    /**
     * Collect all <code>NoPosTacletApp</code> s that are stored by <code>this</code> (and by the
     * sub-indices of <code>this</code>).
     *
     * @param pos The position of this index
     * @param collectedApps the {@link ImmutableMap <PosInOccurrence,ImmutableList<NoPosTacletApp>>}
     *        to which to add the found taclet applications; it must not contain {@code pos} or any
     *        position below pos as key
     * @return the resulting list of taclet applications from this and all subterm taclet indices
     */
    private ImmutableList<Pair<PosInOccurrence, ImmutableList<NoPosTacletApp>>> collectAllTacletAppsHereAndBelow(
            PosInOccurrence pos,
            ImmutableList<Pair<PosInOccurrence, ImmutableList<NoPosTacletApp>>> collectedApps) {

        // assert collectedApps.get(pos) == null;
        collectedApps = collectedApps.prepend(new Pair<>(pos, localTacletApps));

        for (int subterm = 0; subterm < subtermIndices.size(); subterm++) {
            collectedApps = subtermIndices.get(subterm)
                    .collectAllTacletAppsHereAndBelow(pos.down(subterm), collectedApps);
        }

        return collectedApps;
    }

    private ImmutableList<TacletApp> convert(ImmutableList<? extends RuleApp> rules,
            PosInOccurrence pos, ImmutableList<TacletApp> convertedApps,
            Services services) {

        for (final RuleApp app : rules) {
            final TacletApp tacletApp =
                TacletAppIndex.createTacletApp((NoPosTacletApp) app, pos, services);
            if (tacletApp != null) {
                convertedApps = convertedApps.prepend(tacletApp);
            }
        }

        return convertedApps;
    }

    /**
     * Create a new tree of indices that additionally contain the taclet
     *
     * @param newTaclet The taclet that is supposed to be added
     * @param pos Pointer to the term/formula for which an index is to be created. <code>pos</code>
     *        has to be a top-level term position
     * @return the index object
     */
    public TermTacletAppIndex addTaclet(NoPosTacletApp newTaclet, PosInOccurrence pos, Services services, TacletIndex tacletIndex) {
        return addTacletHelp(newTaclet, pos, services, tacletIndex);
    }

    private TermTacletAppIndex addTacletHelp(NoPosTacletApp newTaclet, PosInOccurrence pos,
                                              Services services, TacletIndex tacletIndex) {
        final ImmutableArray<TermTacletAppIndex> newSubIndices =
                addTacletsSubIndices(newTaclet, pos, services, tacletIndex);

        final ImmutableList<NoPosTacletApp> additionalApps =
                getFindTaclet(pos, services, tacletIndex);

        return new TermTacletAppIndex(term, localTacletApps.prepend(additionalApps), newSubIndices);
    }

    private ImmutableArray<TermTacletAppIndex> addTacletsSubIndices(NoPosTacletApp newTaclet,
                                                                    PosInOccurrence pos, Services services, TacletIndex tacletIndex) {
        final TermTacletAppIndex[] result = new TermTacletAppIndex[subtermIndices.size()];

        for (int i = 0; i < subtermIndices.size(); i++) {
            final TermTacletAppIndex oldSubIndex = subtermIndices.get(i);
            final TermTacletAppIndex newSubIndex =
                    oldSubIndex.addTacletHelp(newTaclet, pos.down(i), services, tacletIndex);
            result[i] = newSubIndex;
        }

        return new ImmutableArray<>(result);
    }
}
