/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.HashMap;
import java.util.HashSet;

import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;

import org.key_project.logic.LogicServices;
import org.key_project.prover.proof.rulefilter.RuleFilter;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;

/**
 * The default taclet index implementation. It executes method
 * {@link #matchTaclets(ImmutableList, RuleFilter, PosInOccurrence, LogicServices)}
 * in a single thread
 * (the thread invoking the method).
 *
 * Do not create this index directly. Use the {@link TacletIndexKit#createTacletIndex()} resp.
 * {@link TacletIndexKit#createTacletIndex(Iterable)}.
 *
 * @see TacletIndex
 * @see TacletIndexKit
 */
final class SingleThreadedTacletIndex extends TacletIndex {

    SingleThreadedTacletIndex() {
        super();
    }

    SingleThreadedTacletIndex(Iterable<Taclet> tacletSet) {
        super(tacletSet);
    }

    private SingleThreadedTacletIndex(HashMap<Object, ImmutableList<NoPosTacletApp>> rwList,
            HashMap<Object, ImmutableList<NoPosTacletApp>> antecList,
            HashMap<Object, ImmutableList<NoPosTacletApp>> succList,
            ImmutableList<NoPosTacletApp> noFindList,
            HashSet<NoPosTacletApp> partialInstantiatedRuleApps) {
        super(rwList, antecList, succList, noFindList, partialInstantiatedRuleApps);
    }

    /**
     * {@inheritDoc}
     */
    @SuppressWarnings("unchecked")
    @Override
    public TacletIndex copy() {
        return new SingleThreadedTacletIndex(
            (HashMap<Object, ImmutableList<NoPosTacletApp>>) rwList.clone(),
            (HashMap<Object, ImmutableList<NoPosTacletApp>>) antecList.clone(),
            (HashMap<Object, ImmutableList<NoPosTacletApp>>) succList.clone(), noFindList,
            (HashSet<NoPosTacletApp>) partialInstantiatedRuleApps.clone());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected ImmutableList<NoPosTacletApp> matchTaclets(
            @NonNull ImmutableList<NoPosTacletApp> tacletApps,
            RuleFilter p_filter, PosInOccurrence pos, LogicServices services) {
        ImmutableList<NoPosTacletApp> result = ImmutableSLList.nil();

        for (final NoPosTacletApp tacletApp : tacletApps) {
            if (!p_filter.filter(tacletApp.taclet())) {
                continue;
            }
            final NoPosTacletApp newTacletApp = tacletApp.matchFind(pos, services);
            if (newTacletApp != null) {
                result = result.prepend(newTacletApp);
            }
        }

        return result;
    }

}
