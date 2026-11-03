/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof;

import java.util.HashSet;

import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;

import org.key_project.logic.LogicServices;
import org.key_project.prover.proof.rulefilter.RuleFilter;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

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
@NullMarked
final class SingleThreadedTacletIndex extends TacletIndex {

    SingleThreadedTacletIndex() {
        super();
    }

    SingleThreadedTacletIndex(Iterable<Taclet> tacletSet) {
        super(tacletSet);
    }

    private SingleThreadedTacletIndex(
            CopyOnWriteIndexMap<Object, ImmutableList<NoPosTacletApp>> rwList,
            CopyOnWriteIndexMap<Object, ImmutableList<NoPosTacletApp>> antecList,
            CopyOnWriteIndexMap<Object, ImmutableList<NoPosTacletApp>> succList,
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
        return new SingleThreadedTacletIndex(rwList.copy(), antecList.copy(), succList.copy(),
            noFindList, (HashSet<NoPosTacletApp>) partialInstantiatedRuleApps.clone());
    }

    /**
     * {@inheritDoc}
     *
     * <p>
     * The parameter {@code pos} is nullable by design: {@link TacletIndex#getNoFindTaclet} matches
     * find-less taclets with a {@code null} position. Forwarding this nullable position into
     * {@link NoPosTacletApp#matchFind} (non-null parameter) is intended; {@code matchFind} only
     * dereferences the position for taclets with a find/rewrite part, which never occur in the
     * no-find lists matched with a null position.
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    @Override
    protected ImmutableList<NoPosTacletApp> matchTaclets(
            @NonNull ImmutableList<NoPosTacletApp> tacletApps,
            RuleFilter p_filter, @Nullable PosInOccurrence pos, LogicServices services) {
        ImmutableList<NoPosTacletApp> result = ImmutableList.nil();

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
