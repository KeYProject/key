/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import org.key_project.rusty.Services;
import org.key_project.rusty.logic.PosInOccurrence;
import org.key_project.rusty.logic.Sequent;
import org.key_project.rusty.rule.*;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;


public class TacletAppIndex {
    private final TacletIndex tacletIndex;

    private SemisequentTacletAppIndex antecIndex;
    private SemisequentTacletAppIndex succIndex;

    private final Goal goal;

    /**
     * The sequent with the formulas for which taclet indices are hold by this object. Invariant:
     * <code>seq != null</code> implies that the indices <code>antecIndex</code>,
     * <code>succIndex</code> are up-to-date for the sequent <code>seq</code>
     */
    private Sequent seq;

    public TacletAppIndex(TacletIndex tacletIndex, Goal goal, Services services) {
        this(tacletIndex, null, null, goal, null);
    }

    private TacletAppIndex(TacletIndex tacletIndex, SemisequentTacletAppIndex antecIndex,
            SemisequentTacletAppIndex succIndex, @NonNull Goal goal, Sequent seq) {
        this.tacletIndex = tacletIndex;
        this.antecIndex = antecIndex;
        this.succIndex = succIndex;
        this.goal = goal;
        this.seq = seq;
    }

    public TacletIndex tacletIndex() {
        return tacletIndex;
    }

    public ImmutableList<TacletApp> getTacletAppAt(PosInOccurrence pos, Services services) {
        return prepend(getFindTacletWithPos(pos, services), getNoFindTaclet(services));
    }

    private ImmutableList<TacletApp> getFindTacletWithPos(PosInOccurrence pos,
            Services services) {
        ImmutableList<NoPosTacletApp> tacletInsts = getFindTaclet(pos);
        return createTacletApps(tacletInsts, pos, services);
    }


    /**
     * collects all NoFindTacletInstantiations
     *
     * @param services the Services object encapsulating information about the Rust datastructures
     *        like (static)types etc.
     * @return list of all possible instantiations
     */
    public ImmutableList<NoPosTacletApp> getNoFindTaclet(Services services) {
        return tacletIndex().getNoFindTaclet(services);
    }

    /**
     * collects all FindTaclets with instantiations and position
     *
     * @param pos the PosInOccurrence to focus
     * @return list of all possible instantiations
     */
    public ImmutableList<NoPosTacletApp> getFindTaclet(PosInOccurrence pos) {
        return getIndex(pos).getTacletAppAt(pos);
    }

    private void ensureIndicesExist() {
        if (isOutdated()) {
            // Indices are not up-to-date
            createAllFromGoal();
        }
    }

    private void createAllFromGoal() {
        this.seq = getNode().sequent();

        antecIndex =
            new SemisequentTacletAppIndex(getSequent(), true, getServices(), tacletIndex());
        succIndex =
            new SemisequentTacletAppIndex(getSequent(), false, getServices(), tacletIndex());
    }

    private Services getServices() {
        return getProof().getServices();
    }

    private Proof getProof() {
        return getNode().proof();
    }

    /**
     * @return true iff this index is currently outdated with respect to the sequent of the
     *         associated goal; this does not detect other modifications
     *         like an altered user
     *         constraint
     */
    private boolean isOutdated() {
        return getGoal() == null || getSequent() != getNode().sequent();
    }

    private Goal getGoal() {
        return goal;
    }

    private Sequent getSequent() {
        return seq;
    }

    private Node getNode() {
        return goal.getNode();
    }

    private SemisequentTacletAppIndex getIndex(PosInOccurrence pos) {
        ensureIndicesExist();
        return pos.isInAntec() ? antecIndex : succIndex;
    }

    private static ImmutableList<TacletApp> prepend(ImmutableList<TacletApp> l1,
            ImmutableList<NoPosTacletApp> l2) {
        for (NoPosTacletApp aL2 : l2) {
            l1 = l1.prepend(aL2);
        }
        return l1;
    }

    /**
     * creates TacletApps out of each single NoPosTacletApp object
     *
     * @param tacletInsts the list of NoPosTacletApps the TacletApps are to be created from
     * @param pos the PosInOccurrence to focus
     * @return list of all created TacletApps
     */
    static ImmutableList<TacletApp> createTacletApps(ImmutableList<NoPosTacletApp> tacletInsts,
            PosInOccurrence pos, Services services) {
        ImmutableList<TacletApp> result = ImmutableSLList.nil();
        for (NoPosTacletApp tacletApp : tacletInsts) {
            if (tacletApp.taclet() instanceof FindTaclet) {
                PosTacletApp newTacletApp = tacletApp.setPosInOccurrence(pos, services);
                if (newTacletApp != null) {
                    result = result.prepend(newTacletApp);
                }
            } else {
                result = result.prepend(tacletApp);
            }
        }
        return result;
    }

    /**
     * returns a new TacletAppIndex with a given TacletIndex
     */
    TacletAppIndex copyWith(TacletIndex p_tacletIndex, Goal goal) {
        return new TacletAppIndex(p_tacletIndex, antecIndex, succIndex, goal, getSequent());
    }

    /**
     * updates the internal caches after a new Taclet with instantiation information has been added
     * to the TacletIndex.
     *
     * @param tacletApp the partially instantiated Taclet to add
     */
    public void addedNoPosTacletApp(NoPosTacletApp tacletApp) {
        // TODO
    }
}
