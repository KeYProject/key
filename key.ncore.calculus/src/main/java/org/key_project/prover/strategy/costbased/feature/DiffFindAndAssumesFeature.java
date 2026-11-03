/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.ITacletApp;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstSeq;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.util.collection.ImmutableList;

import org.checkerframework.checker.nullness.qual.MonotonicNonNull;

/**
 * Binary feature that returns zero iff the <tt>\assumes</tt>- and find-formula of a Taclet are
 * matched to different members of the sequent. If a taclet has more than one formula in its
 * <tt>\assumes</tt> part, all of them must be matched to different members.
 */
// Weakly stable: compares the whole find FORMULA (pos.sequentFormula(), by content) to the
// application's \assumes instantiations. The find can be a proper sub-formula (replace_known's
// \find(b)), so the formula sits above the find term; a sibling rewrite then changes the formula
// while the find subterm survives. Reusable only while the find formula is unchanged.
@WeakStableCost
public class DiffFindAndAssumesFeature<GOAL extends ProofGoal<GOAL>>
        extends BinaryTacletAppFeature<GOAL> {
    public static <GOAL extends ProofGoal<GOAL>> DiffFindAndAssumesFeature<GOAL> create() {
        return new DiffFindAndAssumesFeature<>();
    }

    private DiffFindAndAssumesFeature() {}

    @Override
    protected boolean filter(@MonotonicNonNull ITacletApp app, PosInOccurrence pos, GOAL goal,
            MutableState mState) {
        assert pos != null : "Feature is only applicable to rules with find";

        ImmutableList<AssumesFormulaInstantiation> list = app.assumesFormulaInstantiations();
        final var findFormula = pos.sequentFormula();
        final boolean findIsInAntec = pos.isInAntec();

        assert list != null;

        for (final AssumesFormulaInstantiation aList : list) {
            final AssumesFormulaInstSeq instantiationOfAssumesFormula =
                (AssumesFormulaInstSeq) aList;
            assert instantiationOfAssumesFormula != null;
            final SequentFormula assumesFormula = instantiationOfAssumesFormula.getSequentFormula();

            final boolean result =
                findIsInAntec != instantiationOfAssumesFormula.inAntecedent() ||
                        !findFormula.equals(assumesFormula);
            if (!result) {
                return false;
            }
        }
        return true;
    }
}
