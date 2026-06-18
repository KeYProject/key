/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.prover.rules.instantiation.AssumesFormulaInstSeq;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.util.collection.ImmutableList;

/**
 * Binary feature that returns zero iff the <tt>\assumes</tt>- and find-formula of a Taclet are
 * matched to different members of the sequent. If a taclet has more than one formula in its
 * <tt>\assumes</tt> part, all of the must be matched to different members.
 */
public class DiffFindAndIfFeature extends BinaryTacletAppFeature {

    /** the single instance of this feature */
    public static final Feature INSTANCE = new DiffFindAndIfFeature();

    private DiffFindAndIfFeature() {}

    @Override
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
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
