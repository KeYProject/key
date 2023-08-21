/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.TacletApp;

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

    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";

        ImmutableList<IfFormulaInstantiation> list = app.ifFormulaInstantiations();
        final SequentFormula findFormula = pos.sequentFormula();
        final boolean findIsInAntec = pos.isInAntec();

        assert list != null;

        for (final IfFormulaInstantiation aList : list) {
            final IfFormulaInstSeq iffi = (IfFormulaInstSeq) aList;
            assert iffi != null;
            final SequentFormula ifFormula = iffi.getConstrainedFormula();

            final boolean result =
                findIsInAntec != iffi.inAntec() || !findFormula.equals(ifFormula);
            if (!result) {
                return false;
            }
        }
        return true;
    }

}
