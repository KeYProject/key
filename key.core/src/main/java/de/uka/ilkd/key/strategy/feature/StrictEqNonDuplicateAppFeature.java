/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import java.util.Iterator;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.util.collection.ImmutableList;


/**
 * Binary feature that returns zero iff a certain Taclet app has not already
 * been performed. Contrary to <code>NonDuplicateAppFeature</code>, this feature
 * is also able to handle failing meta-constructs correctly (these constructs
 * return equal, but not identical formulas in case of a failure), but is less
 * efficient. It is also modulo position.
 */
public class StrictEqNonDuplicateAppFeature extends AbstractNonDuplicateAppFeature {

    public static final Feature INSTANCE = new StrictEqNonDuplicateAppFeature();

    private StrictEqNonDuplicateAppFeature() {}

    public boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";

        if (!app.ifInstsComplete())
            return true;

        return noDuplicateFindTaclet(app, pos, goal);
    }

    protected boolean sameApplication(RuleApp ruleCmp,
            TacletApp newApp,
            PosInOccurrence newPio) {
        // compare the rules
        if (newApp.rule() != ruleCmp.rule()) {
            return false;
        }

        final TacletApp cmp = (TacletApp) ruleCmp;

        // compare the position of application
        if (newPio != null) {
            if (!(cmp instanceof PosTacletApp))
                return false;
            final PosInOccurrence oldPio = cmp.posInOccurrence();
            if (!comparePio(newApp, cmp, newPio, oldPio))
                return false;
        }


        // compare the if-sequent instantiations
        final ImmutableList<IfFormulaInstantiation> newAppIfFmlInstantiations =
            newApp.ifFormulaInstantiations();
        final ImmutableList<IfFormulaInstantiation> cmpIfFmlInstantiations =
            cmp.ifFormulaInstantiations();
        if (newAppIfFmlInstantiations == null
                || cmpIfFmlInstantiations == null) {
            if (newAppIfFmlInstantiations != null
                    || cmpIfFmlInstantiations != null) {
                return false;
            }
        } else {

            final Iterator<IfFormulaInstantiation> it0 =
                newAppIfFmlInstantiations.iterator();
            final Iterator<IfFormulaInstantiation> it1 =
                cmpIfFmlInstantiations.iterator();

            while (it0.hasNext()) {
                // this test should be improved
                if (!it0.next().getConstrainedFormula().formula().equalsModIrrelevantTermLabels(
                    it1.next().getConstrainedFormula().formula()))
                    return false;
            }
        }

        return equalInterestingInsts(newApp.instantiations(), cmp.instantiations());
    }

    protected boolean semiSequentContains(Semisequent semisequent,
            SequentFormula cfma) {

        return semisequent.containsEqual(cfma);
    }

    protected boolean comparePio(TacletApp newApp,
            TacletApp oldApp,
            PosInOccurrence newPio, PosInOccurrence oldPio) {
        final Term newFocus = newPio.subTerm();
        final Term oldFocus = oldPio.subTerm();
        if (!newFocus.equalsModIrrelevantTermLabels(oldFocus)) {
            return false;
        }

        if (newFocus.isRigid()) {
            return true;
        }

        final ImmutableList<SVInstantiations.UpdateLabelPair> oldUpdateContext =
            oldApp.instantiations().getUpdateContext();
        final ImmutableList<SVInstantiations.UpdateLabelPair> newUpdateContext =
            newApp.instantiations().getUpdateContext();
        return oldUpdateContext.equals(newUpdateContext);
    }
}
