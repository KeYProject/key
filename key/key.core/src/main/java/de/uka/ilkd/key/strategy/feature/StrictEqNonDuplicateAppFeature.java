package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
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
    
    public boolean filter (TacletApp app, PosInOccurrence pos, Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";

        if ( !app.ifInstsComplete () ) return true;

        return noDuplicateFindTaclet ( app, pos, goal );
    }

    protected boolean semiSequentContains(Semisequent semisequent,
                                          SequentFormula cfma) {

        return semisequent.containsEqual ( cfma );
    }

    protected boolean comparePio(TacletApp newApp,
                                 TacletApp oldApp,
                                 PosInOccurrence newPio, PosInOccurrence oldPio) {
        final Term newFocus = newPio.subTerm ();
        final Term oldFocus = oldPio.subTerm ();
        if (!newFocus.equalsModIrrelevantTermLabels(oldFocus)) {
            return false;
        }

        if (newFocus.isRigid ()) {
            return true;
        }

        final ImmutableList<SVInstantiations.UpdateLabelPair> oldUpdateContext =
            oldApp.instantiations().getUpdateContext();
        final ImmutableList<SVInstantiations.UpdateLabelPair> newUpdateContext =
            newApp.instantiations().getUpdateContext();
        return oldUpdateContext.equals(newUpdateContext);
    }
}