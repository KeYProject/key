package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.util.collection.ImmutableList;

/**
 * Binary feature that returns zero iff a certain Taclet app has not already been performed
 */
public class NonDuplicateAppFeature extends AbstractNonDuplicateAppFeature {

    public static final Feature INSTANCE = new NonDuplicateAppFeature();

    protected boolean containsRuleApp(ImmutableList<RuleApp> list, TacletApp rapp,
            PosInOccurrence pio) {

        for (RuleApp aList : list) {
            if (sameApplication(aList, rapp, pio)) {
                return true;
            }
        }

        return false;
    }

    public boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        if (!app.ifInstsComplete()) {
            return true;
        }

        if (pos == null) {
            return !containsRuleApp(goal.appliedRuleApps(), app, pos);
        }

        return noDuplicateFindTaclet(app, pos, goal);
    }

    protected boolean comparePio(TacletApp newApp, TacletApp oldApp, PosInOccurrence newPio,
            PosInOccurrence oldPio) {
        return oldPio.equals(newPio);
    }

    protected boolean semiSequentContains(Semisequent semisequent, SequentFormula cfma) {
        return semisequent.contains(cfma);
    }
}
