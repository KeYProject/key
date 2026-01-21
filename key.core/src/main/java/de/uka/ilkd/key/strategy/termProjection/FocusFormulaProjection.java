package de.uka.ilkd.key.strategy.termProjection;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

public class FocusFormulaProjection implements ProjectionToTerm {

    public static final ProjectionToTerm INSTANCE = new FocusFormulaProjection();

    private FocusFormulaProjection() {}

    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal) {
        assert pos != null : "Projection is only applicable to rules with find";

        return pos.sequentFormula().formula();
    }

}
