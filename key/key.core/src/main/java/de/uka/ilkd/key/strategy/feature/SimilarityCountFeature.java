package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;


/**
 * A feature that computes the depth of the find-position of a taclet (top-level
 * positions have depth zero or if not a find taclet) 
 * 
 * TODO: eliminate this class and use term features instead
 */
public class SimilarityCountFeature implements Feature {

    private ProjectionToTerm first;
    private ProjectionToTerm second;

    public static Feature create(ProjectionToTerm first, ProjectionToTerm second) {
        return new SimilarityCountFeature(first, second);
    }

    private SimilarityCountFeature(ProjectionToTerm first, ProjectionToTerm second) {
        this.first = first;
        this.second = second;
    }
    
    public RuleAppCost computeCost ( RuleApp app, PosInOccurrence pos, Goal goal ) {
        Term fst = first.toTerm(app, pos, goal);
        Term snd = second.toTerm(app, pos, goal);

        if (fst.arity() != snd.arity()) {
            return NumberRuleAppCost.getZeroCost();
        }
        int count = 0;
        for (int i = 0; i<fst.arity();i++) {
            if (fst.sub(i).equalsModRenaming(snd.sub(i))) {
                count += 1;
            }
        }
        return NumberRuleAppCost.create(count);
    }

}