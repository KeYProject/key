package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;

public class SortComparisionFeature extends BinaryFeature {

    public final static int SUBSORT = 0;
    
    public static Feature create(ProjectionToTerm s1, ProjectionToTerm s2, int cmp) {
        return new SortComparisionFeature(s1, s2, cmp);
    }
    
    private final ProjectionToTerm s1;
    private final ProjectionToTerm s2;
    private final int comparator;

    /**
     * creates a new comparision term feature
     * @param s
     */
    private SortComparisionFeature(ProjectionToTerm s1, ProjectionToTerm s2, 
            int comparator) {
        this.s1 = s1;
        this.s2 = s2;
        this.comparator = comparator;
    }
    
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {        
        final Sort sort1 = s1.toTerm(app, pos, goal).sort();
        final Sort sort2 = s2.toTerm(app, pos, goal).sort();

        return compare(sort1, sort2);       
    }

    /**
     * @param sort1
     * @param sort2
     * @return
     */
    protected boolean compare(final Sort sort1, final Sort sort2) {
        switch (comparator) {
        case SUBSORT : 
            return sort1.extendsTrans(sort2);
        default:
            return false;
        }
    }

}
