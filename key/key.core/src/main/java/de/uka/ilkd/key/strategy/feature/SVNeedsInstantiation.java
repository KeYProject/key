package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;

public class SVNeedsInstantiation extends InstantiatedSVFeature {

    public static Feature create(String svName) {
        return new SVNeedsInstantiation(new Name(svName));
    }

    private Name svName;
    
    protected SVNeedsInstantiation(Name svName) {
        super(svName);
        this.svName = svName;
    }
    
    @Override
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        boolean res = super.filter(app, pos, goal);
        if (res == false) {
            for (SchemaVariable sv : app.uninstantiatedVars()) {
                if (sv.name().equals(svName)) { 
                    return true;
                }
            }
        }
        return false;
    }
    
    
}
