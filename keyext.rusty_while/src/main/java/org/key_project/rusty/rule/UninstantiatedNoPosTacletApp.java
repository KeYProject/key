package org.key_project.rusty.rule;

import org.key_project.rusty.Services;
import org.key_project.rusty.logic.PosInOccurrence;

public class UninstantiatedNoPosTacletApp extends NoPosTacletApp {
    UninstantiatedNoPosTacletApp(Taclet taclet) {
        super(taclet);
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.rule.NoPosTacletApp#setupMatchConditions(de.uka.ilkd.key.logic.
     * PosInOccurrence, de.uka.ilkd.key.java.Services, de.uka.ilkd.key.logic.Constraint)
     */
    @Override
    protected MatchConditions setupMatchConditions(PosInOccurrence pos, Services services) {
        if (taclet() instanceof RewriteTaclet rwt) {
            return rwt.checkPrefix(pos,
                    MatchConditions.EMPTY_MATCHCONDITIONS);
        }

        return MatchConditions.EMPTY_MATCHCONDITIONS;
    }
}
