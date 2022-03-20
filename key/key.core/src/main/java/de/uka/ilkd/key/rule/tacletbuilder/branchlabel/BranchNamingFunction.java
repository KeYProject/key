package de.uka.ilkd.key.rule.tacletbuilder.branchlabel;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * @author Alexander Weigl
 * @version 1 (1/15/22)
 */
public interface BranchNamingFunction {
    String getName(Services services, SequentChangeInfo currentSequent,
                   TacletApp tacletApp, MatchConditions matchConditions);
}
