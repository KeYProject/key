package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletGoalTemplate;

public class MatchHelper extends FindTaclet {

    @Override
    protected void applyAdd(Sequent add, Goal goal, PosInOccurrence posOfFind,
	    Services services, MatchConditions matchCond) {
	// TODO Auto-generated method stub

    }

    @Override
    protected void applyReplacewith(TacletGoalTemplate gt, Goal goal,
	    PosInOccurrence posOfFind, Services services,
	    MatchConditions matchCond) {
	// TODO Auto-generated method stub

    }

    @Override
    protected boolean ignoreTopLevelUpdates() {
	// TODO Auto-generated method stub
	return false;
    }

    @Override
    protected Taclet setName(String s) {
	// TODO Auto-generated method stub
	return null;
    }

}
