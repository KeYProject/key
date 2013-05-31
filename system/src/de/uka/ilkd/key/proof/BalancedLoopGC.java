// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;

/**
 * This goal chooser takes care of a balanced unwinding of loops
 * acorss different proof branches. 
 * 
 * Selects only goals on which no loop expand rule will be applied
 * next. Then when no other goals are left it is done the other way
 * round until all loops have been expanded. This implements a
 * rudimentary fairness measure for symbolic execution for
 * test case generation purposes preventing that shorter execution
 * paths through a loop body are favoured over longer ones. 
 */
public class BalancedLoopGC extends DefaultGoalChooser {
    
    private boolean split = false;
    
    /**
     * @return the next goal a taclet should be applied to
     */
    public Goal getNextGoal () {
        Goal result;
        if(selectedList.isEmpty()) return null;
        selectedList = rotateList ( selectedList );
        Goal first = selectedList.head();
        RuleApp next;
        do{
            result = selectedList.head();
            next = result.getRuleAppManager().peekNext();
            selectedList = rotateList ( selectedList );
        }while(selectedList.head()!=first && next!=null &&
                (next.rule() instanceof Taclet) &&
                (split^loopExpandCriterion((Taclet) next.rule())));
        if(selectedList.head()==first&& next!=null &&
                (next.rule() instanceof Taclet) &&
                (split^loopExpandCriterion((Taclet) next.rule()))){
            split = !split;
        }

        return result;
    }
    
    protected boolean loopExpandCriterion(Taclet t){
        return ruleSetCriterion(t, "loop_expand");
    }

    protected boolean splitCriterion(Taclet t){
        return t.goalTemplates().size() > 1;
    }

    protected boolean methodExpandCriterion(Taclet t){
        return ruleSetCriterion(t, "method_expand");
    }

    protected boolean ruleSetCriterion(Taclet t, String ruleSetName){
        for (RuleSet ruleSet : t.getRuleSets()) {
            if (ruleSet.name().toString().equals(ruleSetName)) {
                return true;
            }
        }
        return false;
    }
    
    
}
