package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.rule.IteratorOfRuleSet;
import de.uka.ilkd.key.rule.RuleApp;
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
        IteratorOfRuleSet it = t.getRuleSets().iterator();
        while(it.hasNext()){
            if(it.next().name().toString().equals(ruleSetName)){
                return true;
            }
        }
        return false;
    }
    
    
}
