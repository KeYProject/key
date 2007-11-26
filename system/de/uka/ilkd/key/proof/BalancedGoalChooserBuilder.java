package de.uka.ilkd.key.proof;

/**
 * builds a goal chooser taking care that loops are equally often 
 * unwound across different branches 
 *
 */
public class BalancedGoalChooserBuilder implements GoalChooserBuilder {

    public static final String NAME = "Balanced Goal Chooser";

    
    public BalancedGoalChooserBuilder() {}
    
    public IGoalChooser create() {        
        return new BalancedLoopGC();
    }

    public GoalChooserBuilder copy() {
        return new BalancedGoalChooserBuilder();
    }

    public String name() {
        return NAME;
    }

}
