package de.uka.ilkd.key.proof;

/**
 * creates the default goal chooser used in KeY
 */
public class DefaultGoalChooserBuilder implements GoalChooserBuilder {
    
    public static final String NAME = "Simple Goal Chooser";
    
    public DefaultGoalChooserBuilder() {}
    
    public IGoalChooser create() {      
        return new DefaultGoalChooser();
    }
    
    public String name() {
        return NAME;
    }

    public GoalChooserBuilder copy() {        
        return new DefaultGoalChooserBuilder();
    }    

}
