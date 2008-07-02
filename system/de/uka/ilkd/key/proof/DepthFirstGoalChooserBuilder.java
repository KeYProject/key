package de.uka.ilkd.key.proof;

public class DepthFirstGoalChooserBuilder implements GoalChooserBuilder {
 
	public static final String NAME = "Depth First Goal Chooser";
	
	public DepthFirstGoalChooserBuilder(){};
	
	public IGoalChooser create() {      
        return new DepthFirstGoalChooser();
    }
    
    public GoalChooserBuilder copy() {        
        return new DepthFirstGoalChooserBuilder();
    }   
    
    public String name() {
        return NAME;
    }
}
