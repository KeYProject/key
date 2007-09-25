package de.uka.ilkd.key.proof;

/**
 * interface to be implemented by builders returning a 
 * goal chooser
 */
public interface GoalChooserBuilder {

    /** returns a new goal chooser */
    IGoalChooser create();

    /** returns a clone of this goal chooser */
    GoalChooserBuilder copy();
    
    /** returns the name of the goal chooser */
    String name();
}
