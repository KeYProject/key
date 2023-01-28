package de.uka.ilkd.key.prover;

/**
 * interface to be implemented by builders returning a goal chooser
 */
public interface GoalChooserBuilder {

    /** returns a new goal chooser */
    GoalChooser create();

    /** returns a clone of this goal chooser */
    GoalChooserBuilder copy();

    /** returns the name of the goal chooser */
    String name();
}
