package de.uka.ilkd.key.symbolic_execution.strategy;

import de.uka.ilkd.key.prover.GoalChooserBuilder;
import de.uka.ilkd.key.prover.GoalChooser;

/**
 * This {@link GoalChooserBuilder} creates a special {@link GoalChooser} for symbolic execution.
 *
 * @author Martin Hentschel
 * @see SymbolicExecutionGoalChooser
 */
public class SymbolicExecutionGoalChooserBuilder implements GoalChooserBuilder {
    /**
     * The name of this goal chooser.
     */
    public static final String NAME = "Symbolic Execution Goal Chooser";

    /**
     * {@inheritDoc}
     */
    @Override
    public GoalChooser create() {
        return new SymbolicExecutionGoalChooser();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public GoalChooserBuilder copy() {
        return new SymbolicExecutionGoalChooserBuilder();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String name() {
        return NAME;
    }
}
