/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.strategy;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.prover.engine.GoalChooser;
import org.key_project.prover.engine.GoalChooserBuilder;

/**
 * This {@link GoalChooserBuilder} creates a special {@link GoalChooser} for symbolic execution.
 *
 * @author Martin Hentschel
 * @see SymbolicExecutionGoalChooser
 */
public class SymbolicExecutionGoalChooserBuilder implements GoalChooserBuilder<Proof, Goal> {
    /**
     * The name of this goal chooser.
     */
    public static final String NAME = "Symbolic Execution Goal Chooser";

    /**
     * {@inheritDoc}
     */
    @Override
    public GoalChooser<Proof, Goal> create() {
        return new SymbolicExecutionGoalChooser();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public GoalChooserBuilder<Proof, Goal> copy() {
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
