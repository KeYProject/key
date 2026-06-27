/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents a list of goal specifications.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * goal_specs: goal_spec (COMMA goal_spec)*;
 * }</pre>
 */
@NullMarked
public class GoalSpecs extends BaseAstNode {
    private final List<GoalSpec> specs;

    public GoalSpecs(Position position, List<GoalSpec> specs) {
        super(position);
        this.specs = specs;
        for (GoalSpec s : specs) {
            setChildParent(s);
        }
    }

    public List<GoalSpec> getSpecs() {
        return specs;
    }
}