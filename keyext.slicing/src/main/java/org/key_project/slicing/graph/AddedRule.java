/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.graph;

import java.util.Objects;

import de.uka.ilkd.key.proof.BranchLocation;

/**
 * Graph node that represents a rule added by some rule application.
 *
 * @author Arne Keller
 */
public class AddedRule extends GraphNode {
    /**
     * The name of the added rule.
     */
    public final String name;

    /**
     * Construct a new graph node for a dynamically added rule.
     *
     * @param name the name of the rule (must be unique per proof)
     */
    public AddedRule(String name) {
        super(BranchLocation.ROOT); // branch location does not matter since the rule name is
                                    // unique
        this.name = name;
    }

    @Override
    public GraphNode popLastBranchID() {
        return this;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        AddedRule addedRule = (AddedRule) o;
        return Objects.equals(name, addedRule.name);
    }

    @Override
    public int hashCode() {
        return Objects.hash(name);
    }

    @Override
    public String toString(boolean abbreviated, boolean omitBranch) {
        return "added rule " + name;
    }
}
