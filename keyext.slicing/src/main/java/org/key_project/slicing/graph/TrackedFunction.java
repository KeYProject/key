/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.graph;

import java.util.Objects;

import de.uka.ilkd.key.proof.BranchLocation;

import org.key_project.logic.op.Function;

/**
 * A skolem constant tracked in the dependency graph.
 *
 * @author Arne Keller
 */
public class TrackedFunction extends GraphNode {
    private final Function function;

    public TrackedFunction(Function f, BranchLocation loc) {
        super(loc);

        this.function = f;
    }

    @Override
    public GraphNode popLastBranchID() {
        return new TrackedFunction(function, getBranchLocation().removeLast());
    }

    @Override
    public String toString(boolean abbreviated, boolean omitBranch) {
        return "variable " + function.toString();
    }

    public Function getFunction() {
        return function;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }

        TrackedFunction that = (TrackedFunction) o;

        return Objects.equals(function, that.function);
    }

    @Override
    public int hashCode() {
        return function != null ? function.hashCode() : 0;
    }
}
