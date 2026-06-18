/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.logic.op.LocationVariable;

/**
 * A {@link ProgramVariableCollector} that stops as soon as it has found every variable in a given
 * <em>interested</em> set.
 * <p>
 * Collecting all program variables of a large program is the dominant cost of symbolic-execution
 * rule costing (it walks the whole remaining program, repeated once per step -> quadratic). When
 * only a few variables matter -- e.g. the left-hand-side variables of an update being simplified by
 * {@code \dropEffectlessElementaries} -- this collector early-exits once they have all been seen,
 * via the {@link #done()} short-circuit of {@link JavaASTWalker}.
 * <p>
 * Because it stops only when {@code result} already contains all interested variables (or the walk
 * is exhausted), {@code result() ∩ interested} equals the full collection intersected with
 * {@code interested}. All the spec handling of the superclass (loop invariants, block/loop/merge
 * contracts, statement specs) is inherited unchanged, so it stays correct as that evolves.
 */
public class BoundedProgramVariableCollector extends ProgramVariableCollector {

    private final Set<LocationVariable> interested;

    /**
     * @param root the program element to collect from
     * @param services the services
     * @param interested the variables whose presence we want to determine; the walk stops once all
     *        of them have been found
     */
    public BoundedProgramVariableCollector(ProgramElement root, Services services,
            Set<LocationVariable> interested) {
        super(root, services);
        this.interested = interested;
    }

    @Override
    protected boolean done() {
        return result().containsAll(interested);
    }
}
