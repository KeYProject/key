/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * Collects all operators occurring in the traversed term.
 */
public class OpCollector implements DefaultVisitor {
    /** the found operators */
    protected final HashSet<Operator> ops;

    /** creates the Op collector */
    public OpCollector() {
        ops = new LinkedHashSet<>();
    }

    @Override
    public void visit(Term t) {
        ops.add(t.op());
        if (t.op() instanceof ElementaryUpdate update) {
            ops.add(update.lhs());
        }
    }

    public boolean contains(Operator op) {
        return ops.contains(op);
    }

    public Set<Operator> ops() {
        return Collections.unmodifiableSet(ops);
    }
}
