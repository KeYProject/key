/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

import org.key_project.logic.Term;
import org.key_project.logic.Visitor;
import org.key_project.logic.op.Operator;
import org.key_project.rusty.logic.op.ElementaryUpdate;

import org.jspecify.annotations.NonNull;

/**
 * Collects all operators occurring in the traversed term.
 */
public class OpCollector implements Visitor<@NonNull Term> {
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
