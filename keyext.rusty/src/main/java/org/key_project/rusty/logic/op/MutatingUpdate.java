/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op;

import java.lang.ref.WeakReference;
import java.util.WeakHashMap;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.Term;
import org.key_project.logic.op.AbstractSortedOperator;
import org.key_project.logic.op.Modifier;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.logic.RustyDLTheory;

import org.jspecify.annotations.NonNull;

public class MutatingUpdate extends AbstractSortedOperator {
    private static final WeakHashMap<Term, WeakReference<MutatingUpdate>> instances =
        new WeakHashMap<>();

    private final Term lhs;

    private MutatingUpdate(Term lhs) {
        super(new Name("mutating-update(" + lhs + ")"), new Sort[] { lhs.sort() },
            RustyDLTheory.UPDATE, Modifier.NONE);
        this.lhs = lhs;
        assert lhs.arity() == 0;
    }

    public Term lhs() {
        return lhs;
    }

    /**
     * Returns the elementary update operator for the passed left hand side.
     */
    public static MutatingUpdate getInstance(Term lhs) {
        WeakReference<MutatingUpdate> ref = instances.get(lhs);
        MutatingUpdate result = null;
        if (ref != null) {
            result = ref.get();
        }
        if (result == null) {
            result = new MutatingUpdate(lhs);
            ref = new WeakReference<>(result);
            instances.put(lhs, ref);
        }
        return result;
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0)
            return lhs;
        throw new IndexOutOfBoundsException("Mutating updates only contain 1 child");
    }
}
