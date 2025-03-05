/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import java.lang.ref.WeakReference;
import java.util.WeakHashMap;

import de.uka.ilkd.key.ldt.JavaDLTheory;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.sort.Sort;


/**
 * Class of operators for elementary updates, i.e., updates of the form "x := t". There is one such
 * operator for every left hand side "x". Each of these operator is unary, accepting a single
 * argument "t".
 */
public final class ElementaryUpdate extends AbstractSortedOperator {

    private static final WeakHashMap<UpdateableOperator, WeakReference<ElementaryUpdate>> instances =
        new WeakHashMap<>();


    private final UpdateableOperator lhs;


    private ElementaryUpdate(UpdateableOperator lhs) {
        super(new Name("elem-update(" + lhs + ")"), new Sort[] { lhs.sort() }, JavaDLTheory.UPDATE,
            false);
        this.lhs = lhs;
        assert lhs.arity() == 0;
    }


    /**
     * Returns the elementary update operator for the passed left hand side.
     */
    public static ElementaryUpdate getInstance(UpdateableOperator lhs) {
        WeakReference<ElementaryUpdate> ref = instances.get(lhs);
        ElementaryUpdate result = null;
        if (ref != null) {
            result = ref.get();
        }
        if (result == null) {
            result = new ElementaryUpdate(lhs);
            ref = new WeakReference<>(result);
            instances.put(lhs, ref);
        }
        return result;
    }


    /**
     * Returns the left hand side of this elementary update operator.
     */
    public UpdateableOperator lhs() {
        return lhs;
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public SyntaxElement getChild(int n) {
        if (n == 0)
            return lhs;
        throw new IndexOutOfBoundsException("Elementary updates only contain 1 child");
    }
}
