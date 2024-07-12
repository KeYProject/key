package org.key_project.rusty.logic.op;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.AbstractSortedOperator;
import org.key_project.logic.op.Modifier;
import org.key_project.logic.op.UpdateableOperator;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.logic.RustyDLTheory;

import java.lang.ref.WeakReference;
import java.util.WeakHashMap;

public class ElementaryUpdate extends AbstractSortedOperator {

    private static final WeakHashMap<UpdateableOperator, WeakReference<ElementaryUpdate>> instances =
            new WeakHashMap<>();

    private final UpdateableOperator lhs;

    private ElementaryUpdate(UpdateableOperator lhs) {
        super(new Name("elem-update(" + lhs + ")"), new Sort[] { lhs.sort() }, RustyDLTheory.UPDATE,
                Modifier.NONE);
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
