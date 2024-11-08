/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op;

import java.lang.ref.WeakReference;
import java.util.Map;
import java.util.WeakHashMap;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.AbstractSortedOperator;
import org.key_project.logic.op.Modifier;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;

public class SharedRef extends AbstractSortedOperator {
    private static final Map<Sort, WeakReference<SharedRef>> instances = new WeakHashMap<>();

    private SharedRef(Sort sort, Services services) {
        super(new Name("refS_" + sort.name()), new Sort[] { sort },
            services.getMRefManager().getRefSort(sort, false), Modifier.RIGID);
    }

    /**
     * Returns the mut ref operator for the passed left hand side.
     */
    public static SharedRef getInstance(Sort sort, Services services) {
        WeakReference<SharedRef> ref = instances.get(sort);
        SharedRef result = null;
        if (ref != null) {
            result = ref.get();
        }
        if (result == null) {
            result = new SharedRef(sort, services);
            ref = new WeakReference<>(result);
            instances.put(sort, ref);
        }
        return result;
    }

    @Override
    public SyntaxElement getChild(int n) {
        throw new UnsupportedOperationException();
    }

    @Override
    public int getChildCount() {
        return 0;
    }
}
