/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op;

import java.lang.ref.WeakReference;
import java.util.WeakHashMap;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.AbstractSortedOperator;
import org.key_project.logic.op.Modifier;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.Place;

public class MutRef extends AbstractSortedOperator {
    private static final WeakHashMap<Place, WeakReference<MutRef>> instances =
        new WeakHashMap<>();

    private final Place place;

    private MutRef(Place p, Services services) {
        super(new Name("refM<" + p + ">"), new Sort[] {},
            services.getMRefManager().getMRefSort(p.sort()),
            Modifier.NONE);
        this.place = p;
    }

    /**
     * Returns the mut ref operator for the passed left hand side.
     */
    public static MutRef getInstance(Place place, Services services) {
        WeakReference<MutRef> ref = instances.get(place);
        MutRef result = null;
        if (ref != null) {
            result = ref.get();
        }
        if (result == null) {
            result = new MutRef(place, services);
            ref = new WeakReference<>(result);
            instances.put(place, ref);
        }
        return result;
    }

    public Place getPlace() {
        return place;
    }

    @Override
    public SyntaxElement getChild(int n) {
        throw new UnsupportedOperationException();
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public String toString() {
        return "refM<" + place + ">";
    }
}
