/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.ldt.JavaDLTheory;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.sort.Sort;

/**
 * This class defines an update that represents a sequence (possibly empty) of events.
 * It takes as argument the timestamp t of the event issued directly before. This means
 * if the update stands for sequence of length >= 1, the first event in this sequence would have
 * the timestamp t+1.
 *
 * @author Asma
 *
 */
public class AnonEventUpdate extends AbstractSortedOperator {

    /*
     * private static WeakHashMap<Sort, AnonEventUpdate> anonEventUpdates =
     * new WeakHashMap<>();
     *
     * public static AnonEventUpdate getAnonEventUpdateFor(Services s) {
     * Sort intSort = s.getTypeConverter().getIntegerLDT().targetSort();
     * AnonEventUpdate evUpdate = null;
     * synchronized(AnonEventUpdate.class) {
     * evUpdate = anonEventUpdates.get(intSort);
     * if (evUpdate == null) {
     * evUpdate = new AnonEventUpdate(intSort);
     * anonEventUpdates.put(intSort, evUpdate);
     * }
     * }
     * return evUpdate;
     * }
     */

    public static final Operator SINGLETON = new AnonEventUpdate();

    private AnonEventUpdate() {
        super(new Name("\\anonEvUp"), new Sort[] { /* int, but no order */JavaDLTheory.ANY },
            JavaDLTheory.UPDATE,
            false);
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("Anon event updates do not have child elements");
    }

    public String toString() {
        return "anonEvUp";
    }

}
