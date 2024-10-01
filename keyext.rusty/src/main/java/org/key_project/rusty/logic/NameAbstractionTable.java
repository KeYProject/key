/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.key_project.logic.Name;

public class NameAbstractionTable {

    /**
     * The order in which symbols are declared in the two terms or programs that are compared. The
     * latest declaration of a symbol will be the first matching entry in the list
     */
    private List<Name> declarations0 = null, declarations1 = null;

    /**
     * adds the given two elements to the table
     *
     * @param name1 Name to be added
     * @param name2 Name to be added
     */
    public void add(Name name1, Name name2) {
        if (declarations0 == null) {
            declarations0 = new LinkedList<>();
            declarations1 = new LinkedList<>();
        }

        declarations0.add(0, name1);
        declarations1.add(0, name2);
    }

    /**
     * tests if the given elements have been assigned to the same abstract name.
     *
     * @param name1 first name to test
     * @param name2 second name to test
     * @returns true if {@code name1} and {@code name2} are the same abstract name
     */
    public boolean sameAbstractName(Name name1, Name name2) {
        if (declarations0 != null) {
            final Iterator<Name> it0 = declarations0.iterator();
            final Iterator<Name> it1 = declarations1.iterator();

            while (it0.hasNext()) {
                // both lists are assumed to hold the same number of elements
                final Object o0 = it0.next();
                final Object o1 = it1.next();

                if (name1.equals(o0)) {
                    return name2.equals(o1);
                } else if (name2.equals(o1)) {
                    return false;
                }
            }
        }

        return name1.equals(name2);
    }
}
