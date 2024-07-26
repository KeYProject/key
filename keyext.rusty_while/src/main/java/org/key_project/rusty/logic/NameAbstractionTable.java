/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.key_project.rusty.ast.RustyProgramElement;

public class NameAbstractionTable {

    /**
     * The order in which symbols are declared in the two terms or programs that are compared. The
     * latest declaration of a symbol will be the first matching entry in the list
     */
    private List<RustyProgramElement> declarations0 = null, declarations1 = null;

    /**
     * adds the given two elements to the table
     *
     * @param pe1 RustyProgramElement to be added
     * @param pe2 RustyProgramElement to be added
     */
    public void add(RustyProgramElement pe1, RustyProgramElement pe2) {
        if (declarations0 == null) {
            declarations0 = new LinkedList<>();
            declarations1 = new LinkedList<>();
        }

        declarations0.add(0, pe1);
        declarations1.add(0, pe2);
    }

    /**
     * tests if the given elements have been assigned to the same abstract name.
     *
     * @param pe0 RustyProgramElement
     * @param pe1 RustyProgramElement
     * @returns true if the pe1 and pe2 have been assigned to the same name
     */
    public boolean sameAbstractName(RustyProgramElement pe0, RustyProgramElement pe1) {
        if (declarations0 != null) {
            final Iterator<RustyProgramElement> it0 = declarations0.iterator();
            final Iterator<RustyProgramElement> it1 = declarations1.iterator();

            while (it0.hasNext()) {
                // both lists are assumed to hold the same number of elements
                final Object o0 = it0.next();
                final Object o1 = it1.next();

                if (pe0.equals(o0)) {
                    return pe1.equals(o1);
                } else if (pe1.equals(o1)) {
                    return false;
                }
            }
        }

        return pe0.equals(pe1);
    }
}
