/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.ldt.JavaDLTheory;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.sort.Sort;

public class InverseAnonEventUpdate extends AbstractSortedOperator {


    public static final Operator SINGLETON = new InverseAnonEventUpdate();

    private InverseAnonEventUpdate() {
        super(new Name("\\invAnonEvUp"), new Sort[] { JavaDLTheory.ANY }, JavaDLTheory.UPDATE,
            false);
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("Inverse anon updates do not have child elements");
    }

    public String toString() {
        return "invAnonEvUp";
    }

}
