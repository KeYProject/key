/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

public class InverseAnonEventUpdate extends AbstractSortedOperator {


    public static final Operator SINGLETON = new InverseAnonEventUpdate();

    private InverseAnonEventUpdate() {
        super(new Name("\\invAnonEvUp"), new Sort[] { Sort.ANY }, Sort.UPDATE, false);
    }

    public String toString() {
        return "invAnonEvUp";
    }

}
