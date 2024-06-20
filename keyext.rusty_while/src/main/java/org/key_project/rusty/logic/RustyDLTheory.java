/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.logic.sort.SortImpl;

public class RustyDLTheory {
    /**
     * Formulas are represented as "terms" of this sort.
     */
    public static final Sort FORMULA = new SortImpl(new Name("Formula"));
    /**
     * Updates are represented as "terms" of this sort.
     */
    public static final Sort UPDATE = new SortImpl(new Name("Update"));
    /**
     * Any is a supersort of all sorts.
     */
    public static final Sort ANY = new SortImpl(new Name("any"));
}
