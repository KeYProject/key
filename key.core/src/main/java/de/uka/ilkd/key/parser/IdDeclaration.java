/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser;

import de.uka.ilkd.key.logic.sort.Sort;


public class IdDeclaration {

    private final String name;
    private final Sort sort;

    public IdDeclaration(String p_name, Sort p_sort) {
        name = p_name;
        sort = p_sort;
    }

    public String getName() {
        return name;
    }

    public Sort getSort() {
        return sort;
    }

}
