/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import java.util.HashMap;

import org.key_project.rusty.ast.RustyProgramElement;

public class MultiRenamingTable extends RenamingTable {
    private final HashMap<? extends RustyProgramElement, ? extends RustyProgramElement> hmap;

    public MultiRenamingTable(
            HashMap<? extends RustyProgramElement, ? extends RustyProgramElement> hmap) {
        this.hmap = hmap;
    }

    public RustyProgramElement getRenaming(RustyProgramElement se) {
        return hmap.get(se);
    }

    public String toString() {
        return ("MultiRenamingTable: " + hmap);
    }

    public HashMap<? extends RustyProgramElement, ? extends RustyProgramElement> getHashMap() {
        return hmap;
    }
}
