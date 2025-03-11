/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.java.SourceElement;



public class MultiRenamingTable extends RenamingTable {

    private final HashMap<? extends SourceElement, ? extends SourceElement> hmap;

    public MultiRenamingTable(HashMap<? extends SourceElement, ? extends SourceElement> hmap) {
        this.hmap = hmap;
    }

    public SourceElement getRenaming(SourceElement se) {
        return hmap.get(se);
    }

    public Iterator<? extends SourceElement> getRenamingIterator() {
        return hmap.keySet().iterator();
    }

    public String toString() {
        return ("MultiRenamingTable: " + hmap);
    }

    public HashMap<? extends SourceElement, ? extends SourceElement> getHashMap() {
        return hmap;
    }

}
