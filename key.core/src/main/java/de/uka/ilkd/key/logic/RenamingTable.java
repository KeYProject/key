/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map.Entry;

import de.uka.ilkd.key.java.SourceElement;


public abstract class RenamingTable {

    public abstract SourceElement getRenaming(SourceElement se);

    public abstract Iterator<? extends SourceElement> getRenamingIterator();

    public static RenamingTable getRenamingTable(
            HashMap<? extends SourceElement, ? extends SourceElement> hmap) {
        if (hmap.size() == 0) {
            return null;
        }
        if (hmap.size() == 1) {
            Entry<? extends SourceElement, ? extends SourceElement> entry =
                hmap.entrySet().iterator().next();
            return new SingleRenamingTable(entry.getKey(), entry.getValue());
        } else {
            return new MultiRenamingTable(hmap);
        }
    }

    public abstract HashMap<? extends SourceElement, ? extends SourceElement> getHashMap();

}
