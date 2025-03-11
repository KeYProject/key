/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.op.LocationVariable;

public class SingleRenamingTable extends RenamingTable {

    final SourceElement oldVar;
    final SourceElement newVar;

    public SingleRenamingTable(SourceElement oldVar, SourceElement newVar) {
        this.oldVar = oldVar;
        this.newVar = newVar;
    }

    public SourceElement getRenaming(SourceElement se) {
        if (se.equals(oldVar)) {
            return newVar;
        }
        return null;
    }

    public Iterator<SourceElement> getRenamingIterator() {
        return new SingleIterator(oldVar);
    }

    public String toString() {
        LocationVariable ov = (LocationVariable) oldVar;
        LocationVariable nv = (LocationVariable) newVar;
        return ("SingleRenamingTable: " + oldVar + " id: " + System.identityHashCode(ov) + " -> "
            + newVar + " id: " + System.identityHashCode(nv));
    }

    public HashMap<SourceElement, SourceElement> getHashMap() {
        HashMap<SourceElement, SourceElement> hm = new LinkedHashMap<>();
        hm.put(oldVar, newVar);
        return hm;
    }

    private static class SingleIterator implements Iterator<SourceElement> {

        private SourceElement se;

        public SingleIterator(SourceElement se) {
            this.se = se;
        }

        @Override
        public boolean hasNext() {
            return se != null;
        }

        @Override
        public SourceElement next() {
            final SourceElement next = se;
            se = null;
            return next;
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }

}
