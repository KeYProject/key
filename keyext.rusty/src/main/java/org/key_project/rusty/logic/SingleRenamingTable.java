/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import java.util.HashMap;
import java.util.LinkedHashMap;

import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.logic.op.ProgramVariable;

public class SingleRenamingTable extends RenamingTable {
    final RustyProgramElement oldVar;
    final RustyProgramElement newVar;

    public SingleRenamingTable(RustyProgramElement oldVar, RustyProgramElement newVar) {
        this.oldVar = oldVar;
        this.newVar = newVar;
    }

    public RustyProgramElement getRenaming(RustyProgramElement se) {
        if (se.equals(oldVar)) {
            return newVar;
        }
        return null;
    }

    public String toString() {
        var ov = (ProgramVariable) oldVar;
        var nv = (ProgramVariable) newVar;
        return ("SingleRenamingTable: " + oldVar + " id: " + System.identityHashCode(ov) + " -> "
            + newVar + " id: " + System.identityHashCode(nv));
    }

    public HashMap<RustyProgramElement, RustyProgramElement> getHashMap() {
        HashMap<RustyProgramElement, RustyProgramElement> hm = new LinkedHashMap<>();
        hm.put(oldVar, newVar);
        return hm;
    }
}
