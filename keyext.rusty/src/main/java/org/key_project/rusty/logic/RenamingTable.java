/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import java.util.HashMap;
import java.util.Map;

import org.key_project.rusty.ast.RustyProgramElement;

public abstract class RenamingTable {
    public abstract RustyProgramElement getRenaming(RustyProgramElement pe);

    public static RenamingTable getRenamingTable(
            HashMap<? extends RustyProgramElement, ? extends RustyProgramElement> hmap) {
        if (hmap.isEmpty()) {
            return null;
        }
        if (hmap.size() == 1) {
            Map.Entry<? extends RustyProgramElement, ? extends RustyProgramElement> entry =
                hmap.entrySet().iterator().next();
            return new SingleRenamingTable(entry.getKey(), entry.getValue());
        } else {
            return new MultiRenamingTable(hmap);
        }
    }

    public abstract HashMap<? extends RustyProgramElement, ? extends RustyProgramElement> getHashMap();
}
