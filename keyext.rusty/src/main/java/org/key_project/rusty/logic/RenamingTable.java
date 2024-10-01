package org.key_project.rusty.logic;

import org.key_project.rusty.ast.RustyProgramElement;

import java.util.HashMap;
import java.util.Map;

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
