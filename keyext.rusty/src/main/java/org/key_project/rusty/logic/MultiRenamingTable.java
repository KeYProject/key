package org.key_project.rusty.logic;

import org.key_project.rusty.ast.RustyProgramElement;

import java.util.HashMap;

public class MultiRenamingTable extends RenamingTable {
    private final HashMap<? extends RustyProgramElement, ? extends RustyProgramElement> hmap;

    public MultiRenamingTable(HashMap<? extends RustyProgramElement, ? extends RustyProgramElement> hmap) {
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
