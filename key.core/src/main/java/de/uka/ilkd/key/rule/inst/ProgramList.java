/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.inst;

import de.uka.ilkd.key.java.ProgramElement;

import org.key_project.logic.SyntaxElement;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NonNull;

public class ProgramList implements SyntaxElement {

    private final @NonNull ImmutableArray<ProgramElement> list;


    public ProgramList(@NonNull ImmutableArray<ProgramElement> list) {
        assert list != null
                : "Constructor of ProgramList must" + " not be called with null argument";
        this.list = list;
    }

    public @NonNull ImmutableArray<ProgramElement> getList() {
        return list;
    }

    @Override
    public boolean equals(@org.jspecify.annotations.Nullable Object o) {
        if (!(o instanceof ProgramList)) {
            return false;
        }
        return list.equals(((ProgramList) o).list);
    }

    public int hashCode() {
        return list.hashCode();
    }


    @Override
    public @NonNull SyntaxElement getChild(int n) {
        return list.get(n);
    }

    @Override
    public int getChildCount() {
        return list.size();
    }
}
