/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op.sv;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.UpdateableOperator;
import org.key_project.rusty.logic.ProgramConstruct;
import org.key_project.rusty.logic.sort.ProgramSVSort;

import org.jspecify.annotations.NonNull;

public final class ProgramSV extends OperatorSV
        implements SyntaxElement, UpdateableOperator, ProgramConstruct {
    private final boolean isListSV;

    /**
     * creates a new SchemaVariable used as a placeholder for program constructs
     *
     * @param name the Name of the SchemaVariable allowed to match a list of program constructs
     */
    ProgramSV(Name name, ProgramSVSort s, boolean isListSV) {
        super(name, s, false, false);
        this.isListSV = isListSV;
    }

    public boolean isListSV() {
        return isListSV;
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("ProgramSV " + this + " has no children");
    }

    @Override
    public int getChildCount() {
        return 0;
    }
}
