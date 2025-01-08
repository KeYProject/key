/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op.sv;

import org.key_project.logic.Name;
import org.key_project.logic.TerminalSyntaxElement;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.logic.RustyDLTheory;
import org.key_project.rusty.pp.Layouter;

import org.jspecify.annotations.NonNull;

public class TermSV extends OperatorSV implements TerminalSyntaxElement {
    /**
     * @param name the name of the schema variable
     * @param sort the sort of the schema variable
     * @param isRigid true iff this schema variable may only match rigid terms
     * @param isStrict boolean indicating if the schema variable is declared as strict forcing exact
     *        type match
     */
    TermSV(Name name, Sort sort, boolean isRigid, boolean isStrict) {
        super(name, sort, isRigid, isStrict);
        assert sort != RustyDLTheory.FORMULA;
        assert sort != RustyDLTheory.UPDATE;
    }

    @Override
    public @NonNull String toString() {
        return toString(sort() + " term");
    }

    @Override
    public boolean isTerm() {
        return true;
    }

    @Override
    public void layout(Layouter<?> l) {
        l.print("\\schemaVar \\term ").print(sort().name().toString()).print(" ")
                .print(name().toString());
    }
}
