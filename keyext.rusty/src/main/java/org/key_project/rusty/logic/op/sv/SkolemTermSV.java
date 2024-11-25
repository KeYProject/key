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

public class SkolemTermSV extends OperatorSV implements TerminalSyntaxElement {
    /**
     * Creates a new schema variable that is used as placeholder for skolem terms.
     *
     * @param name the Name of the SchemaVariable
     * @param sort the Sort of the SchemaVariable and the matched type allowed to match a list of
     *        program constructs
     */
    SkolemTermSV(Name name, Sort sort) {
        super(name, sort, true, false);
        assert sort != RustyDLTheory.UPDATE;
    }

    @Override
    public @NonNull String toString() {
        return toString(sort() + " skolem term");
    }

    @Override
    public void layout(Layouter<?> l) {
        l.print("\\schemaVar ");
        if (sort() == RustyDLTheory.FORMULA) {
            l.print("\\skolemFormula");
        } else {
            l.print("\\skolemTerm ").print(sort().name().toString());
        }
        l.print(" ").print(name().toString());
    }
}
