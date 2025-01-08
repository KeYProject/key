/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op.sv;

import org.key_project.logic.Name;
import org.key_project.logic.TerminalSyntaxElement;
import org.key_project.rusty.logic.RustyDLTheory;
import org.key_project.rusty.pp.Layouter;

import org.jspecify.annotations.NonNull;

public class FormulaSV extends OperatorSV implements TerminalSyntaxElement {
    /**
     * @param name the name of the SchemaVariable
     * @param isRigid true iff this SV may only match rigid formulas
     */
    FormulaSV(Name name, boolean isRigid) {
        super(name, RustyDLTheory.FORMULA, isRigid, true);
    }

    @Override
    public @NonNull String toString() {
        return toString("formula");
    }

    @Override
    public boolean isFormula() {
        return true;
    }

    @Override
    public void layout(Layouter<?> layouter) {
        layouter.print("\\schemaVar \\formula ").print(name().toString());
    }
}
