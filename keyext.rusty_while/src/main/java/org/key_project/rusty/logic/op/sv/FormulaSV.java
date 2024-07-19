package org.key_project.rusty.logic.op.sv;

import org.jspecify.annotations.NonNull;
import org.key_project.logic.Name;
import org.key_project.logic.TerminalSyntaxElement;
import org.key_project.rusty.logic.RustyDLTheory;

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
}
