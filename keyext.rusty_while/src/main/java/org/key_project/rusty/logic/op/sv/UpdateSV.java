package org.key_project.rusty.logic.op.sv;

import org.jspecify.annotations.NonNull;
import org.key_project.logic.Name;
import org.key_project.logic.TerminalSyntaxElement;
import org.key_project.rusty.logic.RustyDLTheory;

public class UpdateSV extends OperatorSV implements TerminalSyntaxElement {
    UpdateSV(Name name) {
        super(name, RustyDLTheory.UPDATE, false, true);
    }


    @Override
    public  @NonNull String toString() {
        return toString("update");
    }
}
