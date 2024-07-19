package org.key_project.rusty.logic.op.sv;

import org.jspecify.annotations.NonNull;
import org.key_project.logic.Name;
import org.key_project.logic.TerminalSyntaxElement;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.logic.RustyDLTheory;

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
    public  @NonNull String toString() {
        return toString(sort().toString() + " term");
    }
}
