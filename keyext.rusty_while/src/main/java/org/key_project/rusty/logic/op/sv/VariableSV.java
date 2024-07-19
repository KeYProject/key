package org.key_project.rusty.logic.op.sv;

import org.jspecify.annotations.NonNull;
import org.key_project.logic.Name;
import org.key_project.logic.TerminalSyntaxElement;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;

public class VariableSV extends OperatorSV implements QuantifiableVariable, TerminalSyntaxElement {
    /**
     * Creates a new SchemaVariable that is used as placeholder for bound(quantified) variables.
     *
     * @param name the Name of the SchemaVariable
     * @param sort the Sort of the SchemaVariable and the matched type
     */
    VariableSV(Name name, Sort sort) {
        super(name, sort, true, false);
    }


    @Override
    public @NonNull String toString() {
        return toString("variable");
    }
}
