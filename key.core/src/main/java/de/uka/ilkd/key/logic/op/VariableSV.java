package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Schema variable that is instantiated with logical variables.
 */
public final class VariableSV extends AbstractSV implements QuantifiableVariable {

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
    public String toString() {
        return toString("variable");
    }


    @Override
    public String proofToString() {
        return "\\schemaVar \\variables " + sort().name() + " " + name() + ";\n";
    }
}
