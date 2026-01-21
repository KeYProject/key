package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * A schema variable that is used as placeholder for formulas.
 */
public final class FormulaSV extends AbstractSV {

    /**
     * @param name the name of the SchemaVariable
     * @param isRigid true iff this SV may only match rigid formulas
     */
    FormulaSV(Name name, boolean isRigid) {
        super(name, Sort.FORMULA, isRigid, true);
    }

    @Override
    public String toString() {
        return toString("formula");
    }


    @Override
    public String proofToString() {
        return "\\schemaVar \\formula " + name() + ";\n";
    }
}
