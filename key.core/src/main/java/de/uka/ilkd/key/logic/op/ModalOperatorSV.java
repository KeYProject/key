package de.uka.ilkd.key.logic.op;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Schema variable matching modal operators.
 */
public final class ModalOperatorSV extends AbstractSV {

    /**
     * the set of modalities this sv can match
     */
    private final ImmutableSet<Modality> modalities;


    /**
     * creates a new SchemaVariable that is used as placeholder for modal operators.
     *
     * @param name the Name of the SchemaVariable
     * @param modalities modal operators matched by this SV
     */
    ModalOperatorSV(Name name, ImmutableSet<Modality> modalities) {
        super(name, new Sort[] { Sort.FORMULA }, Sort.FORMULA, false, false);
        this.modalities = modalities;
    }

    /**
     * returns an unmodifiable set of operators this schemavariable can match
     */
    public ImmutableSet<Modality> getModalities() {
        return modalities;
    }


    @Override
    public String toString() {
        return toString(" (modal operator)");
    }


    @Override
    public String proofToString() {
        StringBuffer result = new StringBuffer();
        result.append("\\schemaVar \\modalOperator {");
        boolean first = true;
        for (Modality modality : modalities) {
            if (!first) {
                result.append(", ");
            } else {
                first = false;
            }
            result.append(modality);
        }
        result.append("} ").append(name()).append(";\n");
        return result.toString();
    }
}
