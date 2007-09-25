package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.op.SchemaVariable;

public interface Restriction {
    public String getTypeOfRestriction();

    public SchemaVariable getAttributeVar();
}
