package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.op.SchemaVariable;

public class RestrictionInt implements Restriction {
    public String getTypeOfRestriction() {
	return "int";
    }

    public SchemaVariable getAttributeVar() {
	return null;
    }
}

