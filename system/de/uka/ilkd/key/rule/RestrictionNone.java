package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.op.SchemaVariable;

public class RestrictionNone implements Restriction {
    public String getTypeOfRestriction() {
	return "none";
    }

    public SchemaVariable getAttributeVar() {
	return null;
    }
}

