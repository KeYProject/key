package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.op.SchemaVariable;

public class RestrictionBool implements Restriction {
    public String getTypeOfRestriction() {
	return "bool";
    }

    public SchemaVariable getAttributeVar() {
	return null;
    }
}

