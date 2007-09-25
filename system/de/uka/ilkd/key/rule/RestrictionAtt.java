package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.op.SchemaVariable;


public class RestrictionAtt implements Restriction {
    SchemaVariable AttVar;

    public RestrictionAtt(SchemaVariable sv) {
	AttVar = sv;
    }

    public String getTypeOfRestriction() {
	return "att "+ AttVar;
    }

    public SchemaVariable getAttributeVar() {
	return AttVar;
    }
}

