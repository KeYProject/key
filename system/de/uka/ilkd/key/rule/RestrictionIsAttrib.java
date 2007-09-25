package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.op.SchemaVariable;


public class RestrictionIsAttrib implements Restriction {

    Restriction attribsRestriction;

    public RestrictionIsAttrib(Restriction r) {
	attribsRestriction = r;
    }

    public String getTypeOfRestriction() {
	return "isAttrib";
    }

    public SchemaVariable getAttributeVar() {
	return null;
    }

    public Restriction getAttribsRestriction() {
	return attribsRestriction;
    }
}

