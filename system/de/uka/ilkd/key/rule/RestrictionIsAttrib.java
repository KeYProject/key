// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
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

