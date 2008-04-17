// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
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

