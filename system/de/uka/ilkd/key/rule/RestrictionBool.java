// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

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

