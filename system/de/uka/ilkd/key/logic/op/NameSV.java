// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.rule.Rule;

public class NameSV extends SchemaVariableAdapter {

    public NameSV(Name name) {
        super(name, Rule.class);
    }

    public NameSV(String s) {
        this(new Name(s));
    }
    
    public boolean isNameSV() {
	return true;
    }
    
    public String toString() {
	return super.toString("name");
    }	

    public boolean equals(Object o) {

        if (o instanceof NameSV) {
            if (toString() != null) {
                return toString().equals(o.toString());
            } else {
                return o.toString() == null;
            }
        } else {
            return false;
        }

    }

}
