// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.logic.op.SchemaVariable;

/**
 * variable condition used if a new variable is introduced
 */
public class NewVarcond {

    private final SchemaVariable sv;
    private final SchemaVariable peerSV;
    private final Type type;

    
    /*
     * @param sv the Schemavariable representing a new variable.
     * @param peerSV a Schemavariable defining the type of the new variable.
     */
    public NewVarcond(SchemaVariable sv, SchemaVariable peerSV) {
	assert sv != null;
	assert peerSV != null;
	this.sv = sv;
	this.peerSV = peerSV;
	this.type = null;
    }

    
    public NewVarcond(SchemaVariable sv, Type type) {
	assert sv != null;
	assert type != null;
	this.sv = sv;
	this.peerSV = null;
	this.type = type;
    }

    
    public boolean isDefinedByType() {
	return peerSV == null;
    }

    
    public SchemaVariable getSchemaVariable() {
	return sv;
    }
    

    public SchemaVariable getPeerSchemaVariable() {
	return peerSV;
    }
    

    public Type getType() {
	return type;
    }
    
    
    public Object getTypeDefiningObject() {
	return type != null ? type : peerSV;
    }

    
    @Override
    public String toString() {
	return "\\new(" + sv + ", " 
	       + (type != null 
		  ? "" + type 
	          : "\\typeof(" + peerSV + ")") 
	       + ")";
    }
}
