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

package de.uka.ilkd.key.java.recoderext;

import recoder.java.SourceElement;
import recoder.java.reference.TypeReference;
import de.uka.ilkd.key.logic.op.SchemaVariable;

public class TypeSVWrapper extends TypeReference
    implements KeYRecoderExtension, SVWrapper{

    /**
     * 
     */
    private static final long serialVersionUID = 2694567717981292433L;
    SchemaVariable sv=null;

    public TypeSVWrapper(SchemaVariable sv) {
        this.sv=sv;
    }

    protected TypeSVWrapper(TypeSVWrapper proto) {
        super(proto);
    }

    /**
     * sets the schema variable of sort label
     * @param sv the SchemaVariable
     */
    public void setSV(SchemaVariable sv) {
	this.sv=sv;
    }

    /**
     * returns the schema variable of this type sv wrapper
     */
    public SchemaVariable getSV() {
	return sv;
    }

    public SourceElement getFirstElement() {
	return this;
    }


}
