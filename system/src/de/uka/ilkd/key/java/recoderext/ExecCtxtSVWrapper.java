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
import recoder.java.SourceVisitor;
import de.uka.ilkd.key.logic.op.SchemaVariable;

public class ExecCtxtSVWrapper extends ExecutionContext 
    implements KeYRecoderExtension, SVWrapper{

    /**
     * 
     */
    private static final long serialVersionUID = 2299515454738715766L;
    SchemaVariable sv=null;

    
    public ExecCtxtSVWrapper(SchemaVariable sv) {
        this.sv = sv;
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

    public ExecutionContext deepClone() {
	return new ExecCtxtSVWrapper(sv);
    }

    //don't think we need it
    public void accept(SourceVisitor v) {
    }


}
