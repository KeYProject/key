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

import de.uka.ilkd.key.java.recoderext.adt.MethodSignature;
import de.uka.ilkd.key.logic.op.SchemaVariable;

public class MethodSignatureSVWrapper extends MethodSignature implements SVWrapper {

    private static final long serialVersionUID = -4381850332826267659L;
    private SchemaVariable method; 
    
    public MethodSignatureSVWrapper(SchemaVariable l) {
       super(null, null);
       method = l;
    }
    
    public SchemaVariable getSV() {        
        return method;
    }

    public void setSV(SchemaVariable sv) {
        method = sv;        
    }

    public String toString() {
        return ""+method;
    }
}