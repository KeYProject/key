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

import recoder.java.Identifier;
import recoder.java.expression.operator.NewArray;

public class NewArrayWrapper extends NewArray {

    /**
     * 
     */
    private static final long serialVersionUID = -3838799869300845065L;
    private Identifier scope;
    
    public NewArrayWrapper(NewArray proto, Identifier scope){
        super(proto);
        this.scope = scope;
    }
    
    public NewArrayWrapper deepClone(){
        return new NewArrayWrapper(super.deepClone(), scope==null ? null : scope.deepClone());
    }
    
    public Identifier getScope(){
        return scope;
    }
    
}
