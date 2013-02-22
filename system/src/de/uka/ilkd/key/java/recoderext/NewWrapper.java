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
import recoder.java.expression.operator.New;

public class NewWrapper extends New {

    /**
     * 
     */
    private static final long serialVersionUID = -2814303467813768233L;
    private Identifier scope;
    
    public NewWrapper(New proto, Identifier scope){
        super(proto);
        this.scope = scope;
    }
    
    public NewWrapper deepClone(){
        return new NewWrapper(super.deepClone(), scope==null ? null : scope.deepClone());
    }
    
    public Identifier getScope(){
        return scope;
    }
    
}
