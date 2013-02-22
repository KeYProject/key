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

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;


public class Model extends Modifier {
    
    /**
     * 
     */
    private static final long serialVersionUID = -1997772798461795576L;


    public Model() {
    }
    

    protected Model(Model proto) {
        super(proto);
    }
    

    public Model deepClone() {
        return new Model(this);
    }

    
    public void accept(SourceVisitor v) {
    }
 }
