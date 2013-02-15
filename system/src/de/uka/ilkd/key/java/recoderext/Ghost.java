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


public class Ghost extends Modifier {
    
    /**
     * 
     */
    private static final long serialVersionUID = -4883937081008486072L;


    public Ghost() {
    }
    

    protected Ghost(Ghost proto) {
        super(proto);
    }
    

    public Ghost deepClone() {
        return new Ghost(this);
    }

    
    public void accept(SourceVisitor v) {
    }
 }
