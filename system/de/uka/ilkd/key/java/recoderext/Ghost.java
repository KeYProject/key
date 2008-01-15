// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.recoderext;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;


public class Ghost extends Modifier {
    
    public Ghost() {
    }
    

    protected Ghost(Ghost proto) {
        super(proto);
    }
    

    public Object deepClone() {
        return new Ghost(this);
    }

    
    public void accept(SourceVisitor v) {
        assert false;
    }
 }
