// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.recoderext;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;


public final class EmptySetLiteral extends Literal {
    
    public static final EmptySetLiteral INSTANCE = new EmptySetLiteral();
    
    @Override
    public Expression deepClone() {
	return this;
    }

    @Override    
    public void accept(SourceVisitor v) {
    }

    
    @Override
    public Object getEquivalentJavaType() {
	return null;
    }
}
