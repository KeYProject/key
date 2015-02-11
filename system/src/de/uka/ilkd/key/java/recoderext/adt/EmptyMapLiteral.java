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
package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;

public final class EmptyMapLiteral extends Literal {

    public static final EmptyMapLiteral INSTANCE = new EmptyMapLiteral();

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

    @Override
    public String toSource() {
        return "\\map_empty";
    }
}
