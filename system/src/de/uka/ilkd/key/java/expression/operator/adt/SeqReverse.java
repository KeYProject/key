// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.expression.operator.adt;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

public class SeqReverse extends Operator {

    public SeqReverse(ExtList children) {
        super(children);
    }


    @Override    
    public int getPrecedence() {
        return 0;
    }


    @Override    
    public int getNotation() {
        return PREFIX;
    }


    @Override    
    public void visit(Visitor v) {
	v.performActionOnSeqReverse(this);
    }


    @Override    
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printSeqReverse(this);
    }
    
    
    @Override
    public int getArity() {
	return 1;
    }
    
    
    @Override
    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
	return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_SEQ);
    }    
}