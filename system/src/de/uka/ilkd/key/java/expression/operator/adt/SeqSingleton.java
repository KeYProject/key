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



package de.uka.ilkd.key.java.expression.operator.adt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

public class SeqSingleton extends Operator {

    public SeqSingleton(ExtList children) {
        super(children);
    }
    
    public SeqSingleton(Expression child) {
        super(child);
    }


    public int getPrecedence() {
        return 0;
    }


    public int getNotation() {
        return PREFIX;
    }


    public void visit(Visitor v) {
	v.performActionOnSeqSingleton(this);
    }

    
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printSeqSingleton(this);
    }

    public int getArity() {
        return 1;
    }

    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
	return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_SEQ);
    }    
}
