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

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

public class SeqSub extends Operator {

    public SeqSub(ExtList children) {
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
	v.performActionOnSeqSub(this);
    }


    @Override    
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printSeqSub(this);
    }
    
    
    @Override
    public int getArity() {
	return 3;
    }
    
    
    @Override
    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
	final TypeConverter tc=javaServ.getTypeConverter();
	return tc.getPromotedType
	    (tc.getKeYJavaType((de.uka.ilkd.key.java.Expression)getChildAt(0), ec),
	     tc.getKeYJavaType((de.uka.ilkd.key.java.Expression)getChildAt(1), ec));
    }    
}
