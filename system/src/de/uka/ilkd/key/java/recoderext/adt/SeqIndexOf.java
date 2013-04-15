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
import recoder.java.expression.Operator;


public class SeqIndexOf extends Operator {

    private static final long serialVersionUID = -6353396950660375581L;


    /**
     * Creates an "index of" operator.
     * @param seq Sequence to operate on
     * @param elem The element to look for in the sequence
     */
    public SeqIndexOf(Expression seq, Expression elem) {
        super(seq, elem);
        makeParentRoleValid();
    }


    protected SeqIndexOf(SeqIndexOf proto) {
        super(proto);
        makeParentRoleValid();
    }


    @Override    
    public SeqIndexOf deepClone() {
        return new SeqIndexOf(this);
    }


    @Override    
    public int getArity() {
        return 2;
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
    public void accept(SourceVisitor v) {

    }
    
    @Override
    public String toSource(){
        return "\\indexOf("+children.get(0).toSource()+","+children.get(1).toSource()+")";
    }
}
