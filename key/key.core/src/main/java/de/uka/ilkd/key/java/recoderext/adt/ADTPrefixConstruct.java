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

package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.ReferenceSuffix;

public abstract class ADTPrefixConstruct extends Operator implements ReferencePrefix {
    
    /**
     * 
     */
    private static final long serialVersionUID = 2903025447315816147L;
    private ReferenceSuffix suffix;
    
    public ADTPrefixConstruct(){
        super();
    }
    
    public ADTPrefixConstruct(Expression unary){
        super(unary);
    }
    
    public ADTPrefixConstruct(Expression lhs, Expression rhs){
        super(lhs,rhs);
    }
    
    protected ADTPrefixConstruct(ADTPrefixConstruct proto){
        super(proto);
    }

    @Override
    public ReferenceSuffix getReferenceSuffix() {
        return suffix;
    }

    @Override
    public void setReferenceSuffix(ReferenceSuffix arg0) {
        suffix = arg0;
    }

    @Override
    public void accept(SourceVisitor arg0) {
        // SourceVisitors in RecodeR currently are only used to perform the toSource() operation.
        // One of them needs to be implemented in order for source code to be reproduced.
    }
    
    @Override
    public int getPrecedence(){
        return 0; // TODO remove from subclasses
    }
    
    @Override
    public String toString(){
        return toSource();
    }

}