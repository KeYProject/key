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

import recoder.java.*;
import recoder.java.expression.Operator;


/**
 * Represents the range suffix for subsequences written in suffix notation, e.g., <pre>seq[from..to]</pre>
 * @since 1.7.2119
 * @author bruns
 *
 */
public class RangeExpression extends Operator implements Expression {
    
    
    /**
     * 
     */
    private static final long serialVersionUID = 6404478656913511767L;


    public RangeExpression (Expression fromIdx, Expression toIdx){
        super(fromIdx, toIdx);
        makeParentRoleValid();
    }

    public RangeExpression(RangeExpression rangeExpression) {
        super(rangeExpression);
    }

    @Override
    public void accept(SourceVisitor arg0) {
        // TODO Auto-generated method stub
        
    }

    @Override
    public RangeExpression deepClone() {
        return new RangeExpression(this);
    }
    
    @Override
    public String toSource(){
        return "["+children.get(0)+".."+children.get(1)+"]";
    }


    @Override
    public int getArity() {
        return 2;
    }


    @Override
    public int getNotation() {
        return INFIX;
    }


    @Override
    public int getPrecedence() {
        return 1;
    }
    
}