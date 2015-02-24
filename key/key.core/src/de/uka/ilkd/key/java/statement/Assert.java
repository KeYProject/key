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

package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.Visitor;


public class Assert extends JavaStatement implements ExpressionContainer {

    private Expression condition;
    private Expression message;

    public Assert(Expression condition, Expression message, PositionInfo pos) {
        super(pos);
        assert condition != null;
        this.condition = condition;
        this.message   = message; 
    }
   

    public Expression getExpressionAt(int index) {
        if (index == 0) { return condition; }
        index--;
        if (index == 0) { 
            if (message != null) { return message; }        
        }
        throw new IndexOutOfBoundsException();
    }

    public int getExpressionCount() {        
        return message == null ? 1 : 2;
    }

    public ProgramElement getChildAt(int index) {        
        return getExpressionAt(index);
    }

    public int getChildCount() {        
        return getExpressionCount();
    }

    public void visit(Visitor v) {
        v.performActionOnAssert(this);
    }

    public Expression getCondition() {
        return condition;
    }
    
    public Expression getMessage() {
        return message;
    }
    
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printAssert(this);
    }
}