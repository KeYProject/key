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

/**
 * This class encapsulates a guard for a loop
 */

package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

public class Guard extends JavaNonTerminalProgramElement 
    implements IGuard {

    Expression expr;

    public Guard(Expression expression) {
	expr=expression;
    }

    public Guard(ExtList children) {
	expr=children.get(Expression.class);
    }

    public Expression getExpression() {
	return expr;
    }

    public void visit(Visitor v) {
	v.performActionOnGuard(this);
    }

    public int getChildCount() {
	return (expr!=null) ? 1 : 0;
    }

    public ProgramElement getChildAt(int index) {
	if (index==0) return expr;
	return null;
    }
    
    public String toString(){
        return expr.toString();
    }
}
