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
 * This class encapsulates updates of a for loop
 */

package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

public class ForUpdates extends JavaNonTerminalProgramElement
    implements ExpressionContainer, IForUpdates{

    ImmutableArray<Expression> updates;

    public ForUpdates(ImmutableArray<Expression> exprarr) {
	updates = exprarr;
    }

    public ForUpdates(ExtList ups, PositionInfo pos) {
        super(pos);
	Expression[] exps = new Expression[ups.size()];	
	for (int i = 0; i < exps.length; i++) {
	    exps[i] = (Expression)ups.get(i);
	}
	updates = new ImmutableArray<Expression>(exps);
    }
    

    /**
     *      Get the number of expressions in this container.
     *      @return the number of expressions.
     */
    public int getExpressionCount() {
	return updates.size();
    }

    /*
      Return the expression at the specified index in this node's
      "virtual" expression array.
      @param index an index for an expression.
      @return the expression with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */
    public Expression getExpressionAt(int index) {
	return updates.get(index);
    }

    public int size() {
	return getExpressionCount();
    }

    public ImmutableArray<Expression> getUpdates() {
	return updates;
    }
    
    public void visit(Visitor v) {
	v.performActionOnForUpdates(this);
    }

    public int getChildCount() {
	return getExpressionCount();
    }

    public ProgramElement getChildAt(int index) {
	return getExpressionAt(index);
    }

}
