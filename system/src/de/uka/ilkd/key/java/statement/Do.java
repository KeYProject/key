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



package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Do.
 *  
 */
public class Do extends LoopStatement {

    /**
     *      Do.
     */
    public Do() {
	super();
    }

    /**
     *      Do.
     *      @param guard an expression.
     */
    public Do(Expression guard) {
        super(guard);
    }

    /**
     *      Do.
     *      @param guard an expression.
     *      @param body a statement.
     */
    public Do(Expression guard, Statement body, ExtList l, PositionInfo pos) {
        super(guard, body, l, pos);	
    }

    /**
     *      Do.
     *      @param guard an expression.
     *      @param body a statement.
     */
    public Do(Expression guard, Statement body, PositionInfo pos) {
        super(guard, body, pos);	
    }

 
    public SourceElement getLastElement() {
        return this;
    }

    /**
     *      Is checked before iteration.
     *      @return the boolean value.
     */
    public boolean isCheckedBeforeIteration() {
        return false;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnDo(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printDo(this);
    }
}
