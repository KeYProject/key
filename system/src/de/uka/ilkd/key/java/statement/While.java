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
import de.uka.ilkd.key.util.ExtList;

/**
 *  While.
 */

public class While extends LoopStatement {

    /**
     *      While.
     */

    public While() {}

    /**
     *      While.
     *      @param guard an expression.
     *      @param body a statement.
     *	    @param pos a PositionInformation.
     */

    public While(Expression guard, Statement body, PositionInfo pos,
		 ExtList comments){
        super(guard,body,comments,pos);
    }
    
    /**
     * create a new While statement with no position info and no comments but guard and body set
     * @param guard an expression.
     * @param body a statement.
     */

    public While(Expression guard, Statement body) {
        super(guard, body, new ExtList());
    }

	/**
     *      While.
     *      @param guard an expression.
     *      @param body a statement.
     *	    @param pos a PositionInformation.
     */

    public While(Expression guard, Statement body, PositionInfo pos){
        super(guard, body, pos);	
    }

    public SourceElement getLastElement() {
        return (body != null) ? body.getLastElement() : this;
    }

    /**
     *      Is checked before iteration.
     *      @return the boolean value.
     */

    public boolean isCheckedBeforeIteration() {
        return true;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnWhile(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printWhile(this);
    }
}
