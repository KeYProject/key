// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.annotation.Annotation;
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
     *      While.
     *      @param guard an expression.
     *      @param body a statement.
     *	    @param pos a PositionInformation.
     */

    public While(Expression guard, Statement body, PositionInfo pos, 
		 Annotation[] a){
        super(guard, body, a, pos);	
    }

    public SourceElement getLastElement() {
        return (body != null) ? body.getLastElement() : this;
    }

    /**
     *      Is exit condition.
     *      @return the boolean value.
     */

    public boolean isExitCondition() {
        return false;
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
