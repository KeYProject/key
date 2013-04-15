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

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Break.
 * 
 */

public class Break extends LabelJumpStatement {

    /**
     *      Break.
     */

    public Break() {
	super();
    }

    /**
     *      Break.
     *      @param label a name for the label.
     */
    public Break(Label label) {
        super(label);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * May contain: Comments,
     *              a ProgramElementName (as label of the label jump statement)
     */ 
    public Break(ExtList children) {
	super(children);
	//	label=(ProgramElementName)children.get(ProgramElementName.class);
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnBreak(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printBreak(this);
    }
}
