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

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Else.
 */

public class Else extends BranchImp {

    /**
     *      Body.
     */
    protected Statement body;


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * May contain: a Body (as body of Else), Comments
     */ 
    public Else(ExtList children) {
	super(children);
	body=children.get(Statement.class);
    }




    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param body Statement that is the body of the else part
     */ 
    public Else(Statement body) {
	this.body = body;
    }


    public SourceElement getLastElement() {
        return body.getLastElement();
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */
    public int getChildCount() {
        return (body != null) ? 1 : 0;
    }

    /**
     *      Returns the child at the specified index in this node's "virtual"
     *      child array
     *      @param index an index into this node's "virtual" child array
     *      @return the program element at the given position
     *      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *                 of bounds
     */
    public ProgramElement getChildAt(int index) {
        if (body != null) {
            if (index == 0) return body;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get the number of statements in this container.
     *      @return the number of statements.
     */
    public int getStatementCount() {
        return (body != null) ? 1 : 0;
    }

    /*
      Return the statement at the specified index in this node's
      "virtual" statement array.
      @param index an index for a statement.
      @return the statement with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */
    public Statement getStatementAt(int index) {
        if (body != null && index == 0) {
            return body;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      The body may be empty (null), to define a fall-through.
     *      Attaching an {@link EmptyStatement} would create a single ";".
     */
    public Statement getBody() {
        return body;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnElse(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printElse(this);
    }
}
