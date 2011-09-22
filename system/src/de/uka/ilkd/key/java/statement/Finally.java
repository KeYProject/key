// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Finally.
 * 
 */
public class Finally extends BranchImp {

    /**
     *      Body.
     */
    protected StatementBlock body;

    /**
     *      Finally.
     */
    public Finally() {
	body=null;
    }

    /**
     *      Finally.
     *      @param body a statement.
     */
    public Finally(StatementBlock body) {
        this.body = body;
    }


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * May contain: a Body (as body of the Finally), Comments
     */ 
    public Finally(ExtList children) {
	super(children);
	body=children.get(StatementBlock.class);
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */    
    public int getChildCount() {
        int result = 0;
        if (body != null) result++;
        return result;
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
            index--;
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
     *        Get body.
     *        @return the statement.
     */
    public Statement getBody() {
        return body;
    }

    public SourceElement getLastElement() {
        return body;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnFinally(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printFinally(this);
    }
}
