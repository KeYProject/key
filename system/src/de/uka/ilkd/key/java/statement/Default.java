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

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;
/**
 *  Default.
 * 
 */
public class Default extends BranchImp {

    /**
     *      Body.
     */
    protected final ImmutableArray<Statement> body;

    /**
     *      Default.
     */
    public Default() {
	this.body=null;
    }

    /**
     *      Default.
     *      @param body a statement array.
     */

    public Default(Statement[] body) {
	this.body=new ImmutableArray<Statement>(body);
    }

   /**
    * Constructor for the transformation of COMPOST ASTs to KeY.
    * @param children the children of this AST element as KeY classes.
    * May contain: 	Comments,
    * 		        several of Statement (as the statements for Default)
    */ 
    public Default(ExtList children) {
	super(children);
	this.body=new ImmutableArray<Statement>(children.collect(Statement.class)); 
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if (body != null) result += body.size();
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
        int len;
        if (body != null) {
            len = body.size();
            if (len > index) {
                return body.get(index);
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get the number of statements in this container.
     *      @return the number of statements.
     */
    public int getStatementCount() {
        return (body != null) ? body.size() : 0;
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
        if (body != null) {
            return body.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      The body may be empty (null), to define a fall-through.
     *      Attaching an {@link EmptyStatement} would create a single ";".
     */
    public ImmutableArray<Statement> getBody() {
        return body;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnDefault(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printDefault(this);
    }
}
