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
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;
/**
 *  Catch.
 * 
 */
public class Catch extends BranchImp implements ParameterContainer,
                                             VariableScope {

    /**
     *      Parameter.
     */

    protected final ParameterDeclaration parameter;

    /**
     *      Body.
     */

    protected final StatementBlock body;

    /**
     *      Catch.
     */
    public Catch() {
	super();
	parameter=null;
	body=null;
    }

    /**
     *      Catch.
     *      @param e a parameter declaration.
     *      @param body a statement.
     */
    public Catch(ParameterDeclaration e, StatementBlock body) {
        super();
        this.body=body;
	parameter=e;
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * May contain: 	Comments,
     * 		a ParameterDeclaration (declaring the catched
     * 				exceptions)
     * 		a StatementBlock (as the action to do when catching)
     */ 
    public Catch(ExtList children) {
	super(children);
	parameter=(ParameterDeclaration)children.get
	    (ParameterDeclaration.class);
	body=(StatementBlock)children.get(StatementBlock.class);
    }

    public SourceElement getLastElement() {
        return (body != null) ? body.getLastElement() : this;
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if (parameter != null) result++;
        if (body      != null) result++;
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
        if (parameter != null) {
            if (index == 0) return parameter;
            index--;
        }
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
     *      Get the number of parameters in this container.
     *      @return the number of parameters.
     */
    public int getParameterDeclarationCount() {
        return (parameter != null) ? 1 : 0;
    }

    /*
      Return the parameter declaration at the specified index in this node's
      "virtual" parameter declaration array.
      @param index an index for a parameter declaration.
      @return the parameter declaration with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */
    public ParameterDeclaration getParameterDeclarationAt(int index) {
        if (parameter != null && index == 0) {
            return parameter;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get body.
     *      @return the statement.
     */
    public Statement getBody() {
        return body;
    }

    /**
     *      Get parameter declaration.
     *      @return the parameter declaration.
     */
    public ParameterDeclaration getParameterDeclaration() {
        return parameter;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnCatch(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printCatch(this);
    }
}
