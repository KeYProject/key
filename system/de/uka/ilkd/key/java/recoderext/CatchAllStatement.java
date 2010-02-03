// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.recoderext;

import recoder.java.*;
import recoder.java.declaration.ParameterDeclaration;
import recoder.java.statement.JavaStatement;

/**
 *  A shortcut-statement for a method body.
 */

public class CatchAllStatement extends JavaStatement implements
				 StatementContainer, ParameterContainer {


    /**
     * the ast parent
     */
    private StatementContainer astParent;

    protected StatementBlock body;
    protected ParameterDeclaration paramdecl;
    
    /**
     *      Construct a method body shortcut
     *      @param r the ParameterDeclaration of the catch clause
     *      @param body the StatementBlock representing the catch clause's body     
     */    
    public CatchAllStatement(ParameterDeclaration r,
			     StatementBlock body) {
        this.body = body;
	paramdecl = r;
        makeParentRoleValid();
    }


    public NonTerminalProgramElement getASTParent() {
	return astParent;
    }

    public StatementContainer getStatementContainer() {
	return astParent;
    }

    public int getStatementCount() {
	return (body==null) ? 0 : 1;
    }

    public Statement getStatementAt(int i) {
	return (i==0) ? body : null;
    }

    public int getParameterDeclarationCount() {
	return (paramdecl==null) ? 0 : 1;
    }

    public ParameterDeclaration getParameterDeclarationAt(int i) {
	return (i==0) ? paramdecl : null;
    }

    public void setStatementContainer(StatementContainer parent) {
	astParent = parent;
    }

    /**
     *      Finds the source element that occurs first in the source.
     *      @return the last source element in the syntactical representation of
     *      this element, may be equals to this element.
     */
    
    public SourceElement getFirstElement() {
        return getChildAt(0).getFirstElement();
    }

    /**
     *      Finds the source element that occurs last in the source.
     *      @return the last source element in the syntactical representation of
     *      this element, may be equals to this element.
     */
    
    public SourceElement getLastElement() {
        return getChildAt(getChildCount() - 1).getLastElement();
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */
    
    public int getChildCount() {
        int result = 0;
        if (body != null) result++;
        if (paramdecl != null) result++;
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
        if (paramdecl != null) {
            if (index == 0) return paramdecl;
            index--;
        }
        if (body != null) {
            if (index == 0) return body;
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }


    /**
     * Replace a single child in the current node.
     * The child to replace is matched by identity and hence must be known
     * exactly. The replacement element can be null - in that case, the child
     * is effectively removed.
     * The parent role of the new child is validated, while the
     * parent link of the replaced child is left untouched.
     * @param p the old child.
     * @param q the new child.
     * @return true if a replacement has occured, false otherwise.
     * @exception ClassCastException if the new child cannot take over
     *            the role of the old one.
     */

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
   
        return false;
    }

    
    /**
     *      Ensures that each child has "this" as syntactical parent.
     */
    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (body != null) {
            body.setStatementContainer(this);
        }
        if (paramdecl != null) {
            paramdecl.setParameterContainer(this);
        }
    }

    public int getChildPositionCode(ProgramElement child) {
        if (paramdecl == child) {
            return 0;
        }	
        if (body == child) {
            return 1;
        }
        return -1;
    }

    //don't think we need it
    public void accept(SourceVisitor v) {
	throw new IllegalStateException("Not implemented in "
					+"CatchAllStatement");
    }

    //don't think we need it
    public CatchAllStatement deepClone() {
	throw new IllegalStateException("Not implemented in "
					+"CatchAllStatement");
    }    

    public String getName() {	
	return "catchAll"+"("+paramdecl+") {"+body+" }";
    }


}
