// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.recoderext;

import recoder.java.*;
import recoder.java.statement.JavaStatement;
/**
 *  The statement inserted by KeY if a method call is executed.
 */

public class MethodCallStatement extends JavaStatement implements
    StatementContainer, ExpressionContainer {

    /**
     * resultVar (should be a VariableReference, but the parser can't enforce this)
     */
        
    protected Expression resultVar;

    protected ExecutionContext ec;


    /**
     *      Body.
     */    
    protected Statement body;

    
    
    /**
     *      MethodCallStatement.
     *      @param resultVar the ProgramVariable the return value is assigned to
     *      @param body a Statement containing the method body of
     *      the called method
     */
    
    public MethodCallStatement(Expression resultVar, 
			       ExecutionContext ec,
			       StatementBlock body) {
        this.resultVar  = resultVar;
	this.ec      = ec;
        this.body    = body;
        makeParentRoleValid();
    }

    /**
     *      MethodCallStatement.
     *      @param proto a MethodCallStatement
     */
    
    protected MethodCallStatement(MethodCallStatement proto) {
        super(proto);
        if (proto.resultVar != null) {
            resultVar = (Expression) proto.resultVar.deepClone();
        }
        if (proto.ec != null) {
            ec = (ExecutionContext) proto.ec.deepClone();
        }	
        if (proto.body != null) {
            body = (Statement) proto.body.deepClone();
        }
        makeParentRoleValid();
    }
       

    /**
     *      Set the result variable.
     *      @param resultVar the result variable
     */
    
    public void setResultVariable(Expression resultVar) {
	this.resultVar = resultVar;
    }

    /**
     *      Get the result variable.
     *      @return the VariableReference
     */
    
    public Expression getResultVariable() {
	return resultVar;
    }

    /**
     *      Set body.
     *      @param body the Statement
     */
    
    public void setBody(Statement body) {
        this.body = body;
    }

    /**
     *      Get body.
     *      @return the Statement
     */
    
    public Statement getBody() {
        return body;
    }

    /**
     *      Finds the source element that occurs first in the source.
     *      Returns the first element of the first child.
     *      @return the last source element in the syntactical representation of
     *      this element, may be equals to this element.
     */
    
    public SourceElement getFirstElement() {
        return getChildAt(0).getFirstElement();
    }

    /**
     *      Finds the source element that occurs last in the source.
     *      Returns the last element of the body.
     *      @return the last source element in the syntactical representation of
     *      this element, may be equals to this element.
     */
    
    public SourceElement getLastElement() {
        return body.getLastElement();
    }

    /** 
     * returns the execution context
     */
    public ExecutionContext getExecutionContext() {
	return ec;
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */
    
    public int getChildCount() {
        int result = 0;
        if (resultVar != null) result++;
        if (ec != null) result++;
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
        if (resultVar != null) {
            if (index == 0) return resultVar;
            index--;
        }
        if (ec != null) {
            if (index == 0) return ec;
            index--;
        }
        if (body != null) {
            if (index == 0) return body;
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role -/0: resultVar
        // role 1/2: ec
        // role 2/1: body
        if (resultVar == child) {
            return 0;
        }
        if (ec == child) {
            return (resultVar != null) ? 1 : 0;
        }

        if (body == child) {
            return (resultVar != null) ? 2 : 1;
        }
        return -1;
    }

    /**
     *      Get the number of statements in this container.
     *      @return the number of statements.
     */

    public int getStatementCount() {
        int result = (body != null) ? 1 : 0;
        return result;
    }

    /**
     *       Return the statement at the specified index in this node's
     *       "virtual" statement array.
     *       @param index an index for a statement.
     *       @return the statement with the given index.
     *       @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *       of bounds.
     */

    public Statement getStatementAt(int index) {
        if (body != null && index == 0) {
            return body;
        }
        throw new ArrayIndexOutOfBoundsException();
    }
    

    /**
     *      Get the number of expressions in this container.
     *      @return the number of expressions.
     */

    public int getExpressionCount() {
        return (resultVar != null) ? 1 : 0;
    }

    /**
     *       Return the expression at the specified index in this node's
     *       "virtual" expression array.
     *       @param index an index for a expression.
     *       @return the expression with the given index.
     *       @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *       of bounds.
     */

    public Expression getExpressionAt(int index) {
        if (resultVar != null && index == 0) {
            return resultVar;
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
        if (resultVar == p)
        {
            Expression r = (Expression)q;
            resultVar = r;
            if (r != null) {
                r.setExpressionContainer(this);
            }
            return true;
        }
        else if (ec == p) {
            ec = (ExecutionContext)q;
            if (ec != null) {
                ec.setParent(this);
            }
            return true;
        }
        else if (body == p) {
            Statement r = (Statement)q;
            body = r;
            if (r != null) {
                r.setStatementContainer(this);
            }
            return true;
        }
        return false;
    }
    
    /**
     *      Ensures that each child has "this" as syntactical parent.
     */
    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (resultVar != null) {
            resultVar.setExpressionContainer(this);
        }
        if (ec != null) {
            ec.setParent(this);
        }
        if (body != null) {
            body.setStatementContainer(this);            
        }
    }

    //don't think we need it
    public void accept(SourceVisitor v) {
    }
    
    /**
     * Deep clone.
     * @return the object
     */
    public MethodCallStatement deepClone() {
	return new MethodCallStatement(this);
    }

}
