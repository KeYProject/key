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



package de.uka.ilkd.key.java.recoderext;

import recoder.java.*;
import recoder.java.reference.VariableReference;
import recoder.java.statement.JavaStatement;

public class CatchAllStatement extends JavaStatement 
			       implements StatementContainer,
			       		  ExpressionContainer {

    /**
     * 
     */
    private static final long serialVersionUID = -7826889550059322778L;

    private StatementContainer astParent;

    protected StatementBlock body;
    protected VariableReference param;
    
    
    /**
     *      Construct a catch all statement
     *      @param r the VariableReference of the catch clause
     *      @param body the StatementBlock representing the catch clause's body     
     */    
    public CatchAllStatement(VariableReference r,
			     StatementBlock body) {
        this.body = body;
	param = r;
        makeParentRoleValid();
    }


    public NonTerminalProgramElement getASTParent() {
	return astParent;
    }

    
    public StatementContainer getStatementContainer() {
	return astParent;
    }

    
    public int getStatementCount() {
	return body == null ? 0 : 1;
    }

    
    public Statement getStatementAt(int i) {
	return i == 0 ? body : null;
    }
    
    
    public int getExpressionCount() {
        return (param != null) ? 1 : 0;
    }

    
    public Expression getExpressionAt(int index) {
        if (param != null && index == 0) {
            return param;
        }
        throw new ArrayIndexOutOfBoundsException();
    }
    
    
    public VariableReference getVariable() {
	return param;
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
        if (param != null) result++;
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
        if (param != null) {
            if (index == 0) return param;
            index--;
        }
        if (body != null) {
            if (index == 0) return body;
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }


    @Override
    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (param == p) {
            VariableReference r = (VariableReference)q;
            param = r;
            if (r != null) {
                r.setExpressionContainer(this);
            }
            return true;
        } else if (body == p) {
            StatementBlock r = (StatementBlock)q;
            body = r;
            if (r != null) {
                r.setStatementContainer(this);
            }
            return true;
        }
        return false;
    }

    
    /**
     * Ensures that each child has "this" as syntactical parent.
     */
    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (param != null) {
            param.setExpressionContainer(this);
        }        
        if (body != null) {
            body.setStatementContainer(this);
        }
    }
    

    public int getChildPositionCode(ProgramElement child) {
        if (param == child) {
            return 0;
        }	
        if (body == child) {
            return 1;
        }
        return -1;
    }
    

    //don't think we need it
    public void accept(SourceVisitor v) {
	if (v instanceof SourceVisitorExtended) {
	    ((SourceVisitorExtended)v).visitCatchAll(this);
	} else {
	    throw new IllegalStateException("Method 'accept' not implemented in "
		    +"CatchAllStatement");
	}
    }

    
    //don't think we need it
    public CatchAllStatement deepClone() {
	throw new IllegalStateException("Method 'deepClone' not implemented in "
					+"CatchAllStatement");
    }    

    
    public String getName() {	
	return "catchAll" + "(" + param + ") {" + body + " }";
    }
}
