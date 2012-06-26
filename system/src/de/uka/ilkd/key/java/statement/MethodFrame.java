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
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.util.Debug;

/**
 *  The statement inserted by KeY if a method call is executed.
 */
public class MethodFrame extends JavaStatement implements
    Statement, StatementContainer, ProgramPrefix {

    /**
     * result
     */
    private final IProgramVariable resultVar;

    /**
     *      Body.
     */
    private final StatementBlock body;
    
    private final IExecutionContext execContext;
    
    private final IProgramMethod method;

    private final ImmutableArray<ProgramPrefix> prefixElementArray;
    
    private PosInProgram firstActiveChildPos = null;
    
    /**
     *      Labeled statement.
     *      @param resultVar the ProgramVariable the return value is assigned to
     *      @param body a Statement containing the method body of
     *      the called method
     */
    public MethodFrame(IProgramVariable resultVar, 
		       IExecutionContext execContext,
		       StatementBlock body) {
        this.resultVar   = resultVar;
        this.body        = body;
        this.execContext = execContext;
        this.method      = null;
        
        prefixElementArray = computePrefix(body);
	Debug.assertTrue(execContext != null, 
			 "methodframe: executioncontext missing");
	Debug.assertTrue(body != null, 
			 "methodframe: body missing");
    }
    
    /**
     *      Labeled statement.
     *      @param resultVar the ProgramVariable the return value is assigned to
     *      @param body a Statement containing the method body of
     *      the called method
     *      @param method the corresponding ProgramMethod object
     */
    public MethodFrame(IProgramVariable resultVar, 
		       IExecutionContext execContext,
		       StatementBlock body,
                       IProgramMethod method, 
                       PositionInfo pos) {
        super(pos);
        this.resultVar   = resultVar;
        this.body        = body;
        this.execContext = execContext;
        this.method      = method;
     
        prefixElementArray = computePrefix(body);
	Debug.assertTrue(execContext != null, 
			 "methodframe: executioncontext missing");
	Debug.assertTrue(body != null, 
			 "methodframe: body missing");
    }
   

    private ImmutableArray<ProgramPrefix> computePrefix(StatementBlock b) {
            return StatementBlock.
            computePrefixElements(b.getBody(), 0, this);                
    }
    
    public int getPrefixLength() {        
        return prefixElementArray.size();
    }

    public ProgramPrefix getPrefixElementAt(int i) {       
        return prefixElementArray.get(i);
    }

    public ImmutableArray<ProgramPrefix> getPrefixElements() {
        return prefixElementArray;
    }
    
    public PosInProgram getFirstActiveChildPos() {        
        if (firstActiveChildPos == null) {
            firstActiveChildPos = 
                body.isEmpty() ? PosInProgram.TOP : PosInProgram.TOP.
                down(getChildCount()-1).down(0);
        }
        return firstActiveChildPos;
    }
    
    public SourceElement getFirstElement() {
//        return getChildAt(0).getFirstElement();  -VK
        return body.getFirstElement();
    }

    public SourceElement getLastElement() {
        return body.getLastElement();
    }

    /**
     *      Get the method call header.
     *      @return the MethodCallHeader
     */
    public IProgramVariable getProgramVariable() {
	return resultVar;
    }

    /**
     * returns the execution context for the elements in the method
     * frame's body
     */
    public IExecutionContext getExecutionContext() {
	return execContext;
    }

    /**
     *      Get body.
     *      @return the Statement
     */
    public StatementBlock getBody() {
        return body;
    }
    
    
    /**
     *      Get method.
     *      @return the method
     */
    public IProgramMethod getProgramMethod() {
        return method;
    }



    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */

    public int getChildCount() {
        int result = 0;
        if (resultVar != null) result++;
        if (execContext != null) result++;
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
        if (execContext != null) {
            if (index == 0) return execContext;
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

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnMethodFrame(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
	p.printMethodFrame(this);
    }
}
