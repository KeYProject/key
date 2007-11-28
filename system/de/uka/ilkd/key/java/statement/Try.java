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
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ArrayOfProgramPrefix;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Try.
 *  @author <TT>AutoDoc</TT>
 */
public class Try extends BranchStatement 
    implements StatementContainer, ProgramPrefix {

    /**
     * Body.
     */

    private final StatementBlock body;

    /**
 *      Branches.
     */

    private final ArrayOfBranch branches;

    private final ArrayOfProgramPrefix prefixElementArray;

    private PosInProgram firstActiveChildPos = null;
    
    /**
 *      Try.
 *      @param body a statement block.
     */

    public Try(StatementBlock body) {
        this.body=body;
	this.branches=null;
        prefixElementArray = computePrefix(body);
    }

    /**
 *      Try.
 *      @param body a statement block.
 *      @param branches a branch array.
     */

    public Try(StatementBlock body, Branch[] branches) {
        this.body=body;
	this.branches=new ArrayOfBranch(branches);
        prefixElementArray = computePrefix(body);
    }

    /**
 *      Try.
 *      @param body a statement block.
 *      @param branches a branch array.
     */

    public Try(StatementBlock body, ArrayOfBranch branches) {
        this.body=body;
	this.branches = branches;
        prefixElementArray = computePrefix(body);
    }

    /**
 *      Try.
 *      @param children a list with all children
     */

    public Try(ExtList children) {
        super(children);
	this.body = (StatementBlock)children.get(StatementBlock.class);
	this.branches=new
	    ArrayOfBranch((Branch[])children.collect(Branch.class));
        prefixElementArray = computePrefix(body);
    }


    private ArrayOfProgramPrefix computePrefix(StatementBlock b) {
        return StatementBlock.
        computePrefixElements(b.getBody(), 0, this);                
    }

    public int getPrefixLength() {        
        return prefixElementArray.size();
    }

    public ProgramPrefix getPrefixElementAt(int i) {       
        return prefixElementArray.getProgramPrefix(i);
    }

    public ArrayOfProgramPrefix getPrefixElements() {
        return prefixElementArray;
    }
    
    public SourceElement getFirstElement() {
        return body.getFirstElement();
    }


    public SourceElement getLastElement() {
        return getChildAt(getChildCount() - 1).getLastElement();
    }

    /**
 *      Returns the number of children of this node.
 *      @return an int giving the number of children of this node
    */

    public int getChildCount() {
        int result = 0;
        if (body     != null) result++;
        if (branches != null) result += branches.size();
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
        if (branches != null) {
            return branches.getBranch(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
 *      Get body.
 *      @return the statement block.
     */

    public StatementBlock getBody() {
        return body;
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
 *      Get the number of branches in this container.
 *      @return the number of branches.
     */

    public int getBranchCount() {
        return (branches != null) ? branches.size() : 0;
    }

    /*
      Return the branch at the specified index in this node's
      "virtual" branch array.
      @param index an index for a branch.
      @return the branch with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */

    public Branch getBranchAt(int index) {
        if (branches != null) {
            return branches.getBranch(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /* Return the branch array wrapper
     * @return the array wrapper of the branches
     */
    public ArrayOfBranch getBranchList() {
	return branches;
    }

    public Branch containsAsBranch(Class cl) {
	ArrayOfBranch br = getBranchList();
	for (int i=0, brSize = br.size(); i<brSize; i++) {
	    if (cl.isInstance(br.getBranch(i))) {
		return branches.getBranch(i);
	    }
	}
	return null;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnTry(this);
    }


    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printTry(this);
    }

    public PosInProgram getFirstActiveChildPos() {
        
        if (firstActiveChildPos == null) {
            firstActiveChildPos = body.isEmpty() ? PosInProgram.TOP : PosInProgram.TOP.down(0).down(0);            
        }
        
        return firstActiveChildPos;
    }
}
