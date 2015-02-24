// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.EnhancedFor;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.java.visitor.CreatingASTVisitor;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.ExtList;

/**
 * This visitor is used to identify and replace the while loop
 * in invariant rule.
 * 
 * It can be applied to EnhancedFors also.
 * 
 * @see WhileInvariantTransformer
 * @see WhileInvariantTransformation
 */
public class ReplaceWhileLoop extends CreatingASTVisitor {

    private boolean firstWhileFound = false;
    private boolean replaced = false;
    private StatementBlock toInsert = null;
    private LoopStatement theLoop = null;
    private int lastMethodFrameBeforeLoop = -1;

    private KeYJavaType returnType = null;

    private int currentMethodFrame = -1;
    private int firstLoopPos = -1;
    /**
     * if run in check mode there are normally schemavaribles, so we need the
     * instantiations of them
     */
    protected SVInstantiations instantiations = SVInstantiations.EMPTY_SVINSTANTIATIONS;

    /**
     * the result of the transformation
     */
    protected ProgramElement result = null;

    /**
     * creates the WhileLoopTransformation for the transformation mode
     * 
     * @param root
     *           the ProgramElement where to begin
     * 
     */
    public ReplaceWhileLoop(ProgramElement root, 
                            StatementBlock toInsert, 
                            Services services) {	
        super(root, true, services);
	this.toInsert = toInsert;
        firstWhileFound = false;
    }

    /**
     * creates the WhileLoopTransformation for the check mode
     * 
     * @param root
     *           the ProgramElement where to begin
     * @param inst
     *           the SVInstantiations if available
     */
    public ReplaceWhileLoop(ProgramElement root, SVInstantiations inst,
			    StatementBlock toInsert, Services services) {
        super(root, true, services);
	this.toInsert = toInsert;
        firstWhileFound = false;
        instantiations = (inst == null ? 
			  SVInstantiations.EMPTY_SVINSTANTIATIONS : inst);
    }

    protected void walk(ProgramElement node) {
	if ((node instanceof While || node instanceof EnhancedFor)&& !firstWhileFound) {
	    firstWhileFound = true;
	    firstLoopPos = depth();
	    theLoop = (LoopStatement) node;
	    lastMethodFrameBeforeLoop =
		currentMethodFrame;
	}
	if (node instanceof MethodFrame) {
	    currentMethodFrame = depth();
	}
	
	
	super.walk(node);
    }


    public void start() {
        stack.push(new ExtList());
        walk(root());
        ExtList el = stack.peek();
        int i = 0;
        while (!(el.get(i) instanceof ProgramElement)) {
            i++;
        }
        result = (ProgramElement) stack.peek().get(i);
    }

    public ProgramElement result() {
        return result;
    }


    public KeYJavaType returnType() {
	return returnType;
    }

    public Statement getTheLoop() {
	return theLoop;
    }

    public String toString() {
        return stack.peek().toString();
    }

    public void performActionOnMethodFrame(MethodFrame x) {
	if (lastMethodFrameBeforeLoop == depth()) {
	    IProgramVariable res = x.getProgramVariable();
 	    if (res != null)
 		returnType = res.getKeYJavaType();
	} 

	super.performActionOnMethodFrame(x);
    }

    public void performActionOnWhile(While x) {
        if (firstLoopPos == depth() &&
	    ! replaced) {
	    replaced = true;
	    if (toInsert == null)
		stack.pop();
	    else
		addChild(toInsert);
	    changed();
        } else {
            super.performActionOnWhile(x);
        }
    }
    
    /*
     * spot the first the loop and remember it.
     * This loop may be a while or also a foreach loop
     */
    public void performActionOnEnhancedFor(EnhancedFor x) {
        if (firstLoopPos == depth() && ! replaced) {
            replaced = true;
            if (toInsert == null)
                stack.pop();
            else
                addChild(toInsert);
            changed();
        } else {
            super.performActionOnEnhancedFor(x);
        }
    }
}