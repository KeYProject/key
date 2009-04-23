// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//
//

package de.uka.ilkd.key.rule.metaconstruct;

import java.util.HashMap;
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.expression.ExpressionStatement;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.SetAssignment;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

/** Walks through a java AST in depth-left-fist-order. 
 * This walker is used to transform a loop (not only 
 * while loops) according to the rules of the dynamic logic.
 */
public class WhileLoopTransformation extends JavaASTVisitor {

    protected static final Boolean CHANGED = new Boolean(true);
    /** the replacement element */
    protected ProgramElement replacement;
    /** break outerlabel */
    protected Break breakOuterLabel;
    /** break innerlabel */
    protected Break breakInnerLabel;
    /**  */
    protected ExtList labelList = new ExtList();
    /**  */
    protected Stack stack = new Stack();
    /** if there is a loop inside the loop the breaks of these inner loops have
     * not to be replaced. The replaceBreakWithNoLabel counts the depth of the
     * loop cascades. Replacements are only performed if the value of the
     * variable is zero 
     */
    protected int replaceBreakWithNoLabel = 0;
    /** there are two modes the visitor can be run. The check and transformation
     * mode. In the check mode it is only looked if there are unlabeled break
     * and continues that needs to be replaced, the transformation mode performs
     * the unwinding of the loop with all necessary replacements
     */
    protected static final int TRANSFORMATION = 0;
    protected static final int CHECK          = 1;
    protected int runMode                     = TRANSFORMATION;
    /** indicates if an unlabled break has been found and an outer
     * label is needed
     */
    protected boolean needOuterLabel = false;
    /** Indicates if an unlabled continue has been found or if a labelled 
     * continue with a label outside of the loop currently transformed has 
     * been found. Then an inner label is needed.
     */
    protected boolean needInnerLabel = false;
    /** counts the number of labelled continues with an label outside the
     * while loop that is transformed
     */
    protected int newLabels = 0;

    /** if run in check mode there are normally schemavaribles, so we need the
     * instantiations of them
     */
    protected SVInstantiations instantiations = SVInstantiations.EMPTY_SVINSTANTIATIONS;

    /**
     * the result of the transformation
     */
    protected ProgramElement result=null;

    protected Stack labelStack = new Stack();


    protected Stack methodStack = new Stack();

    /** creates the WhileLoopTransformation for the transformation mode
     * @param root the ProgramElement where to begin
     * @param outerLabel the ProgramElementName of the outer label 
     * @param innerLabel the ProgramElementName of the inner label 
     */
    public WhileLoopTransformation(ProgramElement root, 
				   ProgramElementName outerLabel,
				   ProgramElementName innerLabel,
                                   Services services) {
	super(root, services);
	breakOuterLabel = (outerLabel == null ? null : new Break(outerLabel));
	breakInnerLabel = (innerLabel == null ? null : new Break(innerLabel));
	replaceBreakWithNoLabel = 0;
	runMode = TRANSFORMATION;
    }

    /** creates the  WhileLoopTransformation for the check mode
     * @param root the ProgramElement where to begin
     * @param inst the SVInstantiations if available
     */
    public WhileLoopTransformation(ProgramElement root, 
                                   SVInstantiations inst, 
                                   Services services) {
	super(root, services);
	instantiations = (inst == null ? 
			  SVInstantiations.EMPTY_SVINSTANTIATIONS :
			  inst);
	replaceBreakWithNoLabel = 0;
	runMode = CHECK;
    }

    /** returns true if an inner label is needed */    
    public boolean innerLabelNeeded() {
	return needInnerLabel;
    }

    /** returns true if an outer label is needed */    
    public boolean outerLabelNeeded() {
	return needOuterLabel;
    }


    /** the action that is performed just before leaving the node the
     * last time 
     */
    protected void doAction(ProgramElement node) {
	if (runMode == CHECK) {
	    // in check mode we look only for unlabeled breaks and continues
	    if (node instanceof Break || 
		node instanceof Continue || 
		node instanceof SchemaVariable ||
		node instanceof Return) {
		node.visit(this);
	    }
	} else { 
	    node.visit(this);
	}
    }
    
    /** starts the walker*/
    public void start() {
	replaceBreakWithNoLabel = -1;
	stack.push(new ExtList());		
	walk(root());
	if (runMode == TRANSFORMATION) {
	    ExtList el=(ExtList)stack.peek();
	    int i = ( el.get(0) == CHANGED ? 1 : 0);
	    result = (ProgramElement) (el.get(i));	
	}
    }

    public ProgramElement result() {	
	Debug.out("While-Loop-Tranform-Result: ",result);
	return result;
    }
    
    /** walks through the AST. While keeping track of the current node
     * @param node the JavaProgramElement the walker is at 
     */
    protected void walk(ProgramElement node) {	
	stack.push(new ExtList());
	if ((node instanceof LoopStatement) ||
	    (node instanceof Switch)) {
	    replaceBreakWithNoLabel++;
	}
	if (node instanceof LabeledStatement) {
	    labelStack.push(((LabeledStatement)node).getLabel());
	}
	if (node instanceof MethodFrame) {
	    methodStack.push(node);
	}

	super.walk(node);
	if (runMode == CHECK) {
	    if (needOuterLabel && needInnerLabel) {
		// both labels are needed so if we just look for the necessary
		// schemavariables we can stop here
		return;
	    }
	}
	if (node instanceof LoopStatement || 
	    node instanceof Switch) {
	    replaceBreakWithNoLabel--;
	}
    }

    public String toString() {
	return stack.peek().toString();
    }

    /** the implemented default action is called if a program element is,
     * and if it has children all its children too are left unchanged
     */
    protected void doDefaultAction(SourceElement x) {
	addChild(x);
    }

    public void performActionOnSchemaVariable(SchemaVariable sv) {
        Object buffer = instantiations.getInstantiation(sv);
        if (buffer==null) {
	    // we cannont decide whether there are unlabeled breaks that is why
	    // both labeled are needed
	    needInnerLabel = true;
	    needOuterLabel = true;
        } else {
            if (buffer instanceof ArrayOfProgramElement){
                ArrayOfProgramElement aope = (ArrayOfProgramElement)buffer;
                for (int iterate=0; iterate<aope.size();iterate++){
                    ProgramElement pe = aope.getProgramElement(iterate);
	            if (pe != null) {
                        walk(pe);
                    }
                }
            } else {
                walk((ProgramElement)buffer);                
            }
        }



        /**This was the part handling only ProgramElements
        ProgramElement pe = (ProgramElement)
	    instantiations.getInstantiation(sv);
	if (pe != null) {
	    walk(pe);
	} else {
	    // we cannont decide whether there are unlabeled breaks that is why
	    // both labeled are needed
	    needInnerLabel = true;
	    needOuterLabel = true;
	}
        */

    }

    public void performActionOnLocalVariableDeclaration
	(LocalVariableDeclaration x) {
    	DefaultAction def=new DefaultAction() {
		ProgramElement createNewElement(ExtList changeList) {
		    return new LocalVariableDeclaration(changeList);
		}
	    };
	def.doAction(x);
    }

    public void performActionOnStatementBlock(StatementBlock x) {
	DefaultAction def=new DefaultAction() {
		ProgramElement createNewElement(ExtList changeList) {
		    return new StatementBlock(changeList);
		}
	    };
	def.doAction(x);
    }

    protected boolean replaceJumpStatement(LabelJumpStatement x) {	
	if (replaceBreakWithNoLabel ==0 &&
	    x.getProgramElementName() == null) {
	    return true;
	}
	return labelList.contains(x.getProgramElementName());
    }

    public void performActionOnBreak(Break x) {
	if (replaceJumpStatement(x)) {
	    if (runMode == CHECK) {
		needOuterLabel = true;
	    } else {
	        needOuterLabel = true;	    	
		addChild(breakOuterLabel);
		changed();
	    }
	} else {
	    doDefaultAction(x);
	}
    }

    public void performActionOnContinue(Continue x)     {
	if (replaceJumpStatement(x)) {
	    if (runMode == CHECK) {
		needInnerLabel = true;
	    } else {
	        needInnerLabel = true;
		addChild(breakInnerLabel);
		changed();
	    }
	} else if ((x.getLabel() != null) &&
		   (labelStack.search(x.getLabel())==-1)) {
	    if (runMode == CHECK) {
		needInnerLabel = true;
	    } else if (runMode == TRANSFORMATION) {
                needInnerLabel = true;
		addChild(new Break(breakInnerLabel.getLabel()));
		changed();
	    }
	} else {
	    doDefaultAction(x);
	}
    }

    /**
    *
    *     public void performActionOnFor(For x) {
    * 	ExtList changeList = (ExtList)stack.peek();
    * 	if (replaceBreakWithNoLabel==0){
    * 	//most outer for loop
    * 	    if (changeList.getFirst() == CHANGED)
    * 	    	changeList.removeFirst();
    * 
    * 	    LoopInitializer init[] = new
    * 		LoopInitializer[x.getInitializers().size()];
    * 
    * 	    Expression[] updates = new
    * 		Expression[x.getUpdates().size()];
    * 
    * 	    //the unchanged updates need to be extracted to initialize the
    * 	    //remainding 'for' statement
    * 	    Expression[] unchangedUpdates = new
    * 		Expression[x.getUpdates().size()];
    * 
    * 	    Expression guard = null;
    * 	    Statement body = null;
    * 	    ProgramElement element =
    * 		(ProgramElement) (changeList.isEmpty() ?
    * 				  null :
    * 				  changeList.removeFirst());
    * 	    // get loop initializers
    * 	    int foundInitializers = 0;
    * 	    while (element instanceof LoopInitializer) {
    * 		init[foundInitializers] = (LoopInitializer) element;
    * 		element = (ProgramElement) (changeList.isEmpty() ?
    * 		   		            null :
    * 		                            changeList.removeFirst());
    * 	        foundInitializers++;
    * 	    }
    * 	    de.uka.ilkd.key.util.Debug.assertTrue
    *                 (init.length == x.getInitializers().size(),
    * 		 "Critical Error: not all initializers found. "+
    * 		 "performActionOnFor in WhileLoopTransformation.");
    * 	    // get guard
    * 	    if (x.getGuard() != null) {
    * 		guard = (Expression)element;
    * 	    }
    * 
    * 	    // getUpdates
    * 	    int foundUpdates = 0;
    * 	    element = (ProgramElement) (changeList.isEmpty() ?
    * 		  		        null :
    * 					changeList.removeFirst());
    * 	    while (element instanceof Expression && foundUpdates<x.getUpdates().size()) {
    * 		updates[foundUpdates] = (Expression) element;
    * 		element = (ProgramElement) (changeList.isEmpty() ?
    * 				            null :
    * 					    changeList.removeFirst());
    * 		unchangedUpdates[foundUpdates] = x.getUpdates().getExpression(foundUpdates);
    * 	        foundUpdates++;
    * 	    }
    * 	    de.uka.ilkd.key.util.Debug.assertTrue
    * 		(updates.length == x.getUpdates().size(),
    * 		 "Critical Error: not all updates found. "+
    * 		 "performActionOnFor in WhileLoopTransformation.");
    * 
    * 	    // getBody
    * 	    body = (Statement) element;
    * 
    * 	    For remainder = new For(null, x.getGuard(), unchangedUpdates, x.getBody());
    * 	    if (breakInnerLabel!=null)
    * 	        body = (Statement) new LabeledStatement(breakInnerLabel.getLabel(), body);
    * 
    * 
    * 	    Statement innerBlockStatements[] = new Statement[updates.length+2];
    * 	    innerBlockStatements[0] = body;
    * 	    for (int copyStatements=0; copyStatements<updates.length;copyStatements++)
    * 	        innerBlockStatements[copyStatements+1] = (ExpressionStatement) updates[copyStatements];
    * 	    innerBlockStatements[updates.length+1] = remainder;
    * 
    *             Statement outerBlockStatements[] = new Statement[init.length+1];
    *             for (int copyStatements=0; copyStatements<init.length;copyStatements++)
    *                 outerBlockStatements[copyStatements] = init[copyStatements];
    *             outerBlockStatements[init.length] = new If(guard ,new Then(new StatementBlock(new ArrayOfStatement(innerBlockStatements))));
    *             //outerBlockStatements[init.length+1] = remainder;
    * 
    * 	    if (breakOuterLabel!=null)
    * 	        addChild(new LabeledStatement(breakOuterLabel.getLabel(), new StatementBlock(
    * 	            new ArrayOfStatement(outerBlockStatements))));
    * 	    else
    * 	        addChild(new StatementBlock(new ArrayOfStatement(outerBlockStatements)));
    *      	    changed();
    * 	} else {
    * 	    if (changeList.getFirst() == CHANGED) {
    * 	    	changeList.removeFirst();
    * 
    * 	    	LoopInitializer init[] = new
    * 		    LoopInitializer[x.getInitializers().size()];
    * 
    * 	    	Expression[] updates = new
    * 		    Expression[x.getUpdates().size()];
    * 
    * 	    	Expression guard = null;
    * 	    	Statement body = null;
    * 	    	ProgramElement element =
    * 		    (ProgramElement) (changeList.isEmpty() ?
    * 			   	      null :
    * 				      changeList.removeFirst());
    * 	    	// get loop initializers
    * 	        int foundInitializers = 0;
    * 	    	while (element instanceof LoopInitializer) {
    * 		    init[foundInitializers] = (LoopInitializer) element;
    * 		    element = (ProgramElement) (changeList.isEmpty() ?
    * 					        null :
    * 						changeList.removeFirst());
    * 		    foundInitializers++;
    * 	    	}
    * 	    	de.uka.ilkd.key.util.Debug.assertTrue
    *                     (init.length == x.getInitializers().size(),
    * 		     "Critical Error: not all initializers found. "+
    * 		     "performActionOnFor in WhileLoopTransformation.");
    * 	    	// get guard
    * 	    	if (x.getGuard() != null) {
    * 		    guard = (Expression)element;
    * 	    	}
    * 
    * 	    	// getUpdates
    * 	    	int foundUpdates = 0;
    * 	    	element = (ProgramElement) (changeList.isEmpty() ?
    * 					    null :
    * 					    changeList.removeFirst());
    * 	    	while (element instanceof Expression) {
    * 		    updates[foundUpdates] = (Expression) element;
    * 		    element = (ProgramElement) (changeList.isEmpty() ?
    * 					        null :
    * 					        changeList.removeFirst());
    * 		    foundUpdates++;
    * 	        }
    * 	    	de.uka.ilkd.key.util.Debug.assertTrue
    * 		    (updates.length == x.getUpdates().size(),
    * 		     "Critical Error: not all updates found. "+
    * 		     "performActionOnFor in WhileLoopTransformation.");
    * 
    * 	    	// getBody
    * 	    	body = (Statement) element;
    * 	    	addChild(new For(init, guard, updates, body));
    * 	    	changed();
    * 	    } else {
    * 	    	doDefaultAction(x);
    * 	    }
    * 	}
    *     }
    * 
    */
    public void performActionOnFor(For x) {
	ExtList changeList = (ExtList)stack.peek();
	if (replaceBreakWithNoLabel==0){
	//most outer for loop
	    if (changeList.getFirst() == CHANGED)
	    	changeList.removeFirst();

	    ILoopInit inits = null;

	    IForUpdates updates = null;

	    //the unchanged updates need to be extracted to initialize the
	    //remainding 'for' statement
	    IForUpdates unchangedUpdates = x.getIForUpdates();

	    Guard guard;
	    Statement body = null;

	    if (changeList.get(0) instanceof ILoopInit) {
		inits = (ILoopInit) changeList.removeFirst();
	    } 
            
            if (x.getGuard() != null) {            
                guard = (Guard) changeList.removeFirst();
                if (guard.getExpression() == null) {
                    guard = new Guard(BooleanLiteral.TRUE); 
                }
            } else {
                guard = new Guard(BooleanLiteral.TRUE);
            }
            
	    if (changeList.get(0) instanceof IForUpdates) {
		updates = (IForUpdates) changeList.removeFirst();
	    } 
            body = (Statement) changeList.removeFirst();

	    For remainder = 
		new For(null, x.getGuard(), unchangedUpdates, x.getBody());

            if (innerLabelNeeded() && breakInnerLabel != null) {
	        body = new LabeledStatement(breakInnerLabel.getLabel(), body);
	    }
	    
	    final int updateSize = 
		(updates == null ? 0 : updates.size());
	    Statement innerBlockStatements[] = new Statement[updateSize + 2];
	    innerBlockStatements[0] = body;
	    for (int copyStatements = 0; copyStatements < updateSize; copyStatements++) {
	        innerBlockStatements[copyStatements+1] = (ExpressionStatement) 
		    updates.getExpressionAt(copyStatements);
	    }
	    innerBlockStatements[updateSize+1] = remainder;



	    final int initSize = (inits == null ? 0 : inits.size());
            Statement outerBlockStatements[] = new Statement[initSize + 1];

            for (int copyStatements=0; copyStatements<initSize; copyStatements++) {
                outerBlockStatements[copyStatements] = 
		    inits.getInits().getLoopInitializer(copyStatements);
	    }
            
	    outerBlockStatements[initSize] = 
		new If(guard.getExpression(),
		       new Then(new StatementBlock(new ArrayOfStatement
						   (innerBlockStatements))));
	    
	    if (outerLabelNeeded() && breakOuterLabel!=null) {
	        addChild(new LabeledStatement
			 (breakOuterLabel.getLabel(), 
			  new StatementBlock(new ArrayOfStatement
					     (outerBlockStatements))));
	    } else {
	        addChild(new StatementBlock
			 (new ArrayOfStatement(outerBlockStatements)));
	    }
     	    changed();
	} else {

            if (changeList.getFirst() == CHANGED) {
	    	changeList.removeFirst();
	    	addChild(new For(changeList));
	    	changed();
	    } else {
	    	doDefaultAction(x);
	    }
	}
    }
    
    /**
     * perform the loop transformation on an enhanced for loop (Java5)
     * 
     * If the enhanced for loop is the toplevel loop nothing happens - 
     * return the loop itself, as enhanced for loops cannot be unwound, 
     * a log message is issued.
     *
     * If it is a loop deeper in the AST a new object is created if 
     * needed or the original loop returned.
     * 
     * @author mulbrich
     */
    public void performActionOnEnhancedFor(EnhancedFor x) {
        ExtList changeList = (ExtList)stack.peek();
        if (replaceBreakWithNoLabel == 0) {
            // the outermost loop
            Logger.getRootLogger().error("Enhanced for loops may not be toplevel in WhileLoopTransformation");
            doDefaultAction(x);
        } else {
            if (changeList.getFirst() == CHANGED) {
                changeList.removeFirst();
                addChild(new For(changeList));
                changed();
            } else {
                doDefaultAction(x);
            } 
        }
    }

    public void performActionOnWhile(While x)     {
	ExtList changeList = (ExtList)stack.peek();
	if (replaceBreakWithNoLabel == 0) {
	    // the most outer while loop
	    // get guard
	    if (changeList.getFirst() == CHANGED) {
		changeList.removeFirst();
	    }

	    Expression guard = ((Guard) changeList.removeFirst()).getExpression();
	    Statement body = (Statement) (changeList.isEmpty() ?
					  null :
					  changeList.removeFirst());
	    
	    /* 
	     * rename all occ. variables in the body (same name but different object)
	     */
	    ProgVarReplaceVisitor replacer = new ProgVarReplaceVisitor(body, 
	            new HashMap(), true, services);
	    replacer.start();
	    body = (Statement) replacer.result();
	    
	    if (innerLabelNeeded() && breakInnerLabel != null) {
		// an unlabeled continue needs to be handled with (replaced)
		body = new LabeledStatement(breakInnerLabel.getLabel(),
					    body);
	    }
	    Then then = null;
	    StatementBlock block = new StatementBlock
		(new ArrayOfStatement(new Statement[]
		    {body, (Statement) root()}));
	    if (outerLabelNeeded() && breakOuterLabel != null) {
		// an unlabeled break occurs in the
		// while loop therefore we need a labeled statement
		then = new Then(new LabeledStatement(breakOuterLabel.getLabel(),
						     block));

	    } else {
		then = new Then(block);
	    }
	    addChild(new If(guard, then));
	    changed();
	} else {
	    if (changeList.getFirst() == CHANGED) {
		changeList.removeFirst();
		//		Expression guard = (Expression) changeList.removeFirst(); ????
		Expression guard = ((Guard) changeList.removeFirst()).getExpression();
		Statement body = (Statement) (changeList.isEmpty() ?
					      null :
					      changeList.removeFirst());
		addChild(new While(guard, body, x.getPositionInfo()));
		changed();
	    } else {
		doDefaultAction(x);
	    }
	}
    }

    public void performActionOnDo(Do x)     {
	ExtList changeList = (ExtList)stack.peek();
	if (replaceBreakWithNoLabel == 0) {
	    // the most outer do loop
            if (changeList.getFirst() == CHANGED) {
		changeList.removeFirst();
	    }
	    Statement body = (Statement) (changeList.isEmpty() ?
					  null :
					  changeList.removeFirst());
	    Expression guard = ((Guard) changeList.removeFirst()).getExpression();
            Statement unwindedBody = null;
            if (innerLabelNeeded() && breakInnerLabel != null) {
		// an unlabeled continue needs to be handled with (replaced)
                unwindedBody = new LabeledStatement(breakInnerLabel.getLabel(),
						    body);
	    } else {
                unwindedBody = body;
            }
	    Statement resultStatement = null;
	    StatementBlock block = new StatementBlock
		(new ArrayOfStatement(new Statement[]
		    {unwindedBody, 
		        new While(guard, 
		                  x.getBody(), 
                                  x.getPositionInfo())}));

 	    if (outerLabelNeeded() && breakOuterLabel != null) {
		// an unlabeled break occurs in the
		// body therefore we need a labeled statement
		resultStatement = new LabeledStatement(breakOuterLabel.getLabel(),
						     block);
	    } else {
		resultStatement = block;
	    }
	    addChild(resultStatement);
	    changed();
	} else {
	    if (changeList.getFirst() == CHANGED) {
		changeList.removeFirst();
		Expression guard = (Expression) changeList.removeFirst();
		Statement body = (Statement) (changeList.isEmpty() ?
					      null :
					      changeList.removeFirst());
		addChild(new Do(guard, body, x.getPositionInfo()));
		changed();
	    } else {
		doDefaultAction(x);
	    }
	}
    }


    public void performActionOnIf(If x)     {
	DefaultAction def=new DefaultAction() {		
		ProgramElement createNewElement(ExtList changeList) {
		    return new If(changeList);
		}
	    };
	def.doAction(x);
    }
 
    public void performActionOnSwitch(Switch x)     {
	DefaultAction def=new DefaultAction() {		
		ProgramElement createNewElement(ExtList changeList) {
		    return new Switch(changeList);
		}
	    };
	def.doAction(x);
    }

    public void performActionOnTry(Try x)     {
	DefaultAction def=new DefaultAction() {		
		ProgramElement createNewElement(ExtList changeList) {
		    return new Try(changeList);
		}
	    };
	def.doAction(x);
    }

    public void performActionOnLabeledStatement(LabeledStatement x) {
	Label l = null;
	ExtList changeList = (ExtList)stack.peek();
	if (changeList.getFirst() == CHANGED) {	    
	    changeList.removeFirst();	    
	    if (x.getLabel() != null) {
		l = (Label) changeList.removeFirst();
	    }
	    addChild(new LabeledStatement(changeList, l, x.getPositionInfo()));
	    changed();
	} else {
	    doDefaultAction(x);
	}    
    } 

    public void performActionOnMethodFrame(MethodFrame x) {
	ExtList changeList = (ExtList)stack.peek();
	if (!changeList.isEmpty() && changeList.getFirst() == CHANGED) {	    
	    changeList.removeFirst();	    
	    if (x.getChildCount() == 3) {
		addChild
		    (new MethodFrame((IProgramVariable)changeList.get(0), 
				     (IExecutionContext)changeList.get(1),
				     (StatementBlock)changeList.get(2),
                                     x.getProgramMethod(), PositionInfo.UNDEFINED));

	    } else if (x.getChildCount() == 2) {
		addChild
		    (new MethodFrame(null, 
				     (IExecutionContext)changeList.get(0),
				     (StatementBlock)changeList.get(1),
                                     x.getProgramMethod(), PositionInfo.UNDEFINED));
	    } else {
		throw new IllegalStateException
		    ("Methodframe has not allowed number of children.");
	    }
	    changed();
	} else {
	    doDefaultAction(x);
	}	    
    } 
 

    public void performActionOnSynchronizedBlock(SynchronizedBlock x)     {
	DefaultAction def=new DefaultAction() {
		ProgramElement createNewElement(ExtList changeList) {
		    return new SynchronizedBlock(changeList);
		}
	    };
	def.doAction(x);
    }
 

    public void performActionOnCopyAssignment(CopyAssignment x) {
	DefaultAction def=new DefaultAction() {		
		ProgramElement createNewElement(ExtList changeList) {
		    return new CopyAssignment(changeList);
		}
	    };
	def.doAction(x);	
    }
    
    public void performActionOnSetAssignment(SetAssignment x) {
        DefaultAction def=new DefaultAction() {         
            ProgramElement createNewElement(ExtList changeList) {
                return new SetAssignment(changeList);
            }
        };
        def.doAction(x);                
    }

    public void performActionOnThen(Then x)     {
	DefaultAction def=new DefaultAction() {		
		ProgramElement createNewElement(ExtList changeList) {
		    return new Then(changeList);
		}
	    };
	def.doAction(x);
    }


    public void performActionOnElse(Else x)     {
	DefaultAction def=new DefaultAction() {		
		ProgramElement createNewElement(ExtList changeList) {
		    return new Else(changeList);
		}
	    };
	def.doAction(x);
    }


    public void performActionOnCase(Case x)     {
	Expression e = null;
	ExtList changeList = (ExtList)stack.peek();
	if (changeList.getFirst() == CHANGED) {	    
	    changeList.removeFirst();	    
	    if (x.getExpression() != null) {
		e = (Expression) changeList.removeFirst();
	    }
	    addChild(new Case(changeList, e, x.getPositionInfo()));
	    changed();
	} else {
	    doDefaultAction(x);
	}    
    }


    public void performActionOnCatch(Catch x)     {
	DefaultAction def=new DefaultAction() {		
		ProgramElement createNewElement(ExtList changeList) {
		    return new Catch(changeList);
		}
	    };
	def.doAction(x);
    }


    public void performActionOnDefault(Default x)     {
	DefaultAction def=new DefaultAction() {		
		ProgramElement createNewElement(ExtList changeList) {
		    return new Default(changeList);
		}
	    };
	def.doAction(x);
    }


    public void performActionOnFinally(Finally x)     {
	DefaultAction def=new DefaultAction() {		
		ProgramElement createNewElement(ExtList changeList) {
		    return new Finally(changeList);
		}
	    };
	def.doAction(x);
    }


    protected void changed() {
	ExtList list = (ExtList)stack.peek();
	if (list.getFirst() != CHANGED) {
	    list.addFirst(CHANGED);
	}
    }

    protected void addChild(SourceElement x) {
	stack.pop();
	ExtList list = (ExtList) stack.peek();
	list.add(x);
    }
    
    private abstract class DefaultAction {
	abstract ProgramElement createNewElement(ExtList changeList);

	private void addNewChild(ExtList changeList) {
	    addChild(createNewElement(changeList));
	    changed();	    
	}
	
	public void doAction(ProgramElement x) {
	    ExtList changeList = (ExtList)stack.peek();
	    if ( changeList.size () > 0 && 
		 changeList.getFirst() == CHANGED ) {	    
		changeList.removeFirst();	    
		addNewChild(changeList);
	    } else {
		doDefaultAction(x);
	    }	    
	}
    }
}
