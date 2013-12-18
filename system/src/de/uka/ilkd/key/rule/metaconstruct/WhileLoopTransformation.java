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


package de.uka.ilkd.key.rule.metaconstruct;

import java.util.LinkedHashMap;
import java.util.Stack;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.expression.ExpressionStatement;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.statement.Break;
import de.uka.ilkd.key.java.statement.Case;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.Continue;
import de.uka.ilkd.key.java.statement.Default;
import de.uka.ilkd.key.java.statement.Do;
import de.uka.ilkd.key.java.statement.Else;
import de.uka.ilkd.key.java.statement.EnhancedFor;
import de.uka.ilkd.key.java.statement.Finally;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.Guard;
import de.uka.ilkd.key.java.statement.IForUpdates;
import de.uka.ilkd.key.java.statement.ILoopInit;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.LabelJumpStatement;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.Return;
import de.uka.ilkd.key.java.statement.Switch;
import de.uka.ilkd.key.java.statement.SynchronizedBlock;
import de.uka.ilkd.key.java.statement.Then;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

/** Walks through a java AST in depth-left-fist-order. 
 * This walker is used to transform a loop (not only 
 * while loops) according to the rules of the dynamic logic.
 */
public class WhileLoopTransformation extends JavaASTVisitor {

    protected static final Boolean CHANGED = Boolean.TRUE;
    /** the replacement element */
    protected ProgramElement replacement;
    /** break outerlabel */
    protected Break breakOuterLabel;
    /** break innerlabel */
    protected Break breakInnerLabel;
    /**  */
    protected ExtList labelList = new ExtList();
    /**  */
    protected Stack<ExtList> stack = new Stack<ExtList>();
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

    protected Stack<Label> labelStack = new Stack<Label>();

    protected Stack<MethodFrame> methodStack = new Stack<MethodFrame>();

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
	breakOuterLabel = (outerLabel == null ? null : KeYJavaASTFactory
		.breakStatement(outerLabel));
	breakInnerLabel = (innerLabel == null ? null : KeYJavaASTFactory
		.breakStatement(innerLabel));
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
	    ExtList el=stack.peek();
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
	    methodStack.push((MethodFrame)node);
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
            if (buffer instanceof ProgramElement) {
                walk((ProgramElement)buffer);                
            } else {
                final ImmutableArray<?> aope = (ImmutableArray<?>)buffer;
                for (int iterate=0; iterate<aope.size();iterate++){
                    ProgramElement pe = (Statement)aope.get(iterate);
	            if (pe != null) {
                        walk(pe);
                    }
                }
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
		return KeYJavaASTFactory.declare(changeList);
		}
	    };
	def.doAction(x);
    }

    public void performActionOnStatementBlock(final StatementBlock x) {
        DefaultAction def=new DefaultAction() {
            ProgramElement createNewElement(ExtList changeList) {
		StatementBlock newBlock = KeYJavaASTFactory.block(changeList);
                ImmutableSet<BlockContract> bcs
                    = services.getSpecificationRepository().getBlockContracts(x);
                if (bcs != null) {
                    for (BlockContract bc : bcs) {
                        bc = bc.setBlock(newBlock);
                        services.getSpecificationRepository().addBlockContract(bc);
                    }
                }
                return newBlock;
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
		// Keep the PositionInfo because it is required for symbolic
		// execution tree extraction and this assignment is the only
		// unique representation of the replaced continue
		addChild(KeYJavaASTFactory.breakStatement(
			breakInnerLabel.getLabel(), x.getPositionInfo()));
		changed();
	    }
	} else {
	    doDefaultAction(x);
	}
    }

    /**
    *
    *     public void performActionOnFor(For x) {
    * 	ExtList changeList = stack.peek();
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
    *             outerBlockStatements[init.length] = new If(guard ,new Then(new StatementBlock(new ArrayOf<Statement>(innerBlockStatements))));
    *             //outerBlockStatements[init.length+1] = remainder;
    * 
    * 	    if (breakOuterLabel!=null)
    * 	        addChild(new LabeledStatement(breakOuterLabel.getLabel(), new StatementBlock(
    * 	            new ArrayOf<Statement>(outerBlockStatements))));
    * 	    else
    * 	        addChild(new StatementBlock(new ArrayOf<Statement>(outerBlockStatements)));
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
	ExtList changeList = stack.peek();
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
		    guard = KeYJavaASTFactory.trueGuard();
                }
            } else {
		guard = KeYJavaASTFactory.trueGuard();
            }
            
	    if (changeList.get(0) instanceof IForUpdates) {
		updates = (IForUpdates) changeList.removeFirst();
	    } 
            body = (Statement) changeList.removeFirst();

	    For remainder = KeYJavaASTFactory.forLoop(x.getGuard(),
		    unchangedUpdates, x.getBody());

            if (innerLabelNeeded() && breakInnerLabel != null) {
		body = KeYJavaASTFactory.labeledStatement(
			breakInnerLabel.getLabel(), body);
	    }
	    
	    final int updateSize = updates == null ? 0 : updates.size();
	    Statement innerBlockStatements[] = new Statement[updateSize + 2];
	    innerBlockStatements[0] = body;

	    if (updates != null) {
	        for (int copyStatements = 0; copyStatements < updateSize; copyStatements++) {
	            innerBlockStatements[copyStatements+1] = (ExpressionStatement) 
	                    updates.getExpressionAt(copyStatements);	        
	        }
	    }
	    innerBlockStatements[updateSize+1] = remainder;


	    final int initSize = inits == null ? 0 : inits.size();

	    final Statement outerBlockStatements[] = new Statement[initSize + 1];

	    if (inits != null) {
	        for (int copyStatements=0; copyStatements<initSize; copyStatements++) {
	            outerBlockStatements[copyStatements] = inits.getInits().get(copyStatements);
	        }
	    }
            
	    outerBlockStatements[initSize] = KeYJavaASTFactory.ifThen(
		    guard.getExpression(), innerBlockStatements);
	    
	    if (outerLabelNeeded() && breakOuterLabel!=null) {
		addChild(KeYJavaASTFactory.labeledStatement(
			breakOuterLabel.getLabel(), outerBlockStatements));
	    } else {
		addChild(KeYJavaASTFactory.block(outerBlockStatements));
	    }
     	    changed();
	} else {

            if (changeList.getFirst() == CHANGED) {
	    	changeList.removeFirst();
		For newLoop = KeYJavaASTFactory.forLoop(changeList);
	    	services.getSpecificationRepository().copyLoopInvariant(x, newLoop);
	    	addChild(newLoop);
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
        ExtList changeList = stack.peek();
        if (replaceBreakWithNoLabel == 0) {
            // the outermost loop
            Debug.log4jError("Enhanced for loops may not be toplevel in WhileLoopTransformation", null);
            doDefaultAction(x);
        } else {
            if (changeList.getFirst() == CHANGED) {
                changeList.removeFirst();
		EnhancedFor newLoop = KeYJavaASTFactory
			.enhancedForLoop(changeList);
                services.getSpecificationRepository().copyLoopInvariant(x, newLoop);
                addChild(newLoop);
                changed();
            } else {
                doDefaultAction(x);
            } 
        }
    }

    /* Performs the unwinding of the loop
     * Warning: The unwinding does not comply with the rule in the KeY book up to 100%
     * The difference is revealed by the following example:
     * <code> Label1:while(c){b}</code>
     * According to the KeY book the transformation should be
     * <code> if(c) l':{l'':{p#} Label1:while(c){b}}</code>
     * This implementation creates however.
     * <code> Label1:if(c) l':{l'':{p#} while(c){b}}</code>
     * Check if this is ok when labeled continue statements are involved.
     */
    public void performActionOnWhile(While x)     {
	ExtList changeList = stack.peek();
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
	            new LinkedHashMap<ProgramVariable, ProgramVariable>(), true, services);
	    replacer.start();
	    body = (Statement) replacer.result();
	    
	    if (innerLabelNeeded() && breakInnerLabel != null) {
		// an unlabeled continue needs to be handled with (replaced)
		body = KeYJavaASTFactory.labeledStatement(
			breakInnerLabel.getLabel(), body);
	    }
	    Then then = null;
	    StatementBlock block = KeYJavaASTFactory.block(body,
		    (Statement) root());
	    if (outerLabelNeeded() && breakOuterLabel != null) {
		// an unlabeled break occurs in the
		// while loop therefore we need a labeled statement
		then = KeYJavaASTFactory.thenBlock(KeYJavaASTFactory
			.labeledStatement(breakOuterLabel.getLabel(), block));

	    } else {
		then = KeYJavaASTFactory.thenBlock(block);
	    }
	    addChild(KeYJavaASTFactory.ifThen(guard, then));
	    changed();
	} else {
	    if (changeList.getFirst() == CHANGED) {
		changeList.removeFirst();
		//		Expression guard = (Expression) changeList.removeFirst(); ????
		Expression guard = ((Guard) changeList.removeFirst()).getExpression();
		Statement body = (Statement) (changeList.isEmpty() ?
					      null :
					      changeList.removeFirst());
		While newLoop = KeYJavaASTFactory.whileLoop(guard, body,
			x.getPositionInfo());
		services.getSpecificationRepository().copyLoopInvariant(x, newLoop);
		addChild(newLoop);
		changed();
	    } else {
		doDefaultAction(x);
	    }
	}
    }

    public void performActionOnDo(Do x)     {
	ExtList changeList = stack.peek();
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
		unwindedBody = KeYJavaASTFactory.labeledStatement(
			breakInnerLabel.getLabel(), body);
	    } else {
                unwindedBody = body;
            }
	    Statement resultStatement = null;
	    While newLoop = KeYJavaASTFactory.whileLoop(guard, x.getBody(),
		    x.getPositionInfo());
	    services.getSpecificationRepository().copyLoopInvariant(x, newLoop);
	    StatementBlock block = KeYJavaASTFactory.block(unwindedBody,
		    newLoop);

 	    if (outerLabelNeeded() && breakOuterLabel != null) {
		// an unlabeled break occurs in the
		// body therefore we need a labeled statement
		resultStatement = KeYJavaASTFactory.labeledStatement(
			breakOuterLabel.getLabel(), block);
	    } else {
		resultStatement = block;
	    }
	    addChild(resultStatement);
	    changed();
	} else {
	    if (changeList.getFirst() == CHANGED) {
		changeList.removeFirst();
		Statement body = changeList.removeFirstOccurrence(Statement.class);
		Guard g = changeList.removeFirstOccurrence(Guard.class);
		Expression guard = g == null ? null : g.getExpression();
		Do newLoop = KeYJavaASTFactory.doLoop(guard, body,
			x.getPositionInfo());
		services.getSpecificationRepository().copyLoopInvariant(x, newLoop);
		addChild(newLoop);
		changed();
	    } else {
		doDefaultAction(x);
	    }
	}
    }

    public void performActionOnIf(If x)     {
	DefaultAction def=new DefaultAction() {		
		ProgramElement createNewElement(ExtList changeList) {
		return KeYJavaASTFactory.ifStatement(changeList);
		}
	    };
	def.doAction(x);
    }
 
    public void performActionOnSwitch(Switch x)     {
	DefaultAction def=new DefaultAction() {		
		ProgramElement createNewElement(ExtList changeList) {
		return KeYJavaASTFactory.switchBlock(changeList);
		}
	    };
	def.doAction(x);
    }

    public void performActionOnTry(Try x)     {
	DefaultAction def=new DefaultAction() {		
		ProgramElement createNewElement(ExtList changeList) {
		return KeYJavaASTFactory.tryBlock(changeList);
		}
	    };
	def.doAction(x);
    }

    public void performActionOnLabeledStatement(LabeledStatement x) {
	Label l = null;
	ExtList changeList = stack.peek();
	if (changeList.getFirst() == CHANGED) {	    
	    changeList.removeFirst();	    
	    if (x.getLabel() != null) {
		l = (Label) changeList.removeFirst();
	    }
	    addChild(KeYJavaASTFactory.labeledStatement(changeList, l,
		    x.getPositionInfo()));
	    changed();
	} else {
	    doDefaultAction(x);
	}    
    } 

    public void performActionOnMethodFrame(MethodFrame x) {
	ExtList changeList = stack.peek();
	if (!changeList.isEmpty() && changeList.getFirst() == CHANGED) {	    
	    changeList.removeFirst();	    
	    if (x.getChildCount() == 3) {
		addChild(KeYJavaASTFactory.methodFrame(
			(IProgramVariable) changeList.get(0),
			(IExecutionContext) changeList.get(1),
			(StatementBlock) changeList.get(2),
			PositionInfo.UNDEFINED));

	    } else if (x.getChildCount() == 2) {
		addChild(KeYJavaASTFactory.methodFrame(
			(IExecutionContext) changeList.get(0),
			(StatementBlock) changeList.get(1),
			PositionInfo.UNDEFINED));
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
		return KeYJavaASTFactory.synchronizedBlock(changeList);
		}
	    };
	def.doAction(x);
    }
 

    public void performActionOnCopyAssignment(CopyAssignment x) {
	DefaultAction def=new DefaultAction() {		
		ProgramElement createNewElement(ExtList changeList) {
		return KeYJavaASTFactory.assign(changeList);
		}
	    };
	def.doAction(x);	
    }
    
    public void performActionOnThen(Then x)     {
	DefaultAction def=new DefaultAction() {		
		ProgramElement createNewElement(ExtList changeList) {
		return KeYJavaASTFactory.thenBlock(changeList);
		}
	    };
	def.doAction(x);
    }


    public void performActionOnElse(Else x)     {
	DefaultAction def=new DefaultAction() {		
		ProgramElement createNewElement(ExtList changeList) {
		return KeYJavaASTFactory.elseBlock(changeList);
		}
	    };
	def.doAction(x);
    }


    public void performActionOnCase(Case x)     {
	Expression e = null;
	ExtList changeList = stack.peek();
	if (changeList.getFirst() == CHANGED) {	    
	    changeList.removeFirst();	    
	    if (x.getExpression() != null) {
		e = (Expression) changeList.removeFirst();
	    }
	    addChild(KeYJavaASTFactory.caseBlock(changeList, e,
		    x.getPositionInfo()));
	    changed();
	} else {
	    doDefaultAction(x);
	}    
    }


    public void performActionOnCatch(Catch x)     {
	DefaultAction def=new DefaultAction() {		
		ProgramElement createNewElement(ExtList changeList) {
		return KeYJavaASTFactory.catchClause(changeList);
		}
	    };
	def.doAction(x);
    }


    public void performActionOnDefault(Default x)     {
	DefaultAction def=new DefaultAction() {		
		ProgramElement createNewElement(ExtList changeList) {
		return KeYJavaASTFactory.defaultBlock(changeList);
		}
	    };
	def.doAction(x);
    }


    public void performActionOnFinally(Finally x)     {
	DefaultAction def=new DefaultAction() {		
		ProgramElement createNewElement(ExtList changeList) {
		return KeYJavaASTFactory.finallyBlock(changeList);
		}
	    };
	def.doAction(x);
    }


    protected void changed() {
	ExtList list = stack.peek();
	if (list.getFirst() != CHANGED) {
	    list.addFirst(CHANGED);
	}
    }

    protected void addChild(SourceElement x) {
	stack.pop();
	ExtList list = stack.peek();
	list.add(x);
    }
    
    private abstract class DefaultAction {
	abstract ProgramElement createNewElement(ExtList changeList);

	private void addNewChild(ExtList changeList) {
	    addChild(createNewElement(changeList));
	    changed();	    
	}
	
	public void doAction(ProgramElement x) {
	    ExtList changeList = stack.peek();
	    if ( changeList.size () > 0 && 
		 changeList.getFirst() == CHANGED ) {	    
		changeList.removeFirst();
		changeList.add(x.getPositionInfo());
		addNewChild(changeList);
	    } else {
		doDefaultAction(x);
	    }	    
	}
    }
}
