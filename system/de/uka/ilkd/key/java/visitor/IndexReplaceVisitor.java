// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.visitor;

import java.io.StringWriter;

import de.uka.ilkd.key.java.ArrayOfExpression;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaSourceElement;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ArrayReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.unittest.ppAndJavaASTExtension.CompilableJavaPP;
import de.uka.ilkd.key.util.ExtList;

/** Replaces array references a[expr] by a[dat] where dat is the concrete 
 * value for expr. This is needed for unit test generation.
 */
public class IndexReplaceVisitor extends CreatingASTVisitor{

    private ProgramElement result=null;
//    private KeYJavaType containingKJT=null
    private Expression[][] testLocation;
    private boolean singleTuple;
    private ProgramVariable partCounter;
//    private ProgramVariable[] lCounter;
    private ProgramVariable[] testArray;

    public IndexReplaceVisitor(ProgramElement pe, 
			       Expression[][] testLocation, 
			       boolean singleTuple, 
			       ProgramVariable partCounter, 
//			       ProgramVariable[] lCounter, 
			       ProgramVariable[] testArray,
                               Services services){
	super(pe, true, services);
	this.testLocation = testLocation;
	this.singleTuple = singleTuple;
	this.partCounter = partCounter;
//	this.lCounter = lCounter;
	this.testArray = testArray;
    }

    /** starts the walker*/
    public void start() {	
	stack.push(new ExtList());		
	walk(root());
	ExtList el= stack.peek();
	int i=0;
	while (!(el.get(i) instanceof ProgramElement)) {
	    i++;
	}
	result=(ProgramElement) stack.peek().get(i);
    }

    public ProgramElement result() { 	
	return result;
    }

    private Expression tryToReplaceByTestDatum(Expression e){
	int i = findLocIndex(e);
	if(i!=-1){
	    Expression testDat = singleTuple ? (Expression) testArray[i] : 
		(Expression) new ArrayReference(
		    testArray[i], 
		    new Expression[]{partCounter});
	    return testDat;
	}
	return e;
    }

    private int findLocIndex(Expression e){
	StringWriter sw = new StringWriter();
	CompilableJavaPP cjpp = new CompilableJavaPP(sw,true);
	for(int i = 0; i<testLocation.length; i++){
	    for(int j = 0; j<testLocation[i].length; j++){
		Expression e1 =testLocation[i][j];
		if(e1 instanceof JavaSourceElement && e instanceof JavaSourceElement){
		    String s1= ((JavaSourceElement)e1).toString(cjpp, sw);
        		if(s1.equals(((JavaSourceElement)e).toString(cjpp,sw))){
        		    return i;
        		}
		}else{//here follows the original code. But it's probably wrong because it leads to an invocation of PrettyPrinter.
        		if(testLocation[i][j].toString().equals(e.toString())){
        		    return i;
        		}
		}
	    }
	}
	return -1;
    }

    public void performActionOnArrayReference(ArrayReference x) {
        ExtList changeList = stack.peek();
        if (changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
	}
	changeList.removeFirstOccurrence(PositionInfo.class);
	ReferencePrefix rp = (ReferencePrefix) changeList.get(0);
	ArrayOfExpression aoe = x.getDimensionExpressions();
	Expression[] indices = new Expression[aoe.size()];
	for(int i=0; i<aoe.size(); i++){
	    indices[i] = tryToReplaceByTestDatum(aoe.getExpression(i));
	}
	ArrayReference ar = new ArrayReference(rp, indices);
	addChild(ar);
	changed();
    }

}
