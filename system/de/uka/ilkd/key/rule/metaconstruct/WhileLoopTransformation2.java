// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
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

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.recoderext.TestGenerationModelTransformer;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.ExtList;

/** @author gladisch;
 * Used by class UnwindLoopBounded. This class augments the behavior of class
 * WhileLoopTransformation for test generation purpose. The number of loop unwindings
 * is controlled by the static field unwindings. An example is given in the documentation
 * of the method performActionOnWhile. 
 * This class has a dependency on ..key.java.recoderext.TestGenerationModelTransformer.  
 * 
 */
public class WhileLoopTransformation2 extends WhileLoopTransformation {

    /** Global variable that determins how often to unwind the loop. */
    public static int unwindings=1;


    /** creates the WhileLoopTransformation for the transformation mode
     * @param root the ProgramElement where to begin
     * @param outerLabel the ProgramElementName of the outer label 
     * @param innerLabel the ProgramElementName of the inner label 
     */
    public WhileLoopTransformation2(ProgramElement root, 
				   ProgramElementName outerLabel,
				   ProgramElementName innerLabel,
                                   Services services) {
	super(root, outerLabel, innerLabel, services);
    }

    /** creates the  WhileLoopTransformation for the check mode
     * @param root the ProgramElement where to begin
     * @param inst the SVInstantiations if available
     */
    public WhileLoopTransformation2(ProgramElement root, 
                                   SVInstantiations inst, 
                                   Services services) {
	super(root, inst, services);
    }



   /*This method performs the unwinding of the while loop. The method is copied
    * from the implementation of its bases class and modified.
    * Warning: The unwinding creates not compilable java code, because
    * It uses the same name of a lable multiple times. E.g. it creates
    * code of the form label1:{ label1: { break label1 } }. However the calculus rules
    * for handling the labeled break statement will make the execution jump
    * to the innermost labeled block which in the end results in the desired behavior.
    * 
    *  Here is an example:
    *  / *@ public normal_behavior
	requires i<4 && j<4;
	ensures \result==true;
       @* /
       public boolean loopWithLabelBreakContinue(int i, int j){
       MyLabel:{while(i<10){
		i++;
		if(i==j) break;
		if(i==j) break MyLabel;
		if(i<j+1) continue;
		j=j+2;
	        }
               }
       return i==j;
      }
    * Unwinding of the loop results in the following code.
    *  Look for the Label called INNER_LABEL whichoccurs multiple times
    *  // Result after using the bounded unwinding rule with 2 uwinding
   {_i:=i || _j:=j || exc:=null}
   \<{MyLabel: OUTER_LABEL:
           if (_i<10) { INNER_LABEL
           : INNER_LABEL
             : {  _i++;
                 if (_i==_j) break OUTER_LABEL;
                 if (_i==_j) break MyLabel;
                 if (_i<_j+1)break INNER_LABEL;
               _j=_j+2;
             }
             if (_i<10) { INNER_LABEL
             : { _i++;
                 if (_i==_j) break OUTER_LABEL;
                 if (_i==_j) break MyLabel;
                 if (_i<_j+1) break INNER_LABEL;
                 _j=_j+2;
               }
               if (_i<10)
                  java.lang.Object.<loopAbstractionMethod>(hashCode);
             }
           }
            return 
           _i==_j;
         }\> (result = TRUE & exc = null)
    * The implicit method loopAbstractionMethod(hashCode) is used to terminate the unwinding of the loop. 
    * The idea behind the method is that nothing is known about the method and
    * therefore symbolic execution does not proceed where it encounters this method.
    * In order to make sure that different loops are not mapped to the same statement
    * the loopAbstractionMethod takes a hash value of the loop as argument.
    */
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
	    //Statement result = (Statement)root();
	    TypeRef typeRef= new TypeRef(services.getJavaInfo().getKeYJavaType("java.lang.Object"));
	    ProgramElementName mn = new ProgramElementName(TestGenerationModelTransformer.IMPLICIT_ABSTRACTION_METHOD);
	    int hash = root().hashCode();
	    ImmutableArray<Expression> args = new ImmutableArray<Expression>(new IntLiteral(""+hash));
	    Statement res = new MethodReference(args, mn , typeRef);
	    
	    res = new If(guard, new Then(res));
	    
	    for(int i=0;i<unwindings;i++){
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
        	    //Then then = null;
        	    StatementBlock block = new StatementBlock
        		(new ImmutableArray<Statement>(
        			new Statement[]{body, res}));

        	   
        	    res = new If(guard, new Then(block));
	    }
	    //Embed in outer labeled block
	    if (outerLabelNeeded() && breakOuterLabel != null) {
		// an unlabeled break occurs in the
		// while loop therefore we need a labeled statement
		res = new LabeledStatement(breakOuterLabel.getLabel(), res);
	    }
	    addChild(res);
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

}

/* THIS IS AN EXAMPLE 
/ *@ public normal_behavior
	requires i<4 && j<4;
	ensures \result==true;
@* /
public boolean loopWithLabelBreakContinue(int i, int j){
MyLabel:{
	while(i<10){
		i++;
		if(i==j) break;
		if(i==j) break MyLabel;
		if(i<j+1) continue;
		j=j+2;
	}
}
return i==j;
}
*/
