// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.unittest;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.LoopInitializer;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.Equals;
import de.uka.ilkd.key.java.expression.operator.LessThan;
import de.uka.ilkd.key.java.expression.operator.NewArray;
import de.uka.ilkd.key.java.expression.operator.Plus;
import de.uka.ilkd.key.java.expression.operator.PostIncrement;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.Then;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair;
import de.uka.ilkd.key.unittest.ppAndJavaASTExtension.SyntacticalArrayType;
import de.uka.ilkd.key.java.reference.FieldReference;
/**
 * This class represents a NonRigidFunctionLocation beeing an array
 * 
 * @author mbender
 * 
 */
public class ArrayTermRep extends AbstractTermRepresentation {

    private ProgramVariable pvRead;
    private ProgramVariable pvWrite;
    final KeYJavaType intType;


    /**
     * @param up
     * @param serv
     * @param tce
     * @param trh
     */
    public ArrayTermRep(AssignmentPair up, Services serv,
            TestCodeExtractor tce, TermRepHandler trh) {
        super(up, serv, tce, trh);
        intType = serv.getJavaInfo().getTypeByName("int");
    }

    /**
     * This methods creates a new Array Term for a given AccessOperator and a
     * given 'index-variable'
     * 
     * @param term
     *            denotes the arrayAccessOperator
     * @param pv
     *            the index of the array
     * @return The Array Term that is the ne representation of the NRFL for an
     *         Array
     */
//    private Term createArrayAcc(Term term, ProgramVariable pv) {
//        final Term[] subs = new Term[2];
//        subs[1] = tf.createVariableTerm(pv);
//        if (term.arity() == 0) {
//            subs[0] = term;
//            return tf.createArrayTerm(ArrayOp.getArrayOp(term.sort()), subs);
//        } else {
//            if (term.sub(0).op() instanceof NonRigidFunctionLocation) {
//                subs[0] = trh.getReadRep(term.sub(0));
//
//            } else {
//                subs[0] = term.sub(0);
//            }
//            return tf.createArrayTerm(ArrayOp.getArrayOp(term.sub(0).sort()),
//                    subs);
//        }
//    }
    private Term createArrayAcc(Term term, ProgramVariable pv) {
	//Warning:The following code is actually unsafe because trh may be not sufficiently initialized
	Term arr = term.sub(0).op() instanceof NonRigidFunctionLocation?
			trh.getReadRep(term.sub(0)):
			term.sub(0);
	Term idx = term.sub(1).op() instanceof NonRigidFunctionLocation?
			trh.getReadRep(term.sub(1)):
			term.sub(1);
			
            return tf.createArrayTerm(ArrayOp.getArrayOp(term.sub(0).sort()),arr,new Term[]{idx});
    }


    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.key.unittest.AbstractTermRepresentation#createReadRep()
     */
    protected Term createReadRep() {
        //pvRead = getPV((LogicVariable) left.sub(1).op());
        //pvWrite = getPV((LogicVariable) left.sub(1).op());
        //return createArrayAcc(left, pvRead);
	if(readRep==null)
	    return createArrayAcc(left, pvRead);
	else
	    return readRep;
    }

    /**
     * This method 'converts' a LogicVariable to a ProgramVariable
     * 
     * @param lv
     *            the LogicVariable to convert
     * @return the created ProgramVariable
     */
    private ProgramVariable getPV(LogicVariable lv) {
        return new LocationVariable(createNewName(lv.name().toString()), intType);
    }

    /* Warning: this implementation is capable to translate only some array assignments. 
     * @see de.uka.ilkd.key.unittest.AbstractTermRepresentation#getWriteRep()
     */
    public Statement getWriteRep(Term right) {
	if(! (readRep.op() instanceof ArrayOp)){
	    throw new RuntimeException("readRep.op has bad type: "+readRep.op().getClass());
	}
	Term idx =readRep.sub(1);
	if(idx.op() instanceof LogicVariable){
	    //This is the case for handling a[i]=Expr, where i is quantified
	    final ProgramVariable idxPV = getPV((LogicVariable)idx.op());
	    final Term idxVarTerm = tf.createVariableTerm(idxPV);
    	    //convert the array reference to a suitable read representation if it is a NRFL
	    final Term leftArr = readRep.sub(0).op() instanceof NonRigidFunctionLocation? //This check is already done in createReadRep. It is probably not necessary here.
		    		trh.getReadRep(readRep.sub(0)):
		    		readRep.sub(0);
            final Term leftTrm = tf.createArrayTerm(ArrayOp.getArrayOp(readRep.sub(0).sort()), //This check is already done in createReadRep. It is probably not necessary here.
               	 				leftArr,
               	 				new Term[]{idxVarTerm});
            Term rightArr=null;
            //Replace quantified variable of right array if possible/necessary
	    if(right.op() instanceof ArrayOp){
		//This is the case for handling a[i]=b[i]
		rightArr = right.sub(0).op() instanceof NonRigidFunctionLocation? //This check is required
    			trh.getReadRep(right.sub(0)):
	    		right.sub(0);
    		Term rightIdx = null;
		if( right.sub(1).op() instanceof LogicVariable){
        		if(! idx.op().name().equals(right.sub(1).op().name())){
        		    throw new RuntimeException("Unhandled case:Expected assignment of the form a[i]=b[i] but got a[i]=b[j]. \n" +
        		    		"Don't know what to do with different indices.");
        		}
        		rightIdx = idxVarTerm;
		}else{
		    	rightIdx = right.sub(1);
		}
		right = tf.createArrayTerm(ArrayOp.getArrayOp(right.sub(0).sort()),
			rightArr,
			new Term[]{rightIdx});
	    }
	    	
	    	final Expression  leftExpr   = tce.convertToProgramElement(leftTrm);
	    	final Expression  rightExpr  = tce.convertToProgramElement(right);
	    	
	    	Statement forLoop = forLoopWithAssignment(leftExpr, rightExpr, idxPV);
	        
	        Statement createArray=null;
	        if(rightArr!=null){
	            //if the right expression is an array and the left is an uncreated array, then use the length of the right array to create the left one
	            FieldReference length = new FieldReference(serv.getJavaInfo().getArrayLength(), 
								(ReferencePrefix)(rightExpr.getFirstElement()));
	            createArray = conditionalArrayCreation(leftExpr,length );
	        }
	        
	        final Statement result = createArray==null ? 
	        	forLoop :
	        	new StatementBlock(new ImmutableArray<Statement>(new Statement[]{createArray, forLoop}));
	        
	        return result;

	}else{
	    //WARNING This branch does not handle all cases that can occur.
	    
	    
	    	//Convert the array and index if necessary from NonRigidFunctionLocation to the appropriate read representation
        	final Term leftArr = readRep.sub(0).op() instanceof NonRigidFunctionLocation? //This check is already done in createReadRep. It is probably not necessary here.
        	    			trh.getReadRep(readRep.sub(0)):
        	    			readRep.sub(0);
        	final Term idxVarTerm = readRep.sub(1).op()instanceof NonRigidFunctionLocation? //This check is already done in createReadRep. It is probably not necessary here.
    					trh.getReadRep(readRep.sub(1)):
    					readRep.sub(1);
        	//Reassemble the array term
        	final Term leftTrm = tf.createArrayTerm(ArrayOp.getArrayOp(readRep.sub(0).sort()),
           	 				leftArr,
           	 				new Term[]{idxVarTerm});
        	//Create a program representation 
	    	final Expression  leftExpr   = tce.convertToProgramElement(leftTrm);
	    	final Expression  idxVar   = tce.convertToProgramElement(idxVarTerm);
	    	final Expression  rightExpr  = tce.convertToProgramElement(right);


	        Statement createArray=null;
	        createArray = conditionalArrayCreation(leftExpr,new Plus(idxVar,new IntLiteral(1)) );
	        
	        CopyAssignment  assignment = new CopyAssignment(leftExpr,rightExpr);
	        
	        final Statement result = createArray==null ? 
	        	assignment :
	        	new StatementBlock(new ImmutableArray<Statement>(new Statement[]{createArray, assignment}));
	        
	        return result;
	}
    }
    
    /**This creates code of the form
     * if(ar == null) ar = new T[arrayLength];
     * This is to create an array at runtime (of the generated test) in the case that the array is null */
    private Statement conditionalArrayCreation(Expression arrayExpr, Expression arrayLength){

        final KeYJavaType at = arrayExpr.getKeYJavaType(serv, null);
        //((Expression) ((FieldReference) arrayExpr).getReferencePrefix()).getKeYJavaType(serv, null);
//        final NewArray ar = new NewArray(
//	        new Expression[] { arrayLength}, new TypeRef(
//	                getBaseType(at), at, null, 0);
        final Expression arr = (Expression)arrayExpr.getFirstElement();
        final NewArray newArr = new NewArray(
	        new Expression[] { arrayLength}, new TypeRef(at), at , null, 0);
        final Statement createArray = new If(new Equals(arr, NullLiteral.NULL), 
    			new Then(new CopyAssignment(arr,newArr)));
        return createArray;
    }
    
    private Statement forLoopWithAssignment(Expression leftExpr, Expression rightExpr, ProgramVariable idxPV){
//    	final LocationVariable length = new LocationVariable(
//		new ProgramElementName("length"), 
//		intType);
//        final Expression bound = tce.convertToProgramElement(
//        		tf.createAttributeTerm(length, leftArr));
    	
    	
    	Expression bound = new FieldReference(serv.getJavaInfo().getArrayLength(), 
    						(ReferencePrefix)leftExpr.getFirstElement());
        
        final CopyAssignment copyAssignment = new CopyAssignment(leftExpr, rightExpr); 
        
//        final VariableSpecification counterSpec = new VariableSpecification(
//        idxPV, new IntLiteral(0), intType);
//        final LocalVariableDeclaration counterDecl = new LocalVariableDeclaration(
//        new TypeRef(intType), counterSpec);
//        LoopInitializer[] loopInit =  new LoopInitializer[] { counterSpec}
        
        LoopInitializer[] loopInit= new LoopInitializer[] { new CopyAssignment(idxPV,new IntLiteral(0)) };
        
        Statement result = new For(loopInit, 
        			new LessThan(idxPV, bound),
        			new Expression[] { new PostIncrement(idxPV) },
        			copyAssignment);
        
        return result;

    }

    protected KeYJavaType getBaseType(final KeYJavaType arrayType) {
	return ((ArrayType) arrayType.getJavaType()).getBaseType()
	        .getKeYJavaType();
    }
}
