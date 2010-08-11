// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.rule.soundness;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.RuntimeInstanceEC;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.VariableReference;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * Replace context schema variables (..  ...) with nested method frames and try
 * blocks, together with a number of statement skolem symbols to
 * simulate code fragments.
 */
public class ContextSkolemBuilder extends AbstractSkolemBuilder {

    // Statement SV that are used to represent enclosing code
    private final Statement[]    frameSVs;
    
    // Variables that describe the try-frame
    private final Statement      tryStatement;
    private ImmutableList<SchemaVariable> tryVariables =
    	ImmutableSLList.<SchemaVariable>nil();

    // Variables that describe the method frame
    private Statement            resultStatement  = null;
    private ImmutableList<SchemaVariable> resultVariables  = null;
    private SVTypeInfo           resultSVTypeInfo = null;

    // The insertion point of the whole frame
    private ImmutableList<Integer>        insertionPoint   = ImmutableSLList.<Integer>nil();

    public ContextSkolemBuilder ( SkolemSet p_oriSkolemSet,
				  Services  p_services ) {
	super ( p_oriSkolemSet, p_services );

    	frameSVs     = createStatementSVs ();
        tryStatement = createTryStatement();
    }

    public Iterator<SkolemSet> build () {
	ImmutableList<SkolemSet> res = ImmutableSLList.<SkolemSet>nil();

	Iterator<KeYJavaType> typeIt = getTypeCandidates ();
	while ( typeIt.hasNext () ) {
	    setupFrame ( typeIt.next () );
	    res = res.append ( createSkolemSet () );
	    resetMethodFrame ();
	}

	return res.iterator ();
    }

    
    private SkolemSet createSkolemSet () {
	final PosInProgram     pip = toPosInProgram ( insertionPoint );
        final SVInstantiations svi =
	    SVInstantiations.EMPTY_SVINSTANTIATIONS
	    .add ( pip, pip,
	           createDummyExecutionContext(), // TODO: something with execution context
		   resultStatement );

	SyntacticalReplaceVisitor srv = new SyntacticalReplaceVisitor
	    ( getServices (), svi, Constraint.BOTTOM, false, null, true, false );
	getOriginalFormula ().execPostOrder ( srv );

	SkolemSet res = getOriginalSkolemSet ()
	    .setFormula ( srv.getTerm () )
	    .addMissing ( resultVariables.iterator () );
		

	if ( resultSVTypeInfo != null )
	    res = res.setSVTypeInfos ( res.getSVTypeInfos ()
				       .addInfo ( resultSVTypeInfo ) );

	return res;
    }

    private PosInProgram toPosInProgram ( ImmutableList<Integer> p ) {
	Iterator<Integer> it  = p.iterator ();
	PosInProgram      res = PosInProgram.TOP;

	while ( it.hasNext () )
	    res = res.down ( it.next ().intValue () );

	return res;
    }

    private void addTryVariable(SchemaVariable p_var) {
        tryVariables = tryVariables.prepend ( p_var );
    }

    private void addResultVariable(SchemaVariable p_var) {
        resultVariables = resultVariables.prepend ( p_var );
    }

    /**
     * @return types that are possible result types of the method
     * frame to be created; <code>null</code> means that the method frame
     * should not have a result variable
     */
    private Iterator<KeYJavaType> getTypeCandidates () {
	final Type[] primitiveTypes = new Type[] {
	    PrimitiveType.JAVA_LONG,
	    //	    PrimitiveType.JAVA_DOUBLE,
	    PrimitiveType.JAVA_BOOLEAN
	};
	
	ImmutableList<KeYJavaType> list = ImmutableSLList.<KeYJavaType>nil();
	int               i;

	for ( i = 0; i != primitiveTypes.length; ++i )
	    list = list.prepend
		( getJavaInfo ().getKeYJavaType ( primitiveTypes[i] ) );

        // <code>null</code> (i.e. no result variable) is added as the
        // first possibility to consider (also see class <code>POBuilder</code>)
	list = list.prepend ( (KeYJavaType)null );

	return list.iterator ();	
    }

    /**
     * Create the try frame
     */
    private Try createTryStatement() {
        final Catch          catchObj     = createCatchBlock();
        
        final Statement[] tryBodyStmts = new Statement[2];
        // an empty statement to mark the position of insertion
        tryBodyStmts[0] = new EmptyStatement ();
        tryBodyStmts[1] = getFrameStatementSV(0);

        addTryVariable((SchemaVariable)getFrameStatementSV(0));

        final StatementBlock tryBody      = new StatementBlock ( tryBodyStmts );
        up ( 0 );
	up ( 0 );
        
        return new Try ( tryBody, new Branch[] { catchObj } );
    }

    /**
     * Create the catch block of the try block
     */
    private Catch createCatchBlock() {
        final ParameterDeclaration thDecl = createTryGuardVariable();
        final StatementBlock       catchBody =
            new StatementBlock ( getFrameStatementSV(1) );

        addTryVariable((SchemaVariable)getFrameStatementSV(1));
            
        return new Catch ( thDecl, catchBody );
    }

    /**
     * Create the guard variable of the catch leg of the try block.
     * @return a <code>ParameterDeclaration</code> of the variable
     */
    private ParameterDeclaration createTryGuardVariable() {
        final KeYJavaType           thType =
            getJavaInfo ().getTypeByClassName ( "java.lang.Throwable" );
        final TypeRef               thRef  = new TypeRef ( thType );
        
        final ProgramElementName    thName = createUniquePEName("frame_th");
        final SchemaVariable        thVar  =
            SchemaVariableFactory.createProgramSV ( thName,
        					    ProgramSVSort.VARIABLE,
        					    false );
        final VariableSpecification thSpec = new VariableSpecification
            ( (IProgramVariable)thVar, thType );
        final ParameterDeclaration  thDecl =
            new ParameterDeclaration ( new Modifier [0], thRef, thSpec, false );
        
        addTryVariable(thVar);

        return thDecl;
    }

    /**
     * Create the complete frame statement for a given result type
     */
    private void setupFrame ( KeYJavaType p_resultType ) {
	resultVariables = tryVariables;

        final MethodFrame mfObj = createMethodFrame(p_resultType);

	final Statement[] topLevelStmts = new Statement[2];
	topLevelStmts[0] = mfObj;
	topLevelStmts[1] = getFrameStatementSV(2);

        addResultVariable((SchemaVariable)getFrameStatementSV(2));

	resultStatement = new StatementBlock ( topLevelStmts );
	up ( 0 );
    }

    /**
     * Create the method frame statement
     */
    private MethodFrame createMethodFrame(KeYJavaType p_resultType) {
        final IProgramVariable resVar = createResultVariable(p_resultType);
        
        final StatementBlock   mfBody = new StatementBlock ( tryStatement );
        up ( 0 );

        final MethodFrame      mfObj  = new MethodFrame
            ( resVar, createDummyExecutionContext (), mfBody );
        up ( p_resultType == null ? 1 : 2 );

        return mfObj;
    }

    /**
     * Create the result variable of the method frame
     * @param p_resultType the type the variable should have, or
     * <code>null</code> if the method frame is not to be given a result
     * variable at all 
     * @return the result variable, or <code>null</code> for
     * <code>p_resultType==null</code>
     */
    private IProgramVariable createResultVariable(KeYJavaType p_resultType) {
        if ( p_resultType == null ) {
            resultSVTypeInfo = null;
            return null;
        }

        final IProgramVariable res = (IProgramVariable)SchemaVariableFactory
	    .createProgramSV ( createUniquePEName("frame_res"),
			       ProgramSVSort.VARIABLE,
			       false );

    	resultSVTypeInfo = new SVTypeInfo ( ((SchemaVariable)res),
					    p_resultType );
        addResultVariable((SchemaVariable)res);

        return res;
    }

    /**
     * HACK to create an execution context somehow
     */
    private ExecutionContext createDummyExecutionContext () {
	ProgramElementName refName = new ProgramElementName ( "ref" );
	ProgramVariable    refVar  = new LocationVariable
	    ( refName, getJavaInfo ().getJavaLangObject () );
	VariableReference  ref     = new VariableReference  ( refVar );	
	ExecutionContext  context = new ExecutionContext
	    ( new TypeRef ( getJavaInfo ().getJavaLangObject () ), null, 
		    new RuntimeInstanceEC(ref));
	return context;
    }

    private void resetMethodFrame () {
	insertionPoint = insertionPoint.tail ().tail ().tail ();
    }

    /**
     * @param p_num the number of the SV to return;
     * currently <code>p_num</code> has to be an element of [0, 3)
     * @return frame statement SV with number <code>p_num</code>
     */
    private Statement getFrameStatementSV ( int p_num ) {
    	return frameSVs[p_num];
    }

    /**
     * Setup frame SV
     */
    private Statement[] createStatementSVs () {
 	int                i     = 3;
	final Statement[]  res   = new Statement [ i ];

	while ( i-- != 0 ) {
	    final ProgramElementName name = createUniquePEName ( "frame_s" + i );
	    res[i] = (Statement)SchemaVariableFactory
		.createProgramSV ( name,
				   ProgramSVSort.STATEMENT,
				   false );
	}
	
	return res;
    }

    /**
     * Modify the <code>insertionPoint</code> by increasing the depth by one;
     * this means that the old frame is made a direct subtree of the new frame  
     */
    private void up ( int p ) {
	final Integer t = new Integer ( p );
	insertionPoint = insertionPoint.prepend ( t );
    }

}
