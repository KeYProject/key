// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.soundness;

import java.util.Stack;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.expression.ExpressionStatement;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.AbstractProgramElement;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;


/**
 * Perform static type checking on java blocks
 */
public class StaticProgramChecker
    extends de.uka.ilkd.key.java.visitor.JavaASTVisitor {

    /**
     * The program is traversed in depth-left-first order. This stack
     * contains the types of all maximum subtrees of the AST that have
     * already been left
     */
    private final Stack typeStack       = new Stack ();

    /**
     * The result types of all method frames that enclose the current
     * position within the AST
     */
    private final Stack returnTypeStack = new Stack ();

    /**
     * Symbolic constant that is inserted in <code>typeStack</code>
     * for unknown types. Unknown types are caused by untyped schema
     * variables
     */
    private final KeYJavaType UNKNOWN =
	new KeYJavaType ( PrimitiveType.PROGRAM_SV );

    /**
     * Symbolic constant that is inserted for subtrees of the AST that
     * do not have a result (e.g. statements)
     */
    private final KeYJavaType VOID    =	new KeYJavaType ();

    /**
     * Symbolic constant that is pushed on <code>typeStack</code>
     * whenever a subtree of the AST is entered. This level mark is
     * mostly used to make the traversal more robust against altered
     * arities of nodes, etc.
     */
    private final KeYJavaType LEVEL   = new KeYJavaType ();

    private final Services services;

    private final Logger logger = Logger.getLogger ( "key.taclet_soundness" );

    public StaticProgramChecker ( ProgramElement p_root,
				  Services       p_services ) {
	super(p_root);
	services = p_services;
    }

    /**
     * Check an element of an array using the method
     * <code>checkNonVoidType</code>
     */
    private boolean checkNonVoidType ( ArrayOfKeYJavaType p_array,
				       int                p_pos,
				       boolean            p_push ) {
	return checkNonVoidType ( p_array.getKeYJavaType ( p_pos ), p_push );
    }

    /**
     * Ensure that the given type <code>p_type</code> is a real Java
     * type, and that the type is in particular not unknown or void
     * @param p_type the type object to test
     * @param p_push if this parameter is true and the given type is
     * unknown, then the unknown-type constant is pushed as result on
     * the type stack
     * @return false if the given type is unknown, true if the type is
     * a legal (real) Java type
     * @throws StaticTypeException iff the given type is void
     */
    private boolean checkNonVoidType ( KeYJavaType p_type,
				       boolean     p_push ) {
	Debug.assertFalse( p_type == null,  "Type is null");
	Debug.assertFalse( p_type == LEVEL,
			   "The level mark was tested as a type");
					
	if ( p_type == UNKNOWN ) {
	    if ( p_push )
		pushUnknown ();
	    return false;
	}
	if ( p_type == VOID )
	    raiseTypeError ();
	return true;
    }

    /**
     * Check all elements of an array using the method
     * <code>checkNonVoidType</code>.
     * @param p_push if this parameter is true and the array contains
     * the unknown-type constant, then the unknown-type constant is
     * pushed as result on the type stack (at most once)
     * @return false if the the array contains the unknown-type
     * constant, true if all elements of the array are legal (real)
     * Java types
     */
    private boolean checkNonVoidTypeArray ( ArrayOfKeYJavaType p_array,
					    boolean            p_push ) {
	int     i   = p_array.size ();
	boolean ret = true;
	while ( i-- != 0 ) {
	    if ( !checkNonVoidType ( p_array, i, p_push ) )
		p_push = ret = false;
	}
	return ret;
    }

    /**
     * Ensure that the element of <code>p_array</code> at index
     * <code>p_pos</code> is a suitable type of a statement (i.e. void
     * or unknown), or that otherwise the particular child of the
     * program element <code>p_progEl</code> is an expression
     * statement
     */
    private void checkStatement ( NonTerminalProgramElement p_progEl,
				  ArrayOfKeYJavaType        p_array,
				  int                       p_pos ) {
	if ( !( p_array.getKeYJavaType ( p_pos ) == VOID ||
		p_array.getKeYJavaType ( p_pos ) == UNKNOWN ||
		p_progEl.getChildAt ( p_pos ) instanceof ExpressionStatement ) )
	    raiseTypeError ();	    
    }

    /** the action that is performed just before leaving the node the
     * last time 
     */
    protected void doAction(ProgramElement node) {
	node.visit(this);
    }

    public void doAssignment () {
	// narrowing of constant expressions is not yet performed
	final ArrayOfKeYJavaType types = popAndCheckType ( 2, true );
	if ( types != null ) {
	    if ( getTypeConverter ().isAssignableTo
		 ( types.getKeYJavaType ( 1 ), types.getKeYJavaType ( 0 ) ) )
		pushResult ( types.getKeYJavaType ( 0 ) );
	    else
		raiseTypeError ();
	}
    }

    /**
     * Call the binary type promotion method of the type converter
     * class on the two elements of the array <code>types</code>,
     * which has to have length <code>2</code>. The result in pushed
     * on the type stack
     */
    private void doBinaryPromotion(ArrayOfKeYJavaType p_types) {
	Debug.assertTrue ( p_types.size() == 2,
	                   "doBinaryPromotion: Don't know what to do " +
	                   "with array of length " + p_types.size() );

        doBinaryPromotion(p_types.getKeYJavaType ( 0 ),
			  p_types.getKeYJavaType ( 1 ));
    }

    /**
     * Call the binary type promotion method of the type converter
     * class on the two given types. The result in pushed on the type
     * stack
     */
    private void doBinaryPromotion( KeYJavaType p_type0, KeYJavaType p_type1) {
        KeYJavaType promotedType = null;
        try {
            promotedType =
                getTypeConverter ().getPromotedType ( p_type0, p_type1 );
        } catch ( Exception e ) {
            raiseTypeError ();
        }
        pushResult ( promotedType );
    }

    private void doBitwisePromotion ( Operator x ) {
	final ArrayOfKeYJavaType types = popAndCheckType ( 2, true );
	if ( types != null ) {
	    if ( !( getTypeConverter ().isArithmeticType
		    ( types.getKeYJavaType ( 0 ) ) &&
		    getTypeConverter ().isArithmeticType
		    ( types.getKeYJavaType ( 1 ) ) ||
		    getTypeConverter ().isBooleanType
		    ( types.getKeYJavaType ( 0 ) ) &&
		    getTypeConverter ().isBooleanType
		    ( types.getKeYJavaType ( 1 ) ) ) )
		raiseTypeError ();
            doBinaryPromotion(types);
	}
    }

    /**
     * Cast the topmost element of the type stack to the given type
     * <code>p_targetType</code>, and push the type
     * <code>p_targetType</code> as a result on the stack
     */
    private void doCast ( KeYJavaType p_targetType ) {
	checkNonVoidType ( p_targetType, false );
	final ArrayOfKeYJavaType types = popAndCheckType ( 1, false );
	if ( types != null ) {
	    if ( getTypeConverter ().isCastingTo
		 ( types.getKeYJavaType ( 0 ), p_targetType ) )
		pushResult ( p_targetType );
	    else
		raiseTypeError ();		
	} else
	    pushResult ( p_targetType );
    }

    private void doComparison ( ComparativeOperator x ) {
	final ArrayOfKeYJavaType types = popKeYJavaTypes ( 2 );
	if ( checkNonVoidType ( types, 0, false ) ) {
	    if ( !getTypeConverter ().isArithmeticType
		 ( types.getKeYJavaType ( 0 ) ) )
		raiseTypeError ();
	}
	if ( checkNonVoidType ( types, 1, false ) ) {
	    if ( !getTypeConverter ().isArithmeticType
		 ( types.getKeYJavaType ( 1 ) ) )
		raiseTypeError ();
	}
	pushBoolean ();
    }

    private void doCompoundAssignment ( Assignment x ) {
	popLevelMark ();
	final ArrayOfKeYJavaType types = popKeYJavaTypes ( 2 );
	push ( types.getKeYJavaType ( 1 ) );
	doCast ( types.getKeYJavaType ( 0 ) );
    }

    private void doDecrementsIncrements ( Assignment x ) {
	final ArrayOfKeYJavaType types = popAndCheckType ( 1, true );
	if ( types != null ) {
	    if ( !getTypeConverter ().isArithmeticType
		 ( types.getKeYJavaType ( 0 ) ) )
		raiseTypeError ();
	    pushResult ( types.getKeYJavaType ( 0 ) );
	}
    }

    protected void doDefaultAction(SourceElement x) {
	// Different kinds of literals and variable declarations are
	// treated directly

	if ( x instanceof Literal )
	    doLiteral ( (Literal)x );
	else if ( x instanceof VariableDeclaration )
	    doVariableDeclaration ( (VariableDeclaration)x );
	else
	    // Catch all
	    Debug.assertTrue
	        ( false, "Unknown source element: " + x + " " + x.getClass () );
    }

    private void doEquals ( ComparativeOperator x ) {
	final ArrayOfKeYJavaType types = popKeYJavaTypes ( 2 );
	if ( checkNonVoidType ( types, 0, false ) ) {
	    if ( checkNonVoidType ( types, 1, false ) ) {
		if ( !( getTypeConverter ().isArithmeticType
			( types.getKeYJavaType ( 0 ) ) &&
			getTypeConverter ().isArithmeticType
			( types.getKeYJavaType ( 1 ) ) ||
			getTypeConverter ().isBooleanType
			( types.getKeYJavaType ( 0 ) ) &&
			getTypeConverter ().isBooleanType
			( types.getKeYJavaType ( 1 ) ) ||
			( getTypeConverter ().isReferenceType
			  ( types.getKeYJavaType ( 0 ) ) ||
			  getTypeConverter ().isNullType
			  ( types.getKeYJavaType ( 0 ) ) ) &&
			( getTypeConverter ().isReferenceType
			  ( types.getKeYJavaType ( 1 ) ) ||
			  getTypeConverter ().isNullType
			  ( types.getKeYJavaType ( 1 ) ) ) ) )
		    raiseTypeError ();
	    } else {
		if ( !( getTypeConverter ().isArithmeticType
			( types.getKeYJavaType ( 0 ) ) ||
			getTypeConverter ().isBooleanType
			( types.getKeYJavaType ( 0 ) ) ||
			getTypeConverter ().isReferenceType
			( types.getKeYJavaType ( 0 ) ) ||
			getTypeConverter ().isNullType
			( types.getKeYJavaType ( 
			0 ) ) ) )
		    raiseTypeError ();
	    }
	} else if ( checkNonVoidType ( types, 1, false ) ) {
	    if ( !( getTypeConverter ().isArithmeticType
		    ( types.getKeYJavaType ( 1 ) ) ||
		    getTypeConverter ().isBooleanType
		    ( types.getKeYJavaType ( 1 ) ) ||
		    getTypeConverter ().isReferenceType
		    ( types.getKeYJavaType ( 1 ) ) ||
		    getTypeConverter ().isNullType
		    ( types.getKeYJavaType ( 1 ) ) ) )
		raiseTypeError ();
	}
	pushBoolean ();
    }

    /**
     * Check an <code>instanceof</code> expression
     */
    private void doInstanceof ( TypeOperator x ) {
	final ArrayOfKeYJavaType types = popKeYJavaTypes ( 2 );
	if ( checkNonVoidType ( types, 0, false ) ) {
	    if ( !( getTypeConverter ().isReferenceType
		    ( types.getKeYJavaType ( 0 ) ) ||
		    getTypeConverter ().isNullType
		    ( types.getKeYJavaType ( 0 ) ) ) )
		raiseTypeError ();
	}
	if ( checkNonVoidType ( types, 1, false ) ) {
	    if ( !getTypeConverter ().isReferenceType
		 ( types.getKeYJavaType ( 1 ) ) )
		raiseTypeError ();
	}
	if ( checkNonVoidType ( types, 0, false ) &&
	     checkNonVoidType ( types, 1, false ) ) {
	    if ( !getTypeConverter ().isCastingTo
		 ( types.getKeYJavaType ( 0 ),
		   types.getKeYJavaType ( 1 ) ) )
		raiseTypeError ();		
	}
	pushBoolean ();
    }

    private void doLiteral ( Literal x ) {
	pushResult ( x.getKeYJavaType ( getServices () ) );
    }

    private void doLogicalPromotion ( Operator x ) {
	final ArrayOfKeYJavaType types = popAndCheckType ( 2, true );
	if ( types != null ) {
	    if ( !getTypeConverter ().isBooleanType
		 ( types.getKeYJavaType ( 0 ) ) ||
		 !getTypeConverter ().isBooleanType
		 ( types.getKeYJavaType ( 1 ) ) )
		raiseTypeError ();
	    doBinaryPromotion(types);
	}
    }

    private void doNumericPromotion ( Operator x ) {
	final ArrayOfKeYJavaType types = popAndCheckType ( 2, true );
	if ( types != null ) {
	    if ( !getTypeConverter ().isArithmeticType
		 ( types.getKeYJavaType ( 0 ) ) ||
		 !getTypeConverter ().isArithmeticType
		 ( types.getKeYJavaType ( 1 ) ) )
		raiseTypeError ();		
	    doBinaryPromotion(types);
	}
    }

    private void doPositiveNegative ( Operator x ) {
	final ArrayOfKeYJavaType types = popAndCheckType ( 1, true );
	if ( types != null ) {
	    if ( !getTypeConverter ().isArithmeticType
		 ( types.getKeYJavaType ( 0 ) ) )
		raiseTypeError ();
            doUnaryPromotion(types);
	}
    }

    protected void doSchemaVariable ( SchemaVariable x ) {
	pushUnknown (); //todo
    }

    private void doShiftPromotion ( Operator x ) {
	final ArrayOfKeYJavaType types = popKeYJavaTypes ( 2 );
	if ( checkNonVoidType ( types, 0, true ) ) {
	    if ( !getTypeConverter ().isIntegralType
		 ( types.getKeYJavaType ( 0 ) ) )
		raiseTypeError ();
            doUnaryPromotion(types);
	}
	if ( checkNonVoidType ( types, 1, false ) ) {
	    if ( !getTypeConverter ().isIntegralType
		 ( types.getKeYJavaType ( 1 ) ) )
		raiseTypeError ();
	}
    }

    // HACK
    private void doStandardStatement (NonTerminalProgramElement x) {
	pushVoid ();	
    }

    /**
     * Ensure that all subtrees of the AST below the current node are
     * represent statements compatible with the given program element
     * <code>x</code>
     */
    private void doStatements ( NonTerminalProgramElement x ) {
	final ArrayOfKeYJavaType types = popChildrenWithArityCheck (x);
	int                      i     = types.size ();
	
	while ( i-- != 0 )
	    checkStatement ( x, types, i );
	pushVoid ();
    }

    /**
     * Call the unary type promotion method of the type converter
     * class on the element of the array <code>types</code>, which has
     * to have length <code>1</code>. The result in pushed on the type
     * stack
     */
    private void doUnaryPromotion(ArrayOfKeYJavaType p_types) {
	Debug.assertTrue ( p_types.size() == 1,
	                   "doUnaryPromotion: Don't know what to do " +
	                   "with array of length " + p_types.size() );

        final KeYJavaType type = p_types.getKeYJavaType ( 0 );
	KeYJavaType promotedType = null;
        try {
            promotedType = getTypeConverter ().getPromotedType ( type );
        } catch ( Exception e ) {
            raiseTypeError ();
        }
	pushResult ( promotedType );
    }

    private void doVariableDeclaration ( VariableDeclaration x ) {
    	doVariableDeclarationHelp(x);
	pushVoid ();
    }

    /**
     * @return the type of an arbitrary variable specification of the
     * given variable declaration
     */
    private KeYJavaType doVariableDeclarationHelp(VariableDeclaration x) {
        final ArrayOfKeYJavaType types = popChildrenWithArityCheck(x);
        int                      i;
        KeYJavaType              type  = null;

        for ( i = 0; i != types.size (); ++i ) {
            if ( x.getChildAt ( i ) instanceof VariableSpecification ) {
        	if ( checkNonVoidType ( types, i, false ) && type != null ) {
        	    if ( !validSpecificationType ( types.getKeYJavaType ( i ),
        					   type ) )
        		raiseTypeError ();
        	}
            } else if ( x.getChildAt ( i ) instanceof TypeReference ) {
        	if ( checkNonVoidType ( types, i, false ) )
        	    type = types.getKeYJavaType ( i );
            }
        }
        return type;
    }

    protected JavaInfo getJavaInfo () {
	return getServices ().getJavaInfo ();
    }

    protected Services getServices () {
	return services;
    }

    public TypeConverter getTypeConverter () {
	return getServices ().getTypeConverter ();
    }

    public void performActionOnAbstractProgramElement(AbstractProgramElement x) {
	walk ( x.getConcreteProgramElement ( getServices () ) );
	// the result has to be inserted one level mark below
        propagateSingleResult();
    }

    public void performActionOnBinaryAnd(BinaryAnd x)     {
	doBitwisePromotion ( x );
    }

    public void performActionOnBinaryAndAssignment(BinaryAndAssignment x)     {
	prepareCompoundAssignment ( x );
	performActionOnBinaryAnd ( null );
	doCompoundAssignment ( x );
    }

    public void performActionOnBinaryNot(BinaryNot x)     {
	ArrayOfKeYJavaType types = popAndCheckType ( 1, true );
	if ( types != null ) {
	    if ( !getTypeConverter ().isArithmeticType
		 ( types.getKeYJavaType ( 0 ) ) )
		raiseTypeError ();
            doUnaryPromotion(types);
	}
    }

    public void performActionOnBinaryOr(BinaryOr x)     {
	doBitwisePromotion ( x );
    }

    public void performActionOnBinaryOrAssignment(BinaryOrAssignment x)     {
	prepareCompoundAssignment ( x );
	performActionOnBinaryOr ( null );
	doCompoundAssignment ( x );
    }

    public void performActionOnBinaryXOr(BinaryXOr x)     {
	doBitwisePromotion ( x );
    }

    public void performActionOnBinaryXOrAssignment(BinaryXOrAssignment x)     {
	prepareCompoundAssignment ( x );
	performActionOnBinaryXOr ( null );
	doCompoundAssignment ( x );
    }

    public void performActionOnBreak(Break x) {
	doStatements (x);
    }

    public void performActionOnCatch(Catch x)     {
	ArrayOfKeYJavaType types = popKeYJavaTypes ( 2 );
	if ( checkNonVoidType ( types, 0, false ) ) {
	    KeYJavaType     th      =
		getJavaInfo ().getTypeByClassName ( "java.lang.Throwable" );
	    Sort            thSort  = th.getSort ();
	    Sort            parSort = types.getKeYJavaType ( 0 ).getSort ();

	    if ( !parSort.extendsTrans ( thSort ) )
		raiseTypeError ();
	}
	checkStatement ( x, types, 1 );
	pushVoid ();
    }

    public void performActionOnConditional(Conditional x)     {
	ArrayOfKeYJavaType types = popKeYJavaTypes ( 3 );
	if ( checkNonVoidType ( types, 0, false ) ) {
	    if ( !getTypeConverter ().isBooleanType
		 ( types.getKeYJavaType ( 0 ) ) )
		raiseTypeError ();
	}
	if ( checkNonVoidType ( types, 1, true ) &&
	     checkNonVoidType ( types, 2, true ) ) {
	    KeYJavaType a   = types.getKeYJavaType ( 1 );
	    KeYJavaType b   = types.getKeYJavaType ( 2 );
	    Type        ajt = a.getJavaType ();
	    Type        bjt = b.getJavaType ();
	    if ( a == b ) {
		pushResult ( a );
		return;
	    } else if ( getTypeConverter ().isArithmeticType ( a ) &&
			getTypeConverter ().isArithmeticType ( b ) ) {
		if ( ajt == PrimitiveType.JAVA_BYTE &&
		     bjt == PrimitiveType.JAVA_SHORT ||
		     bjt == PrimitiveType.JAVA_BYTE &&
		     ajt == PrimitiveType.JAVA_SHORT ) {
		    pushResult ( PrimitiveType.JAVA_SHORT );
		    return;
		} else {
		    // constant expressions are not yet considered
		    doBinaryPromotion ( a, b );
		    return;
		}
	    } else if ( getTypeConverter ().isNullType ( a ) &&
			getTypeConverter ().isReferenceType ( b ) ) {
		pushResult ( b );
		return;
	    } else if ( getTypeConverter ().isNullType ( b ) &&
			getTypeConverter ().isReferenceType ( a ) ) {
		pushResult ( a );
		return;
	    } else if ( getTypeConverter ().isReferenceType ( a ) &&
		      getTypeConverter ().isReferenceType ( b ) ) {
		if ( getTypeConverter ().isAssignableTo ( a, b ) ) {
		    pushResult ( b );
		    return;
		} else if ( getTypeConverter ().isAssignableTo ( b, a ) ) {
		    pushResult ( a );
		    return;
		}
	    }
		
	    raiseTypeError ();
	}
    }

    public void performActionOnContinue(Continue x)     {
	doStatements (x);
    }
    
    public void performActionOnCopyAssignment(CopyAssignment x) {
	doAssignment ();
    }

    public void performActionOnDivide(Divide x)     {
	doNumericPromotion ( x );
    }

    public void performActionOnDivideAssignment(DivideAssignment x)     {
	prepareCompoundAssignment ( x );
	performActionOnDivide ( null );
	doCompoundAssignment ( x );
    }

    public void performActionOnDo(Do x)     {
	ArrayOfKeYJavaType types = popKeYJavaTypes ( 2 );
	if ( checkNonVoidType ( types, 1, false ) ) {
	    if ( !getTypeConverter ().isBooleanType
		 ( types.getKeYJavaType ( 1 ) ) )
		raiseTypeError ();
	}
	checkStatement ( x, types, 0 );
	pushVoid ();	
    }

    public void performActionOnElse(Else x)     {
	doStatements(x);
    }

    public void performActionOnEmptyStatement(EmptyStatement x)   {
	pushVoid ();
    }

    public void performActionOnEquals(Equals x)     {
	doEquals(x);
    }

    //////////////////////////////////////////////////////////////////


    public void performActionOnExactInstanceof(ExactInstanceof x)     {
	doInstanceof (x);
    }

    public void performActionOnExecutionContext(ExecutionContext x) {
    	popChildren ();
    	pushVoid ();
    }

    public void performActionOnFieldReference(FieldReference x) {
	performActionOnVariableReference ( x );
    }

    public void performActionOnFinally(Finally x)     {
	doStatements(x);
    }

    public void performActionOnFor(For x) {
	ArrayOfKeYJavaType types = popKeYJavaTypes ( 4 );
	checkStatement ( x, types, 0 );
	if ( checkNonVoidType ( types, 1, false ) ) {
	    if ( !getTypeConverter ().isBooleanType
		 ( types.getKeYJavaType ( 1 ) ) )
		raiseTypeError ();
	}
	checkStatement ( x, types, 2 );
	checkStatement ( x, types, 3 );
	pushVoid ();	
    }

    public void performActionOnForUpdates(ForUpdates x)     {
	doStandardStatement (x);
    }

    public void performActionOnGreaterOrEquals(GreaterOrEquals x)     {
	doComparison(x);
    }

    public void performActionOnGreaterThan(GreaterThan x)     {
	doComparison(x);
    } 

    public void performActionOnGuard(Guard x)     {
	ArrayOfKeYJavaType types = popChildren ();
	pushResult ( types.getKeYJavaType ( 0 ) );
    }

    public void performActionOnIf(If x)     {
	ArrayOfKeYJavaType types = popChildrenWithArityCheck (x);
	if ( checkNonVoidType ( types, 0, false ) ) {
	    if ( !getTypeConverter ().isBooleanType
		 ( types.getKeYJavaType ( 0 ) ) )
		raiseTypeError ();
	}
	checkStatement ( x, types, 1 );
	if ( x.getChildCount () == 3 )
	    checkStatement ( x, types, 2 );
	pushVoid ();
    }

    public void performActionOnInstanceof(Instanceof x)     {
	doInstanceof (x);
    }

    public void performActionOnLabeledStatement(LabeledStatement x) {
	doStatements (x);
    }
 
    public void performActionOnLessOrEquals(LessOrEquals x)     {
	doComparison(x);
    }

    public void performActionOnLessThan(LessThan x)     {
	doComparison(x);
    }
 
    public void performActionOnLocationVariable(LocationVariable x) {
        performActionOnProgramVariable(x);
    }

    public void performActionOnLogicalAnd(LogicalAnd x)     {
	doLogicalPromotion ( x );
    }

    public void performActionOnLogicalNot(LogicalNot x)     {
	ArrayOfKeYJavaType types = popAndCheckType ( 1, true );
	if ( types != null ) {
	    if ( !getTypeConverter ().isBooleanType
		 ( types.getKeYJavaType ( 0 ) ) )
		raiseTypeError ();
            doUnaryPromotion(types);
	}
    }
 
    public void performActionOnLogicalOr(LogicalOr x)     {
	doLogicalPromotion ( x );
    } 

    public void performActionOnLoopInit(LoopInit x)     {
	doStandardStatement (x);
    }

    public void performActionOnMethodFrame(MethodFrame x) {
	performActionOnMethodFrame ( x, false );
    } 

    public void performActionOnMethodFrame(MethodFrame x, boolean p_enter) {
	if ( p_enter ) {
	    IProgramVariable pv = x.getProgramVariable ();
	    if ( pv == null )
		returnTypeStack.push ( VOID );
	    else {
		KeYJavaType t = pv.getKeYJavaType ();
		if ( t == null )
		    t = UNKNOWN;
		returnTypeStack.push ( t );
	    }
	} else {
	    returnTypeStack.pop ();
	    pushVoid ();
	}
    }

    public void performActionOnMinus(Minus x)     {
	doNumericPromotion ( x );
    }

    public void performActionOnMinusAssignment(MinusAssignment x)     {
	prepareCompoundAssignment ( x );
	performActionOnMinus ( null );
	doCompoundAssignment ( x );
    }

    public void performActionOnModulo(Modulo x)     {
	doNumericPromotion ( x );
    }

    public void performActionOnModuloAssignment(ModuloAssignment x)     {
	prepareCompoundAssignment ( x );
	performActionOnModulo ( null );
	doCompoundAssignment ( x );
    }
 
    public void performActionOnNegative(Negative x)     {
	doPositiveNegative ( x );
    }

    public void performActionOnNotEquals(NotEquals x)     {
	doEquals(x);
    }

    public void performActionOnPackageReference(PackageReference x) {
	pushVoid();
    }

    public void performActionOnParameterDeclaration(ParameterDeclaration x) {
	pushResult ( doVariableDeclarationHelp(x) );
    }

    public void performActionOnPlus(Plus x)     {
	// strings are not considered yet
	doNumericPromotion ( x );
    }

    public void performActionOnPlusAssignment(PlusAssignment x)     {
	prepareCompoundAssignment ( x );
	performActionOnPlus ( null );
	doCompoundAssignment ( x );
    }
 
    public void performActionOnPositive(Positive x)     {
	doPositiveNegative ( x );
    }
 
    public void performActionOnPostDecrement(PostDecrement x)     {
	doDecrementsIncrements ( x );
    }
 
    public void performActionOnPostIncrement(PostIncrement x)     {
	doDecrementsIncrements ( x );
    }

    public void performActionOnPreDecrement(PreDecrement x)     {
	doDecrementsIncrements ( x );
    }
 
    public void performActionOnPreIncrement(PreIncrement x)     {
	doDecrementsIncrements ( x );
    }
 
    public void performActionOnProgramConstant(ProgramConstant x) {
        performActionOnProgramConstant(x);        
    }

    public void performActionOnProgramElementName(
			    ProgramElementName x)     {
	pushVoid ();
    }

    public void performActionOnProgramSVProxy(ProgramSVProxy x)     {
	if ( x.getKeYJavaType () == null )
	    pushVoid ();
	else
	    pushResult ( x.getKeYJavaType () );
    }
 
    public void performActionOnProgramSVSkolem(ProgramSVSkolem x)     {
	if ( x.getKeYJavaType () == null )
	    pushVoid ();
	else
	    pushResult ( x.getKeYJavaType () );
    }
 
    public void performActionOnProgramVariable(
			    ProgramVariable x)     {
	pushResult ( x.getKeYJavaType () );
    }

    public void performActionOnReturn(Return x)     {
	Debug.assertFalse ( returnTypeStack.empty (),
                            "Cannot determine correct return type" );
	
	KeYJavaType frameType = (KeYJavaType)returnTypeStack.peek ();
	
	if ( x.getChildCount () == 0 ) {
	    if ( frameType != VOID )
		raiseTypeError ();
	} else {
	    if ( frameType == VOID )
		raiseTypeError ();
	    
	    ArrayOfKeYJavaType types = popAndCheckType ( 1, false );
	    if ( checkNonVoidType ( frameType, false ) && types != null ) {
		    // narrowing of constant expressions is not yet performed
		    if ( !getTypeConverter ().isAssignableTo
			 ( types.getKeYJavaType ( 0 ), frameType ) )
			raiseTypeError ();
	    }
	}
	pushVoid ();
    }

    public void performActionOnSchemaVariable(
			    SchemaVariable x)     {
	doSchemaVariable ( x );
    }

    public void performActionOnShiftLeft(ShiftLeft x)     {
	doShiftPromotion ( x );
    }
 
    public void performActionOnShiftLeftAssignment(ShiftLeftAssignment x)     {
	prepareCompoundAssignment ( x );
	performActionOnShiftLeft ( null );
	doCompoundAssignment ( x );
    }

    public void performActionOnShiftRight(ShiftRight x)     {
	doShiftPromotion ( x );
    }
 
    public void performActionOnShiftRightAssignment(ShiftRightAssignment x)     {
	prepareCompoundAssignment ( x );
	performActionOnShiftRight ( null );
	doCompoundAssignment ( x );
    }

    public void performActionOnStatementBlock(StatementBlock x) {
	doStatements (x);
    }
 
    public void performActionOnSwitch(Switch x)     {
	ArrayOfKeYJavaType types = popChildrenWithArityCheck (x);
	int                i     = types.size ();
	
	if ( checkNonVoidType ( types, 0, false ) ) {
	    Type t = types.getKeYJavaType ( 0 ).getJavaType ();
	    if ( !( t == PrimitiveType.JAVA_CHAR  ||
		    t == PrimitiveType.JAVA_BYTE  ||
		    t == PrimitiveType.JAVA_SHORT ||
		    t == PrimitiveType.JAVA_INT ) )
		raiseTypeError ();
	}
	
	while ( i-- != 1 )
	    checkStatement ( x, types, i );

	pushVoid ();
    }
 
    public void performActionOnThen(Then x)     {
	doStatements(x);
    }

    public void performActionOnThrow(Throw x)     {
	// incomplete
	ArrayOfKeYJavaType types = popAndCheckType ( 1, false );
	if ( types != null ) {
	    if ( !( getTypeConverter ().isReferenceType
		    ( types.getKeYJavaType ( 0 ) ) &&
		    getTypeConverter ().isAssignableTo
		    ( types.getKeYJavaType ( 0 ),
		      getJavaInfo ().getTypeByClassName
		      ( "java.lang.Throwable" ) ) ) )
		 raiseTypeError ();
	}
	pushVoid ();
    }

    public void performActionOnTimes(Times x)     {
	doNumericPromotion ( x );
    }

    public void performActionOnTimesAssignment(TimesAssignment x)     {
	prepareCompoundAssignment ( x );
	performActionOnTimes ( null );
	doCompoundAssignment ( x );
    }

    public void performActionOnTry(Try x)     {
	doStatements (x);	
    }

    public void performActionOnTypeCast(TypeCast x)     {
	ArrayOfKeYJavaType types = popKeYJavaTypes ( 2 );
	push ( types.getKeYJavaType ( 1 ) );
	doCast ( types.getKeYJavaType ( 0 ) );
    }

    public void performActionOnTypeReference(TypeReference x) {
	pushResult ( x.getKeYJavaType () );
    }

    public void performActionOnUnsignedShiftRight(UnsignedShiftRight x)     {
	doShiftPromotion ( x );
    }

    public void performActionOnUnsignedShiftRightAssignment 
	(UnsignedShiftRightAssignment x)     {
	prepareCompoundAssignment ( x );
	performActionOnUnsignedShiftRight ( null );
	doCompoundAssignment ( x );
    }

    public void performActionOnVariableReference(VariableReference x) {
    	ArrayOfKeYJavaType types = popKeYJavaTypes ( 1 );
	pushResult ( types.getKeYJavaType ( 0 ) );
    }

    public void performActionOnVariableSpecification(VariableSpecification x)     {
	if ( x.getChildCount () == 2 )
	    doAssignment ();
	else
	    propagateSingleResult ();
    }

    public void performActionOnWhile(While x)     {
	ArrayOfKeYJavaType types = popKeYJavaTypes ( 2 );
	if ( checkNonVoidType ( types, 0, false ) ) {
	    if ( !getTypeConverter ().isBooleanType
		 ( types.getKeYJavaType ( 0 ) ) )
		raiseTypeError ();
	}
	checkStatement ( x, types, 1 );
	pushVoid ();	
    }

    private Object pop () {
    	Debug.assertFalse ( typeStack.empty (), "Stack should not be empty" );
	return typeStack.pop ();
    }

    /**
     * Pop the <code>p_num</code> topmost elements from the type stack
     * using the method <code>popKeYJavaTypes</code>, and check the
     * resulting array using the method
     * <code>checkNonVoidTypeArray</code>
     * @return the array with the types iff
     * <code>checkNonVoidTypeArray</code> returns true,
     * <code>null</code> otherwise
     */
    private ArrayOfKeYJavaType popAndCheckType ( int     p_num,
						 boolean p_push ) {
	final ArrayOfKeYJavaType t = popKeYJavaTypes ( p_num );
	if ( checkNonVoidTypeArray ( t, p_push ) )
	    return t;
	return null;
    }
 
    /**
     * Pop all elements from the stack that lie above the topmost
     * level mark
     * @return all elements from the stack that lie above the topmost
     * level mark as an array, with the first element of the array
     * being the lowest element removed from the stack
     */
    private ArrayOfKeYJavaType popChildren () {
	final ExtList res = new ExtList ();
	Object o;
	while ( true ) {
	    o = pop ();
	    if ( o == LEVEL ) {
		push ( o );
		break;
	    }
	    res.addFirst ( o );
	}
	return new ArrayOfKeYJavaType
	    ( (KeYJavaType[])res.collect ( KeYJavaType.class ) );
    }

    private ArrayOfKeYJavaType popChildrenWithArityCheck
	(NonTerminalProgramElement x) {
        final ArrayOfKeYJavaType types = popChildren ();
        Debug.assertTrue ( types.size() == x.getChildCount(),
                           "AST node arity mismatch: Number of subtrees " +
                           "processed differs from arity of operator\n" +
                           "AST subtree: " + x );	
        return types;
    }

    /**
     * Pop the <code>p_num</code> topmost elements from the type
     * stack, which are assumed to be <code>KeYJavaType</code>s
     * @return The topmost elements of the type stack as an array,
     * with the first element of the array being the lowest element
     * removed from the stack
     */
    private ArrayOfKeYJavaType popKeYJavaTypes ( int p_num ) {
	final KeYJavaType[] res = new KeYJavaType [ p_num ];
	while ( p_num-- != 0 ) {
	    final Object stackEl = pop ();
	    Debug.assertTrue ( stackEl instanceof KeYJavaType,
	                       "Found an element of wrong kind on type stack" );
            res[p_num] = (KeYJavaType)stackEl;
	}
	return new ArrayOfKeYJavaType ( res );
    }

    /**
     * Pop the topmost level mark from the type stack, together with
     * all elements above the mark
     */
    private void popLevelMark () {
	Object o;
	while ( true ) {
	    o = pop ();
	    if ( o == LEVEL )
	    	break;
	    else
	    	logger.warn ( "Superfluous element on type stack: " + o );
	}
    }    

    private void prepareCompoundAssignment ( Assignment x ) {
	// insert a virtual level mark for binary operator
	final ArrayOfKeYJavaType types = popKeYJavaTypes ( 2 );
	push ( types.getKeYJavaType ( 0 ) );
	pushLevelMark ();
	push ( types.getKeYJavaType ( 0 ) );
	push ( types.getKeYJavaType ( 1 ) );
    }

    private void printTypeStack () {
        logger.debug ( "StaticProgramChecker, current type stack:" );
        logger.debug ( "[ " );
        if ( typeStack.size () != 0 ) {
            int i = 0;
            while ( true ) {
                logger.debug ( typeStack.get ( i ) );
                if ( ++i == typeStack.size () ) break;
                logger.debug ( ", " );
            }
        }
        logger.debug ( " ]" );
    }

    /**
     * Pop the topmost element from the stack and push it as result
     */
    private void propagateSingleResult() {
        pushResult ( pop () );
    }

    private void push ( Object p ) {
	typeStack.push ( p );	    
    }

    protected void pushBoolean () {
	pushResult ( getTypeConverter ().getKeYJavaType
		     ( PrimitiveType.JAVA_BOOLEAN ) );
    }

    private void pushLevelMark () {
	push ( LEVEL );
    }

    /**
     * Push the type of a subtree of the AST on the type stack. The
     * type is inserted immediately below the topmost level mark,
     * i.e. after the next call of <code>popLevelMark</code> the
     * element <code>x</code> is the topmost element of the type stack
     */
    private void pushResult ( Object x ) {
	final Object o = pop ();

	if ( o == LEVEL )
	    push ( x );
	else
	    pushResult ( x );

	push ( o );
    }

    protected void pushUnknown () {
	pushResult ( UNKNOWN );	    
    }

    protected void pushVoid () {
	pushResult ( VOID );	    
    }

    /**
     * @throws StaticTypeException to indicate that a type error has
     * been detected
     */
    private void raiseTypeError () {
	throw new StaticTypeException ( "Static type error" );
    }

    /** starts the walker*/
    public void start() {	
	walk(root());	
    }

    private boolean validSpecificationType ( KeYJavaType p_specType,
					     KeYJavaType p_declType ) {
	assert p_specType != null : "p_specType is null";
	assert p_declType != null : "p_declType is null";

	return
	    p_specType == p_declType ||
	    p_specType.getJavaType () instanceof ArrayType &&
	    validSpecificationType
	    ( ((ArrayType)p_specType.getJavaType ()).getBaseType ()
	      .getKeYJavaType (),
	      p_declType );
    }

    /** walks through the AST. While keeping track of the current node
     * @param node the JavaProgramElement the walker is at 
     */
    protected void walk(ProgramElement node) {
	// for each subtree a level mark is pushed on the type stack ...
	pushLevelMark ();

	if (node instanceof MethodFrame)
	    performActionOnMethodFrame ( (MethodFrame)node, true );
	
	if (node instanceof NonTerminalProgramElement) {
	    NonTerminalProgramElement nonTerminalNode = 
		(NonTerminalProgramElement) node;
	    for (int i = 0; i<nonTerminalNode.getChildCount(); i++) {
		walk(nonTerminalNode.getChildAt(i));
	    }	    
	}
	// otherwise the node is left, so perform the action
	doAction(node);
	
	// ... and is removed which leaving the subtree
	popLevelMark ();
    }

}
