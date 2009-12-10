// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.logic.sort;

import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.expression.literal.StringLiteral;
import de.uka.ilkd.key.java.expression.operator.Instanceof;
import de.uka.ilkd.key.java.expression.operator.Negative;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.expression.operator.NewArray;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.java.recoderext.InstanceAllocationMethodBuilder;
import de.uka.ilkd.key.java.recoderext.JVMIsTransientMethodBuilder;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.soundness.ProgramSVProxy;
import de.uka.ilkd.key.util.ExtList;

public abstract class ProgramSVSort extends PrimitiveSort {

    // Keeps the mapping of ProgramSVSort names to
    // ProgramSVSort instances (helpful in parsing
    // schema variable declarations)
    private static HashMap<Name, ProgramSVSort> name2sort = 
        new HashMap<Name, ProgramSVSort>(60);

    //----------- Types of Expression Program SVs ----------------------------
   
    
    public static final ProgramSVSort LEFTHANDSIDE
	= new LeftHandSideSort();

    public static final ProgramSVSort VARIABLE
	= new ProgramVariableSort();

    public static final ProgramSVSort STATICVARIABLE
	= new StaticVariableSort();


    public static final ProgramSVSort SIMPLEEXPRESSION 
	= new SimpleExpressionSort();

    public static final ProgramSVSort NONSIMPLEEXPRESSION 
	= new NonSimpleExpressionSort();
    
    public static final ProgramSVSort EXPRESSION
	= new ExpressionSort();


    //----------- Initialisation and Creation expressions -------------------
    
    public static final ProgramSVSort NEW = new NewSVSort();

    public static final ProgramSVSort NEWARRAY = new NewArraySVSort();

    public static final ProgramSVSort ARRAYINITIALIZER
	= new ArrayInitializerSVSort();

    public static final ProgramSVSort SPECIALCONSTRUCTORREFERENCE
	= new SpecialConstructorReferenceSort();

    
    //----------- Expressions with restrictions on kind of type -------------

//    public static final ModelMethodSort MODELMETHOD
//	= new ModelMethodSort();

    public static final NonSimpleMethodReferenceSort NONSIMPLEMETHODREFERENCE
	= new NonSimpleMethodReferenceSort();


    //----------- Types of Statement Program SVs -----------------------------    
    
    public static final ProgramSVSort STATEMENT
	= new StatementSort();

    public static final ProgramSVSort CATCH
	= new CatchSort();

    public static final ProgramSVSort METHODBODY
	= new MethodBodySort();

    public static final ProgramSVSort PUREMETHODBODY
        = new PureMethodBodySort();

    public static final ProgramSVSort NONMODELMETHODBODY
	= new NonModelMethodBodySort();


    //-----------Types--------------------------------------------------------
    
    public static final ProgramSVSort TYPE
	= new TypeReferenceSort();

    public static final ProgramSVSort TYPENOTPRIMITIVE
	= new TypeReferenceNotPrimitiveSort();


    //-----------Others-------------------------------------------------------

    public static final ProgramSVSort METHODNAME
	= new MethodNameSort();
    
    public static final ProgramSVSort LABEL
	= new LabelSort();
    
    
    //-----------Specials for primitive types---------------------------------
    
    public static final ProgramSVSort JAVABOOLEANEXPRESSION 
	= new ExpressionSpecialPrimitiveTypeSort
	("JavaBooleanExpression", new
	 PrimitiveType[]{PrimitiveType.JAVA_BOOLEAN});

    public static final ProgramSVSort SIMPLEJAVABYTEEXPRESSION 
	= new SimpleExpressionSpecialPrimitiveTypeSort
	("JavaByteExpression", new
	 PrimitiveType[]{PrimitiveType.JAVA_BYTE});

    public static final ProgramSVSort SIMPLEJAVACHAREXPRESSION 
	= new SimpleExpressionSpecialPrimitiveTypeSort
	("JavaCharExpression", new
	 PrimitiveType[]{PrimitiveType.JAVA_CHAR});

    public static final ProgramSVSort SIMPLEJAVASHORTEXPRESSION 
	= new SimpleExpressionSpecialPrimitiveTypeSort
	("JavaShortExpression", new
	 PrimitiveType[]{PrimitiveType.JAVA_SHORT});

    public static final ProgramSVSort SIMPLEJAVAINTEXPRESSION 
	= new SimpleExpressionSpecialPrimitiveTypeSort
	("JavaIntExpression", new
	 PrimitiveType[]{PrimitiveType.JAVA_INT});

    public static final ProgramSVSort SIMPLEJAVALONGEXPRESSION 
	= new SimpleExpressionSpecialPrimitiveTypeSort
	("JavaLongExpression", new
	 PrimitiveType[]{PrimitiveType.JAVA_LONG});

    public static final ProgramSVSort SIMPLEJAVABYTESHORTEXPRESSION
	= new SimpleExpressionSpecialPrimitiveTypeSort
	("JavaByteShortExpression", new
	 PrimitiveType[]{PrimitiveType.JAVA_BYTE,
			 PrimitiveType.JAVA_SHORT});

    public static final ProgramSVSort SIMPLEJAVABYTESHORTINTEXPRESSION
	= new SimpleExpressionSpecialPrimitiveTypeSort
	("JavaByteShortIntExpression", new
	 PrimitiveType[]{PrimitiveType.JAVA_BYTE,
			 PrimitiveType.JAVA_SHORT,
			 PrimitiveType.JAVA_INT});


    public static final ProgramSVSort SIMPLEANYJAVATYPEEXPRESSION 
	= new SimpleExpressionSpecialPrimitiveTypeSort
	("AnyJavaTypeExpression", new
	 PrimitiveType[]{PrimitiveType.JAVA_BYTE,
			 PrimitiveType.JAVA_SHORT,
			 PrimitiveType.JAVA_INT,
			 PrimitiveType.JAVA_LONG});
    
    public static final ProgramSVSort SIMPLEANYNUMBERTYPEEXPRESSION 
	= new SimpleExpressionSpecialPrimitiveTypeSort
	("AnyNumberTypeExpression", new
	 PrimitiveType[]{PrimitiveType.JAVA_BYTE,
			 PrimitiveType.JAVA_SHORT,
			 PrimitiveType.JAVA_INT,
			 PrimitiveType.JAVA_LONG,
			 PrimitiveType.JAVA_CHAR});

    public static final ProgramSVSort SIMPLEJAVASHORTINTLONGEXPRESSION
	= new SimpleExpressionSpecialPrimitiveTypeSort
	("JavaShortIntLongExpression", new
	 PrimitiveType[]{PrimitiveType.JAVA_SHORT,
			 PrimitiveType.JAVA_INT,
	                 PrimitiveType.JAVA_LONG});

    public static final ProgramSVSort SIMPLEJAVAINTLONGEXPRESSION
	= new SimpleExpressionSpecialPrimitiveTypeSort
	("JavaIntLongExpression", new
	 PrimitiveType[]{PrimitiveType.JAVA_INT,
	                 PrimitiveType.JAVA_LONG});

    public static final ProgramSVSort SIMPLEJAVACHARBYTESHORTINTEXPRESSION
	= new SimpleExpressionSpecialPrimitiveTypeSort
	("JavaCharByteShortIntExpression", new
	 PrimitiveType[]{PrimitiveType.JAVA_CHAR,
			 PrimitiveType.JAVA_BYTE,
			 PrimitiveType.JAVA_SHORT,
			 PrimitiveType.JAVA_INT});

    public static final ProgramSVSort SIMPLESTRINGEXPRESSION
	= new SimpleExpressionStringSort
	("SimpleStringExpression");



    //--------------- Specials that can be get rid of perhaps--------------

    public static final ProgramSVSort LOOPINIT = new LoopInitSort();

    public static final ProgramSVSort GUARD = new GuardSort();

    public static final ProgramSVSort FORUPDATES = new ForUpdatesSort();
    
    public static final ProgramSVSort FORLOOP = new ForLoopSort();

    public static final ProgramSVSort MULTIPLEVARDECL
	= new MultipleVariableDeclarationSort();

    public static final ProgramSVSort ARRAYPOSTDECL
	= new ArrayPostDeclarationSort();
    
    public static final ProgramSVSort SWITCH
	= new SwitchSVSort(); 

    public static final ProgramSVSort IMPLICITVARIABLE
	= new ImplicitProgramVariableSort();

    public static final ProgramSVSort EXPLICITVARIABLE
	= new ExplicitProgramVariableSort();

    public static final ProgramSVSort CONSTANTVARIABLE
	= new ConstantProgramVariableSort();

    // implict field match
    public static final ProgramSVSort IMPLICITREFERENCE
	= new ImplicitFieldReferenceSort();

    public static final ProgramSVSort VARIABLEINIT
	= new ProgramSVSort(new Name("VariableInitializer")) {
        public boolean canStandFor(ProgramElement pe, 
                Services services) {
            return true;
        }
    };

    public static final ProgramSVSort LITERAL = new LiteralSort();

    //--------------- Specials that match on certain names-----------------
    
    public static final ProgramSVSort IMPLICITCLINIT
	= new ImplicitFieldSort(new Name("ImplicitClassInitialized"),
	                        ImplicitFieldAdder.
				IMPLICIT_CLASS_INITIALIZED, true);

    public static final ProgramSVSort IMPLICITINITINPROGRESS
	= new ImplicitFieldSort(new Name("ImplicitClassInitializationInProgress"),
	                        ImplicitFieldAdder.
				IMPLICIT_CLASS_INIT_IN_PROGRESS, true);

    public static final ProgramSVSort IMPLICITERRONEOUS
	= new ImplicitFieldSort(new Name("ImplicitClassErroneous"),
	                        ImplicitFieldAdder.
				IMPLICIT_CLASS_ERRONEOUS, true);

    public static final ProgramSVSort IMPLICITPREPARED
	= new ImplicitFieldSort(new Name("ImplicitClassPrepared"),
	                        ImplicitFieldAdder.
				IMPLICIT_CLASS_PREPARED, true);

    public static final ProgramSVSort IMPLICITNEXTTOCREATE
	= new ImplicitFieldSort(new Name("ImplicitNextToCreate"),
	                        ImplicitFieldAdder.IMPLICIT_NEXT_TO_CREATE, true);
    
    public static final ProgramSVSort IMPLICITCREATED
        = new ImplicitFieldSort(new Name("ImplicitCreated"),
                                ImplicitFieldAdder.IMPLICIT_CREATED, true);
    
    public static final ProgramSVSort IMPLICITENLOSINGTHIS
    = new ImplicitFieldSort(new Name("ImplicitEnclosingThis"),
                            ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS, true);

    public static final ProgramSVSort IMPLICITTRAINITIALIZED
	= new ImplicitFieldSort(new Name("ImplicitTraInitialized"),
	                        ImplicitFieldAdder.IMPLICT_ARRAY_TRA_INITIALIZED, 
				true);

    public static final ProgramSVSort IMPLICITTRANSACTIONCOUNTER
	= new ImplicitFieldSort(new Name("ImplicitTransactionCounter"),
	                        "de.uka.ilkd.key.javacard.KeYJCSystem" + "::" + 
				JVMIsTransientMethodBuilder.IMPLICIT_TRANSACTION_COUNTER, 
				false);

    public static final ProgramSVSort ARRAYLENGTH
	= new ArrayLengthSort();

    public static final ProgramSVSort JCMAKETRANSIENTARRAY
	= new MethodNameReferenceSort(new Name("makeTransientArray"),
	                              new String[] {"jvmMakeTransientBooleanArray",
				        "jvmMakeTransientByteArray",
				        "jvmMakeTransientShortArray",
				        "jvmMakeTransientObjectArray"}, 
				      "de.uka.ilkd.key.javacard.KeYJCSystem",
				      ImmutableSLList.<Name>nil().append
				      (new Name("byte")).append(new Name("short")));

    public static final ProgramSVSort JCARRAYCOPY
	= new SpecificMethodNameSort(new ProgramElementName("jvmArrayCopy"));
    public static final ProgramSVSort JCARRAYCOPYNONATOMIC
	= new SpecificMethodNameSort(new ProgramElementName("jvmArrayCopyNonAtomic"));
    public static final ProgramSVSort JCARRAYFILLNONATOMIC
	= new SpecificMethodNameSort(new ProgramElementName("jvmArrayFillNonAtomic"));
    public static final ProgramSVSort JCARRAYCOMPARE
	= new SpecificMethodNameSort(new ProgramElementName("jvmArrayCompare"));

    public static final ProgramSVSort JCMAKESHORT
	= new SpecificMethodNameSort(new ProgramElementName("jvmMakeShort"));
    public static final ProgramSVSort JCSETSHORT
	= new SpecificMethodNameSort(new ProgramElementName("jvmSetShort"));

    public static final ProgramSVSort JCISTRANSIENT
	= new SpecificMethodNameSort(new ProgramElementName("jvmIsTransient"));
    public static final ProgramSVSort JCBEGINTRANSACTION
	= new SpecificMethodNameSort(new ProgramElementName("jvmBeginTransaction"));
    public static final ProgramSVSort JCCOMMITTRANSACTION
	= new SpecificMethodNameSort(new ProgramElementName("jvmCommitTransaction"));
    public static final ProgramSVSort JCABORTTRANSACTION
	= new SpecificMethodNameSort(new ProgramElementName("jvmAbortTransaction"));
    public static final ProgramSVSort JCSUSPENDTRANSACTION
	= new SpecificMethodNameSort(new ProgramElementName("jvmSuspendTransaction"));
    public static final ProgramSVSort JCRESUMETRANSACTION
	= new SpecificMethodNameSort(new ProgramElementName("jvmResumeTransaction"));
    
    public static final ProgramSVSort ALLOCATE
        = new SpecificMethodNameSort(new ProgramElementName
                (InstanceAllocationMethodBuilder.IMPLICIT_INSTANCE_ALLOCATE));
    
    public static final ProgramSVSort SEP //TODO
        = new SpecificMethodNameSort(new ProgramElementName("sep"));

    public static final ProgramSVSort  DEBUGGERTYPEREF
    = new  DebuggerTypeReferenceSort();
    
    //---------------REFERENCE SORTS ------------------------
    public static final ProgramSVSort EXECUTIONCONTEXT = new ExecutionContextSort();

    

    //---------------UNNECESSARY ONES------------------------



    //--------------------------------------------------------------------------
    
    public ProgramSVSort(Name name) {
	super(name);
	name2sort.put(name, this);
    }

    public boolean canStandFor(Term t) {
 	return true;
    }

    public boolean canStandFor(ProgramElement check,
			       ExecutionContext ec,
			       Services services) {
	return canStandFor(check, services);
    }


    protected abstract boolean canStandFor(ProgramElement check,
            Services services);



    //-------------Now the inner classes representing the-----------------------
    //-------------different kinds of program SVs-------------------------------

    /**
     * This sort represents a type of program schema variables that match
     * only on <ul> <li>program variables or <li>static field references with
     * a prefix that consists of <ul> <li>a program variable followed by a
     * sequence of attribute accesses or <li>of a type reference followed by
     * a sequence of attribute accesses</ul></ul>
     */
    private static class LeftHandSideSort extends ProgramSVSort {

	public LeftHandSideSort() {
	    super(new Name("LeftHandSide"));
	}

	public LeftHandSideSort(Name name) {
	    super(name);
	}

	public boolean canStandFor(Term t) {
	    if (t.op() instanceof ProgramVariable) {
		return true;
	    }
	    return false;
	}

	protected boolean canStandFor(ProgramElement pe,
				      Services services) {

	    if (pe instanceof ProgramVariable       ||
		pe instanceof VariableSpecification) {
		return true;
	    }	   

	    if (pe instanceof FieldReference){
		FieldReference fr = (FieldReference)pe;
		// we allow only static field references with a
		// sequence of PVs or TypeRef 
		ReferencePrefix rp = fr.getReferencePrefix();
		if ((fr.getProgramVariable()).isStatic()) {
		    return (rp == null ||
			    rp instanceof ThisReference ||
			    rp instanceof TypeReference ||
			    canStandFor(rp, services)); 
		} else if (rp == null || //AR was in SimpleEx
			   rp instanceof ThisReference) {
		    return canStandFor
			(fr.getProgramVariable(), services);	  
		}
	    }

	    if (pe instanceof PassiveExpression) {
		return canStandFor
		    (((NonTerminalProgramElement)pe).
		     getChildAt(0), services);
	    }

	    return false;
	}
    }


    /**
     * This sort represents a type of program schema variables that match
     * only on <ul> <li>program variables or <li>static field references with
     * a prefix that consists of <ul> <li>a program variable followed by a
     * sequence of attribute accesses or <li>of a type reference followed by
     * a sequence of attribute accesses</ul></ul>. In opposite to its
     * super class it matches only if the field reference does not
     * trigger static initialisation (i.e. if it is no active reference)
     */
    private static class ProgramVariableSort 
	extends LeftHandSideSort {

	public ProgramVariableSort() {
	    super(new Name("Variable"));
	}

	ProgramVariableSort(Name name) {
	    super(name);
	}

	public boolean canStandFor(Term t) {
	    return t.op() instanceof ProgramVariable;
	}

	protected boolean canStandFor(ProgramElement pe,
				      Services services) {

	    ProgramVariable accessedField = null;
	    if (pe instanceof FieldReference){
		accessedField = ((FieldReference)pe).getProgramVariable();
	    } else if (pe instanceof ProgramVariable) {
		accessedField = (ProgramVariable) pe;
	    } else if (pe instanceof PassiveExpression) {
		return super.canStandFor
		    (((PassiveExpression)pe).getChildAt(0), 
		     services);
	    }
	    
	    
	    if (accessedField != null &&
		accessedField.isStatic() &&
		!(accessedField instanceof ProgramConstant)) {
		return false; 
	    }

	    return super.canStandFor(pe, services); 
	}
	
    }


    private static class StaticVariableSort 
	extends LeftHandSideSort {

	public StaticVariableSort() {
	    super (new Name("StaticVariable"));
	}

	public boolean canStandFor(Term t) {	   
	    return t.op() instanceof ProgramVariable &&
               ((ProgramVariable)t.op()).isStatic();
	}

	protected boolean canStandFor(ProgramElement pe,
				      Services services) {

	    ProgramVariable accessedField = null;
	    if (pe instanceof FieldReference){
		accessedField = ((FieldReference)pe).getProgramVariable();
	    } else if (pe instanceof ProgramVariable) {
		accessedField = (ProgramVariable) pe;
	    } 
	    if (accessedField != null) {
		return 
		    accessedField.isStatic() &&
		    !(accessedField instanceof ProgramConstant) &&
		    super.canStandFor(pe, services);
	    }
	    return false;
	}

    }
    


    /**
     * This sort represents a type of program schema variables that match
     * only on <ul> <li>program variables or <li>static field references with
     * a prefix that consists of <ul> <li>a program variable followed by a
     * sequence of attribute accesses or <li>of a type reference followed by
     * a sequence of attribute accesses</ul> <li> (negated) literal
     * expressions or <li> instanceof expressions v instanceof T with an
     * expression v that matches on a program variable SV </ul>
     */
    private static class SimpleExpressionSort extends ProgramSVSort{

	public SimpleExpressionSort() {
	    super(new Name("SimpleExpression"));
	}

	protected SimpleExpressionSort(Name n) {
	    super(n);
	}

	public boolean canStandFor(Term t) {
	    return true;
	}
	
	protected boolean canStandFor(ProgramElement pe,
				      Services services) {
	    if (pe instanceof Negative) {
 		return ((Negative)pe).getChildAt(0) instanceof Literal;
 	    }	   

	    if (pe instanceof Literal) {
				return true;
	    }
	    if (pe instanceof Instanceof) {
		ProgramElement v = ((Instanceof) pe).getChildAt(0);
		return (v instanceof ThisReference) || VARIABLE.canStandFor(v, services); 
	    }

	    if (pe instanceof ThisReference) {
		return true;
	    }

	    return VARIABLE.canStandFor(pe, services);    
	}
    }



    /**
     * This sort represents a type of program schema variables that match
     * only on all expressions which are not matched by simple expression
     * SVs. 
     */
    private static class NonSimpleExpressionSort extends ProgramSVSort{

	public NonSimpleExpressionSort() {
	    super(new Name("NonSimpleExpression"));
	}

	protected NonSimpleExpressionSort(Name n) {
	    super(n);
	}

	protected boolean canStandFor(ProgramElement check, 
				      Services services) {
	    if (!( check instanceof Expression)
		|| check instanceof SuperReference) {
		return false;
	    }
	    if (check instanceof FieldReference && 
		((FieldReference)check).referencesOwnInstanceField()) {
		return false;
	    }
	    return !SIMPLEEXPRESSION.canStandFor(check,services);
	}
    }

    /**
     * This sort represents a type of program schema variables that match on
     * all expressions only.
     */
    private static class ExpressionSort extends ProgramSVSort{

	public ExpressionSort() {
	    super(new Name("Expression"));
	}

	protected ExpressionSort(Name n) {
	    super(n);
	}

	protected boolean canStandFor(ProgramElement pe, Services services) {
	    return (pe instanceof Expression);
	}

    }


    /**
     * This sort represents a type of program schema variables that match
     * only on literals
     */
    private static class LiteralSort extends ProgramSVSort {

	public LiteralSort() {
	    super(new Name("Literal"));
	}

	protected LiteralSort(Name n) {
	    super(n);
	}

	// not designed to match on terms
	public boolean canStandFor(Term t) {
	    return false;
	}
	
	protected boolean canStandFor(ProgramElement pe,
				      Services services) {
	    return (pe instanceof Literal);
	}
    }


    //----------- Initialisation and Creation expressions -------------------

    
    /**
     * This sort represents a type of program schema variables that match
     * only on Class Instance Creation Expressions, new C()
     */
    private static class NewSVSort extends ProgramSVSort{

	public NewSVSort() {
	    super(new Name("InstanceCreation"));
	}

	protected boolean canStandFor(ProgramElement check, 
				      Services services) {
	    return (check instanceof New);
        }
    }

    /**
     * This sort represents a type of program schema variables that match
     * only on Array Creation Expressions, new A[]
     */
    private static class NewArraySVSort extends ProgramSVSort{
	public NewArraySVSort() {
	    super(new Name("ArrayCreation"));
	}

	protected boolean canStandFor(ProgramElement check, 
				      Services services) {
	    return (check instanceof NewArray);
        }
    }

    /**
     * This sort represents a type of program schema variables that
     * match only on Array Initializers.
     */
    private static class ArrayInitializerSVSort extends ProgramSVSort{

	public ArrayInitializerSVSort() {
	    super(new Name("ArrayInitializer"));
	}

	protected boolean canStandFor(ProgramElement check, 
				      Services services) {
	    return (check instanceof ArrayInitializer);
        }
    }

    
    /**
     * This sort represents a type of program schema variables that
     * match only on Special Constructor References.
     */
    private static class SpecialConstructorReferenceSort 
	extends ProgramSVSort{

	public SpecialConstructorReferenceSort() {
	    super(new Name("SpecialConstructorReference"));
	}

	protected boolean canStandFor(ProgramElement pe,
				      Services services) {
	    return (pe instanceof SpecialConstructorReference);
	}

	public boolean canStandFor(Term t) {
	    return (t.op() instanceof ProgramMethod && 
		    !((ProgramMethod) t.op()).isModel());
	}
    }

    
    
    //----------- Types of Statement Program SVs -----------------------------   

    /**
     * This sort represents a type of program schema variables that
     * match only on statements
     */    
    private static class StatementSort extends ProgramSVSort{

	public StatementSort() {
	    super(new Name("Statement"));
	}

	protected boolean canStandFor(ProgramElement pe, Services services) {
	    return (pe instanceof Statement);
	}

    }

    /**
     * This sort represents a type of program schema variables that
     * match only on catch branches of try-catch-finally blocks
     */    
    private static class CatchSort extends ProgramSVSort{

	public CatchSort() {
	    super(new Name("Catch"));
	}
	
	protected boolean canStandFor(ProgramElement pe, Services services) {
	    return (pe instanceof Catch);
	}
    }

    /**
     * This sort represents a type of program schema variables that
     * match only on method body statements
     */    
    private static class MethodBodySort extends ProgramSVSort{

	public MethodBodySort() {
	    super(new Name("MethodBody"));
	}

	protected boolean canStandFor(ProgramElement check, Services services) {
	    return (check instanceof MethodBodyStatement);
	}
    }

    /**
     * This sort represents a type of program schema variables that
     * match only on pure method body statements
     * 
     * TODO: Maybe further checks in canStandFor? (i.e. is the resultvariable available?)
     */    
    private static class PureMethodBodySort extends ProgramSVSort{

        public PureMethodBodySort() {
            super(new Name("PureMethodBody"));
        }

        protected boolean canStandFor(ProgramElement check, Services services) {
            return ( (check instanceof MethodBodyStatement)
            && ((MethodBodyStatement)check).isPure( services )
            && ((MethodBodyStatement)check).getResultVariable() != null ) ;
        }
    }

    /**
     * This sort represents a type of program schema variables that
     * match only on method body statements for nonmodel methods for which
     * an implementation is present.
     */    
    private static class NonModelMethodBodySort extends ProgramSVSort{

	public NonModelMethodBodySort() {
	    super(new Name("NonModelMethodBody"));
	}

	protected boolean canStandFor(ProgramElement pe, Services services) {
	    if(!(pe instanceof MethodBodyStatement)){
		return false;
	    }
	    
            final ProgramMethod pm = 
		((MethodBodyStatement) pe).getProgramMethod(services);
            if(pm == null) {
                return false;
            }
	    final MethodDeclaration methodDeclaration = pm.getMethodDeclaration();
            
            return !(//pm.isModel() ||
                     methodDeclaration.getBody() == null) ||
                     (methodDeclaration instanceof ConstructorDeclaration);
	}
	
    }

    /**
     * This sort represents a type of program schema variables that
     * match on a method call with SIMPLE PREFIX and AT LEAST a
     * NONSIMPLE expression in the ARGUMENTS.
     */    
    private static class NonSimpleMethodReferenceSort extends ProgramSVSort{

	public NonSimpleMethodReferenceSort() {
	    super(new Name("NonSimpleMethodReference"));
	}

	protected boolean canStandFor(ProgramElement pe,
				      Services services) {
	    if(pe instanceof MethodReference) {
		MethodReference mr = (MethodReference)pe;
		Name localname = mr.getProgramElementName();
		if (excludedMethodName(localname)) return false;
		if (mr.getReferencePrefix() instanceof SuperReference ||
		    mr.getReferencePrefix() instanceof TypeReference) {
		    return false;
		}
		if (mr.getReferencePrefix()!=null && 
		    NONSIMPLEEXPRESSION.canStandFor
		    (mr.getReferencePrefix(), services)) {
		    return false;
		}
 		if (mr.getArguments()==null) {
 		    return false;
 		}
		for (int i=0; i<mr.getArguments().size(); i++) {
		    if (NONSIMPLEEXPRESSION.canStandFor(mr.getArgumentAt(i),
							services)) {
			return true;
		    } 
		}		
	    }
	    return false;
	}

	public boolean canStandFor(Term t) {
	    return (t.op() instanceof ProgramMethod);
	}
    }



    //-----------Types--------------------------------------------------------

    /**
     * This sort represents a type of program schema variables that
     * match only on type references.
     */    
    private static class TypeReferenceSort extends ProgramSVSort {

	public TypeReferenceSort() {
	    super(new Name("Type"));
	}

	protected boolean canStandFor(ProgramElement check, Services services) {
	    return (check instanceof TypeReference);
	}
    }
    
    
    /**
     * This sort represents a type of program schema variables that
     * match only on type references.
     */    
    private static class DebuggerTypeReferenceSort extends ProgramSVSort {

        public DebuggerTypeReferenceSort() {
            super(new Name("DebuggerType"));
        }

        protected boolean canStandFor(ProgramElement check, Services services) {
            if (check instanceof TypeReference){
               TypeReference tr = (TypeReference)check;
               System.out.println(tr.getReferencePrefix());
                
            } 
            return false;
        }
    }


    /**
     * This sort represents a type of program schema variables that
     * match anything except byte, char, short, int, and long.
     */    
    private static class TypeReferenceNotPrimitiveSort extends ProgramSVSort {

	public TypeReferenceNotPrimitiveSort() {
	    super(new Name("NonPrimitiveType"));
	}

	protected boolean canStandFor(ProgramElement check, Services services) {	    
	    if (!(check instanceof TypeReference)) return false;
	    return !(((TypeReference)(check)).getKeYJavaType().getJavaType() 
		     instanceof PrimitiveType);
	
	}
    }

    
    //-----------Names--------------------------------------------------------    
    
    /**
     * This sort represents a type of program schema variables that match
     * on names of method references, i.e. the "m" of o.m(p1,pn).
     */
    private static class MethodNameSort extends ProgramSVSort{

        
        
	public MethodNameSort() {
	    super(new Name("MethodName"));
	}

        protected MethodNameSort(Name n) {
            super(n);
        }
        
	protected boolean canStandFor(ProgramElement pe,
				      Services services) {	    
	    if(pe instanceof MethodName) {
		Name localname = (ProgramElementName) pe;
		return (!excludedMethodName(localname));
	    }
	    return false;
	}

    }

    /**
     * allows to match on a specific method name 
     */
    private static class SpecificMethodNameSort extends MethodNameSort{

        private ProgramElementName methodName; 
        
        public SpecificMethodNameSort(Name sortName, 
				      ProgramElementName methodName) {
            super(sortName);
            this.methodName = methodName;
        }

        public SpecificMethodNameSort(ProgramElementName name) {
            super(name);
            this.methodName = name;
        }

        protected boolean canStandFor(ProgramElement pe,
                                      Services services) {          
            if(pe instanceof MethodName) {                
                return pe.equals(methodName);
            }
            return false;
        }

    }

    
    
    /**
     * This sort represents a type of program schema variables that match
     * on labels.
     */
    private static class LabelSort extends ProgramSVSort{

	public LabelSort() {
	    super(new Name("Label"));
	}

	protected boolean canStandFor(ProgramElement pe,
				      Services services) {	    
	    return (pe instanceof Label);
	}

    }



    /**
     * This sort represents a type of program schema variables that match
     * on string literals and string variables.
     */
    public static class SimpleExpressionStringSort 
	extends SimpleExpressionSort{

	public SimpleExpressionStringSort(String name) {
	    super(new Name(name));
	}

	public boolean canStandFor(ProgramElement check, 
				   ExecutionContext ec,
				   Services services) {
	    if (!super.canStandFor(check, ec, services)) {
		return false;
	    }
	    if (check instanceof StringLiteral) return true;
	    if (check instanceof ProgramVariable) {
		Namespace ns = services.getNamespaces().sorts();
		Sort stringSort = (Sort)ns.lookup(new Name("java.lang.String"));
		return ((ProgramVariable)check).getKeYJavaType().getSort().equals(stringSort);
	    }
	    return false;
	}
    }

    //-----------Specials for primitive types---------------------------------


    /**
     * This sort represents a type of program schema variables that match
     * on simple expressions which have a special primitive type.
     */
    private static class SimpleExpressionSpecialPrimitiveTypeSort 
	extends SimpleExpressionSort{

	private final PrimitiveType[] allowed_types;

	public SimpleExpressionSpecialPrimitiveTypeSort
	    (String name, PrimitiveType[] allowed_types) {
	    
	    super(new Name(name));
	    this.allowed_types = allowed_types;           
	}

	public boolean canStandFor(ProgramElement check, 
				   ExecutionContext ec,
				   Services services) {
	    if (!super.canStandFor(check, ec, services)) {
		return false;
	    }
	    final KeYJavaType kjt = getKeYJavaType(check, ec, services);
            if (kjt != null) {
                final Type type = kjt.getJavaType();
                for (PrimitiveType allowed_type : allowed_types) {
                    if (type == allowed_type)
                        return true;
                }
            }
            return false;
	}
    }

    /**
     * This sort represents a type of program schema variables that match
     * on simple expressions which have a special primitive type.
     */
    private static class ExpressionSpecialPrimitiveTypeSort 
	extends ExpressionSort{

	private PrimitiveType[] allowed_types;

	public ExpressionSpecialPrimitiveTypeSort
	    (String name, PrimitiveType[] allowed_types) {
	    
	    super(new Name(name));
	    this.allowed_types = allowed_types;
	}

	public boolean canStandFor(ProgramElement check, 
				   ExecutionContext ec,
				   Services services) {
	    if (!super.canStandFor(check, ec, services)) {
		return false;
	    }
	    
            final KeYJavaType kjt = getKeYJavaType(check, ec, services);
	    if (kjt != null) {
	        final Type type = kjt.getJavaType();

            for (PrimitiveType allowed_type : allowed_types) {
                if (type == allowed_type)
                    return true;
            }
            }
	    return false;
	}
    }

    //-----------Specials (unnecessary?)--------------------------------------
    

    private static class LoopInitSort extends ProgramSVSort{

	public LoopInitSort() {
	    super(new Name("LoopInit"));
	}

	protected boolean canStandFor(ProgramElement check, Services services) {
	    return (check instanceof LoopInit);
	}
    }

    private static class GuardSort extends ProgramSVSort{
	public GuardSort() {
	    super(new Name("Guard"));
	}
	
	protected boolean canStandFor(ProgramElement check, Services services) {
	    return (check instanceof Guard);
	}
    }

    private static class ForUpdatesSort extends ProgramSVSort{
	public ForUpdatesSort() {
	    super(new Name("ForUpdates"));
	}
	protected boolean canStandFor(ProgramElement check, Services services) {
	    return (check instanceof ForUpdates);

	}
    }
    
    private static class ForLoopSort extends ProgramSVSort {
        public ForLoopSort() {
            super(new Name("ForLoop"));
        }
        protected boolean canStandFor(ProgramElement check, Services services) {
            return (check instanceof For);
        }
    }
        
    private static class SwitchSVSort extends ProgramSVSort{
	public SwitchSVSort(){
	    super(new Name("Switch"));
	}

	protected boolean canStandFor(ProgramElement pe, 
				      Services services) {
	    return (pe instanceof Switch);
	}
    }

    private static class MultipleVariableDeclarationSort extends ProgramSVSort{

	public MultipleVariableDeclarationSort() {
	    super(new Name("MultipleVariableDeclaration"));
	}

	protected boolean canStandFor(ProgramElement pe,
				      Services services) {
	    if (pe instanceof VariableDeclaration &&
		((VariableDeclaration)pe).getVariables().size() > 1) 
		return true;	    
	    return false;
	}	

    }

    private static class ArrayPostDeclarationSort extends ProgramSVSort{

	public ArrayPostDeclarationSort() {
	    super(new Name("ArrayPostDeclaration"));
	}

	protected boolean canStandFor(ProgramElement pe,
				      Services services) {
	    if (pe instanceof VariableDeclaration &&
		((VariableDeclaration)pe).getVariables().size() == 1 &&
		((VariableDeclaration)pe).getVariables().
		get(0).getDimensions() > 0) {
		return true;
	    }
		
	    return false;
	}	

    }


    //------------------ stuff concerned with explicit and implicit elements----
    
    private static class ExplicitProgramVariableSort
	extends LeftHandSideSort {

	public ExplicitProgramVariableSort() {
	    super(new Name("ExplicitVariable"));
	}

	public boolean canStandFor(Term t) {
	    return (t.op() instanceof ProgramVariable);
	}

	protected boolean canStandFor(ProgramElement pe,
				      Services services) {
	    return (super.canStandFor(pe, services) && !implicit(pe));
	}
    }

    private static class ImplicitProgramVariableSort
	extends LeftHandSideSort {

	public ImplicitProgramVariableSort() {
	    super(new Name("ImplicitVariable"));
	}

	public boolean canStandFor(Term t) {
	    return (t.op() instanceof ProgramVariable && 
                    implicit((ProgramVariable)t.op()));
	}

	protected boolean canStandFor(ProgramElement pe,
				      Services services) {
	    return super.canStandFor(pe, services) && implicit(pe);
	}
    }



    private static class ConstantProgramVariableSort 
	extends ProgramSVSort {

	public ConstantProgramVariableSort() {
	    super(new Name("ConstantVariable"));
	}

	public boolean canStandFor(Term t) {	   
	    return t.op () instanceof ProgramConstant;
	}

	protected boolean canStandFor(ProgramElement pe,
				      Services services) {
	    return false;
	}
    }

    private abstract static class NameMatchingSort 
	extends ProgramSVSort {

	protected final String[] matchingNames;
	
	private final boolean ignorePrivatePrefix;

	public NameMatchingSort(Name name, boolean ignorePrivatePrefix) {
	    super(name);
	    this.matchingNames = new String[1];
	    this.ignorePrivatePrefix = ignorePrivatePrefix;
	}

	public NameMatchingSort(Name name,
				String nameStr, 
				boolean ignorePrivatePrefix) {
	    super(name);
	    this.matchingNames = new String[]{nameStr};
	    this.ignorePrivatePrefix = ignorePrivatePrefix;
	}

	public NameMatchingSort(Name name,
				String[] nameStrs, 
				boolean ignorePrivatePrefix) {
	    super(name);
	    this.matchingNames = nameStrs;
	    this.ignorePrivatePrefix = ignorePrivatePrefix;
	}

	protected int compareNames(Name name) {
	    final String toCmp;
	    if (ignorePrivatePrefix && name instanceof ProgramElementName) {
	        toCmp = ((ProgramElementName)name).getProgramName();
	        for(int i=0; i<matchingNames.length; i++) {
		  if(toCmp.equals(matchingNames[i]))
		    return i;
		}
		return -1;
	    } else {
	        toCmp = name.toString();
	        for(int i=0; i<matchingNames.length; i++) {
		  if(toCmp.equals(matchingNames[i]))
		    return i;
		}
		return -1;
	    }
	}

	protected boolean allowed(ProgramElement pe, 
				  Services services) {
	    final Name peName; 
	    if (pe instanceof Named) {		
		peName = ((Named)pe).name();		
	    } else if (pe instanceof NamedProgramElement) {
		peName = ((NamedProgramElement)pe).getProgramElementName();
	    } else {
		return false;
	    }	    
	    return (compareNames(peName) >= 0);
	}

	public boolean canStandFor(Term t) {
	    if (t.op() instanceof ProgramInLogic) {
		return (compareNames(t.op().name()) >= 0);
	    }
	    return false;
	}

	protected boolean canStandFor(ProgramElement pe,
				      Services services) {
	    return allowed(pe, services);
	}	

    }


    private static class MethodNameReferenceSort 
	extends NameMatchingSort {

	private ImmutableList<Name> reverseSignature = ImmutableSLList.<Name>nil();
	private String fullTypeName;

	public MethodNameReferenceSort(Name name,
	                               String methodName, 
				       String declaredInType) {
	    super(name, methodName, false);
	    this.fullTypeName = declaredInType;
	}

	public MethodNameReferenceSort(Name name,
	                               String[] methodNames, 
				       String declaredInType) {
	    super(name, methodNames, false);
	    this.fullTypeName = declaredInType;
	}

	public MethodNameReferenceSort(Name name,
	                               String methodName, 
				       String declaredInType,
				       ImmutableList<Name> signature) {
	    this(name, methodName, declaredInType);	    
	    this.reverseSignature = reverse(signature);
	}

	public MethodNameReferenceSort(Name name,
	                               String[] methodNames, 
				       String declaredInType,
				       ImmutableList<Name> signature) {
	    this(name, methodNames, declaredInType);	    
	    this.reverseSignature = reverse(signature);
	}

	private ImmutableList<Name> reverse(ImmutableList<Name> names) {
	    ImmutableList<Name> result = ImmutableSLList.<Name>nil();
        for (Name name1 : names) {
            result = result.append(name1);
        }
	    return result;
	}

	private ImmutableList<Type> createSignature(Services services) {
	    ImmutableList<Type> result = ImmutableSLList.<Type>nil();
        for (Name aReverseSignature : reverseSignature) {
            result = result.prepend(services.getJavaInfo()
                    .getKeYJavaType("" + aReverseSignature));
        }
	    return result;
	}


	public boolean canStandFor(ProgramElement pe,
				   ExecutionContext ec,
				   Services services) {

	    if (pe instanceof MethodReference) {
		final MethodReference mr = (MethodReference)pe;
		final int cmpRes = compareNames(mr.getProgramElementName());
		if (cmpRes >= 0) {
		    final KeYJavaType kjt = 
			services.getJavaInfo().getKeYJavaType(fullTypeName);
		    final MethodDeclaration master = 
			services.getJavaInfo().getProgramMethod
			(kjt, matchingNames[cmpRes], createSignature(services), kjt).
			getMethodDeclaration();
		    return master == mr.method
		          (services, mr.determineStaticPrefixType(services,ec),
		                  ec).getMethodDeclaration();
		}
	    }
	    return false;
	}

	public boolean canStandFor(Term t) {
	    return (t.op() instanceof ProgramMethod && 
		    !((ProgramMethod) t.op()).isModel());
	}

    }

    private static class FieldSort extends NameMatchingSort {

	public FieldSort(Name name, boolean ignorePrivatePrefix) {
	    super(name, ignorePrivatePrefix);
	}

	public FieldSort(Name name, 
			 String field, 
			 boolean ignorePrivatePrefix) {
	    super(name, field, ignorePrivatePrefix);
	}

	public FieldSort(String field) {
	    this(new Name("Field"), field, true);
	}

	protected boolean allowed(ProgramElement pe, Services services) {
	    if (pe instanceof ProgramVariable) {
		return super.allowed(pe, services);
	    }
	    if (pe instanceof ProgramSVProxy) {
 		return true;
	    }
	    return false;
	}


	public boolean canStandFor(Term t) {
	    if (t.op() instanceof ProgramVariable) {
		return super.canStandFor(t);
	    }
	    return false;
	}

	protected boolean canStandFor(ProgramElement pe,
				      Services services) {
	    return allowed(pe, services);
	}
	
    }

    private static class ImplicitFieldSort extends FieldSort {
	
	public ImplicitFieldSort(Name name, boolean ignorePrivatePrefix) {
	    super(name, ignorePrivatePrefix);
	}

	public ImplicitFieldSort(boolean ignorePrivatePrefix) {
	    this(new Name("ImplicitField"), ignorePrivatePrefix);
	}

	public ImplicitFieldSort(String field, boolean ignorePrivatePrefix) {
	    super(new Name("ImplicitField"), field, ignorePrivatePrefix);
	}

	public ImplicitFieldSort(Name name, String field, boolean ignorePrivatePrefix) {
	    super(name, field, ignorePrivatePrefix);
	}
	

	// %%% we should move information from the variable
	// specification to the program variable %RB
	protected boolean allowed(ProgramElement pe, Services services) {
	    if (pe instanceof ProgramSVProxy) {
 		return true;
	    }
	    return super.allowed(pe, services) ||  
		(matchingNames[0] == null && pe instanceof ProgramVariable && implicit(pe));
	}

	public boolean canStandFor(Term t) {
            boolean result = false;
	    if (t.op() instanceof ProgramVariable) {
		result = allowed((ProgramVariable)t.op(), null);
	    }
	    return result;
	}

	protected boolean canStandFor(ProgramElement pe,
				      Services services) {
	    ProgramElement var = pe;
	    if (pe instanceof ImplicitFieldSpecification) {
		var = ((ImplicitFieldSpecification)pe).getProgramVariable();
	    } else if (pe instanceof FieldReference) {
		var = ((FieldReference)pe).getProgramVariable();
	    }
	    return allowed(var, services);		
	}
    }


    private static class ImplicitFieldReferenceSort 
	extends ImplicitFieldSort {

	public ImplicitFieldReferenceSort() {
	    super(new Name("ImplicitReferenceField"), true);
	}

	// %%% we should move information from the variable
	// specification to the program variable %RB
	// implicit fields are not of array type so we do not check for
	// this reference type
	protected boolean allowed(ProgramElement pe, Services services) {
	    return super.allowed(pe, services) &&
		((ProgramVariable)pe).getKeYJavaType().getJavaType()
		instanceof ClassType;
	}
    }

    private static class ArrayLengthSort extends ProgramSVSort {

        public ArrayLengthSort() {
            super(new Name("ArrayLength"));            
        }

        protected boolean canStandFor(ProgramElement check, 
                Services services) {            
            if (check instanceof ProgramVariable) {
                return check == services.getJavaInfo().getArrayLength();
            }
            return false;
        }
        
        
    }
    
    private static class ExecutionContextSort extends ProgramSVSort {

	public ExecutionContextSort() {
	    super(new Name("ExecutionContext"));
	}
	
	protected boolean canStandFor(ProgramElement check, 
				      Services services) {
	    return (check instanceof ExecutionContext);
	}
    } 

 
    //-------------------helper methods ------------------------------------
    
    static boolean methodConstrReference(ProgramElement pe) {
	return ((pe instanceof MethodReference)
		|| (pe instanceof ConstructorReference)
		|| (pe instanceof SpecialConstructorReference));
    }

    public ProgramElement getSVWithSort(ExtList l, Class alternative) {
        for (Object aL : l) {
            Object o = aL;
            if (o instanceof SortedSchemaVariable
                    && (((SortedSchemaVariable) o).sort() == this)) {
                return (ProgramElement) o;
            } else if ((alternative.isInstance(o))
                    && (!(o instanceof SchemaVariable))) {
                return (ProgramElement) o;
            }
        }
	return null;
    }

    static KeYJavaType getKeYJavaType(ProgramElement pe, ExecutionContext ec, Services services) {
	return services.getTypeConverter().getKeYJavaType((Expression)pe, ec);
    }

    static boolean excludedMethodName(Name name) {
        if(((MethodNameReferenceSort)JCMAKETRANSIENTARRAY).compareNames(name) >= 0)
	    return true;
	return false;
    }

    static boolean implicit(ProgramElement pe) {
	if (pe instanceof ProgramVariable) {
	    if (!((ProgramVariable)pe).isMember()) return false;
        }
        
	final String elemname;
	if (pe instanceof NamedProgramElement) {
	    elemname = ((NamedProgramElement)pe).getProgramElementName().getProgramName();
	} else if (pe instanceof Named) {
	    final Name n = ((Named)pe).name();
	    if (n instanceof ProgramElementName) {
		elemname = ((ProgramElementName)n).getProgramName();
	    } else {
		elemname = n.toString();
	    }
	} else {
	    System.err.println("Please check implicit in ProgramSVSort");
	    return false;
	}
	return elemname.charAt(0)=='<';
    }

    public static HashMap<Name, ProgramSVSort> name2sort() {
        return name2sort;
    }
   
}
