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

package de.uka.ilkd.key.logic.sort;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.NamedProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ConstructorDeclaration;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.VariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.StringLiteral;
import de.uka.ilkd.key.java.expression.operator.DLEmbeddedExpression;
import de.uka.ilkd.key.java.expression.operator.Instanceof;
import de.uka.ilkd.key.java.expression.operator.Intersect;
import de.uka.ilkd.key.java.expression.operator.Negative;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.expression.operator.NewArray;
import de.uka.ilkd.key.java.expression.operator.adt.AllFields;
import de.uka.ilkd.key.java.expression.operator.adt.SeqConcat;
import de.uka.ilkd.key.java.expression.operator.adt.SeqReverse;
import de.uka.ilkd.key.java.expression.operator.adt.SeqSingleton;
import de.uka.ilkd.key.java.expression.operator.adt.SeqSub;
import de.uka.ilkd.key.java.expression.operator.adt.SetMinus;
import de.uka.ilkd.key.java.expression.operator.adt.SetUnion;
import de.uka.ilkd.key.java.expression.operator.adt.Singleton;
import de.uka.ilkd.key.java.reference.ConstructorReference;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.SpecialConstructorReference;
import de.uka.ilkd.key.java.reference.SuperReference;
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.ForUpdates;
import de.uka.ilkd.key.java.statement.Guard;
import de.uka.ilkd.key.java.statement.LoopInit;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.Switch;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.ProgramInLogic;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.util.ExtList;

/**
 * Special "sorts" used for schema variables matching program constructs 
 * (class ProgramSV). Not really sorts in the theoretical meaning of the word. 
 */
public abstract class ProgramSVSort extends AbstractSort {

    // Keeps the mapping of ProgramSVSort names to
    // ProgramSVSort instances (helpful in parsing
    // schema variable declarations)
    private static final Map<Name, ProgramSVSort> name2sort =
        new LinkedHashMap<Name, ProgramSVSort>(60);

    //----------- Types of Expression Program SVs ----------------------------
    
    public static final ProgramSVSort LEFTHANDSIDE
	= new LeftHandSideSort();

    public static final ProgramSVSort VARIABLE
	= new ProgramVariableSort();

    public static final ProgramSVSort STATICVARIABLE
	= new StaticVariableSort();
    
    public static final ProgramSVSort LOCALVARIABLE
        = new LocalVariableSort();
    
    public static final ProgramSVSort SIMPLEEXPRESSION 
	= new SimpleExpressionSort();

    public static final ProgramSVSort NONSIMPLEEXPRESSION 
	= new NonSimpleExpressionSort();
    
    public static final ProgramSVSort EXPRESSION
	= new ExpressionSort();


    //----------- Initialisation and Creation expressions -------------------
    
    public static final ProgramSVSort SIMPLE_NEW = new SimpleNewSVSort();
    
    public static final ProgramSVSort NONSIMPLE_NEW = new NonSimpleNewSVSort();    

    public static final ProgramSVSort NEWARRAY = new NewArraySVSort();

    public static final ProgramSVSort ARRAYINITIALIZER
	= new ArrayInitializerSVSort();

    public static final ProgramSVSort SPECIALCONSTRUCTORREFERENCE
	= new SpecialConstructorReferenceSort();

    
    //----------- Expressions with restrictions on kind of type -------------

    public static final NonSimpleMethodReferenceSort NONSIMPLEMETHODREFERENCE
	= new NonSimpleMethodReferenceSort();


    //----------- Types of Statement Program SVs -----------------------------    
    
    public static final ProgramSVSort STATEMENT
	= new StatementSort();

    public static final ProgramSVSort CATCH
	= new CatchSort();

    public static final ProgramSVSort METHODBODY
	= new MethodBodySort();

    public static final ProgramSVSort NONMODELMETHODBODY
	= new NonModelMethodBodySort();

    public static final ProgramSVSort PROGRAMMETHOD
    = new ProgramMethodSort();

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

    
    public static final ProgramSVSort SIMPLEANYJAVANUMBERTYPEEXPRESSION 
	= new SimpleExpressionSpecialPrimitiveTypeSort
	("AnyJavaNumberTypeExpression", new
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
    
    public static final ProgramSVSort SIMPLEJAVABIGINTEXPRESSION
    = new SimpleExpressionSpecialPrimitiveTypeSort
    ("JavaBigintExpression", new PrimitiveType[]{PrimitiveType.JAVA_BIGINT});

    
    public static final ProgramSVSort SIMPLEANYNUMBERTYPEEXPRESSION 
    = new SimpleExpressionSpecialPrimitiveTypeSort
    ("AnyNumberTypeExpression", new
     PrimitiveType[]{PrimitiveType.JAVA_BYTE,
             PrimitiveType.JAVA_SHORT,
             PrimitiveType.JAVA_INT,
             PrimitiveType.JAVA_LONG,
             PrimitiveType.JAVA_CHAR,
             PrimitiveType.JAVA_BIGINT});

    public static final ProgramSVSort SIMPLEJAVABOOLEANEXPRESSION 
	= new SimpleExpressionSpecialPrimitiveTypeSort
	("SimpleJavaBooleanExpression", new
	 PrimitiveType[]{PrimitiveType.JAVA_BOOLEAN});

    public static final ProgramSVSort SIMPLESTRINGEXPRESSION
	= new SimpleExpressionStringSort("SimpleStringExpression");
    
    public static final ProgramSVSort SIMPLENONSTRINGOBJECTEXPRESSION
	= new SimpleExpressionNonStringObjectSort("SimpleNonStringObjectExpression");

    

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

    public static final ProgramSVSort CONSTANT_PRIMITIVE_TYPE_VARIABLE
	= new ConstantProgramVariableSort(new Name("ConstantPrimitiveTypeVariable"), false);

    public static final ProgramSVSort CONSTANT_STRING_VARIABLE
	= new ConstantProgramVariableSort(new Name("ConstantStringVariable"), true);

    
    public static final ProgramSVSort VARIABLEINIT
	= new ProgramSVSort(new Name("VariableInitializer")) {
        public boolean canStandFor(ProgramElement pe, 
                Services services) {
            return true;
        }
    };

    public static final ProgramSVSort NONSTRINGLITERAL = new NonStringLiteralSort();
    public static final ProgramSVSort STRINGLITERAL = new StringLiteralSort();

    //--------------- Specials that match on certain names-----------------

    public static final ProgramSVSort ARRAYLENGTH
	= new ArrayLengthSort();
   
    //---------------REFERENCE SORTS ------------------------
    public static final ProgramSVSort EXECUTIONCONTEXT = new ExecutionContextSort();


    //--------------------------------------------------------------------------
    
    public ProgramSVSort(Name name) {
	super(name, DefaultImmutableSet.<Sort>nil(), false);
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


    public ProgramSVSort createInstance(String parameter) {
      throw new UnsupportedOperationException();
    }

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
	    return t.op() instanceof ProgramVariable;
	    }

	protected boolean canStandFor(ProgramElement pe,
				      Services services) {

	    if (pe instanceof ProgramVariable ||
                pe instanceof ThisReference ||
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
                }
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
    
    private static class LocalVariableSort 
        extends LeftHandSideSort {

        public LocalVariableSort() {
            super (new Name("LocalVariable"));
        }

        public boolean canStandFor(Term t) {       
            return t.op() instanceof ProgramVariable &&
            !((ProgramVariable)t.op()).isStatic();
        }

        protected boolean canStandFor(ProgramElement pe,
                Services services) {
            return pe instanceof ProgramVariable && !((ProgramVariable) pe).isStatic();
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

	    if (pe instanceof StringLiteral)
		return false;

	    if (pe instanceof Literal) {
		return true;
	    }
	    if (pe instanceof Instanceof) {
		ProgramElement v = ((Instanceof) pe).getChildAt(0);
		return VARIABLE.canStandFor(v, services); 
	    }

	    if(pe instanceof SetUnion 
		|| pe instanceof Singleton		    
		|| pe instanceof Intersect 
		|| pe instanceof SetMinus
		|| pe instanceof AllFields
		|| pe instanceof SeqSingleton
		|| pe instanceof SeqConcat
		|| pe instanceof SeqSub
		|| pe instanceof SeqReverse
		|| pe instanceof DLEmbeddedExpression) {
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
     * only string literals, e.g. "abc"
     */
    private static class StringLiteralSort extends ProgramSVSort {
	public StringLiteralSort() {
	    super(new Name("StringLiteral"));
	}

	protected StringLiteralSort(Name n) {
	    super(n);
	}

	// do not match a term
	public boolean canStandFor(Term t) {
	    return false;
	}

	protected boolean canStandFor(ProgramElement pe,
				      Services services) {
	    return (pe instanceof StringLiteral);
	}
    }

    /**
     * This sort represents a type of program schema variables that match
     * only on non-string literals
     */
    private static class NonStringLiteralSort extends ProgramSVSort {

	public NonStringLiteralSort() {
	    super(new Name("NonStringLiteral"));
	}

	protected NonStringLiteralSort(Name n) {
	    super(n);
	}

	// not designed to match on terms
	public boolean canStandFor(Term t) {
	    return false;
	}
	
	protected boolean canStandFor(ProgramElement pe,
				      Services services) {
	    return (pe instanceof Literal
		    && !(pe instanceof StringLiteral));
	}
    }


    //----------- Initialisation and Creation expressions -------------------

    
    /**
     * This sort represents a type of program schema variables that match
     * only on Class Instance Creation Expressions, new C(), where all
     * arguments are simple expressions.
     */
    private static class SimpleNewSVSort extends ProgramSVSort{

	public SimpleNewSVSort() {
	    super(new Name("SimpleInstanceCreation"));
	}

	protected boolean canStandFor(ProgramElement check, 
				      Services services) {
	    if(!(check instanceof New)) {
		return false;
	    }
	    for(Expression arg : ((New)check).getArguments()) {
		if(NONSIMPLEEXPRESSION.canStandFor(arg, services)) {
		    return false;
		}
	    }
	    return true;
        }
    }
    
    
    /**
     * This sort represents a type of program schema variables that match
     * only on Class Instance Creation Expressions, new C(), where at
     * least one argument is a non-simple expression
     */
    private static class NonSimpleNewSVSort extends ProgramSVSort{

	public NonSimpleNewSVSort() {
	    super(new Name("NonSimpleInstanceCreation"));
	}

	protected boolean canStandFor(ProgramElement check, 
				      Services services) {
	    if(!(check instanceof New)) {
		return false;
	    }
	    for(Expression arg : ((New)check).getArguments()) {
		if(NONSIMPLEEXPRESSION.canStandFor(arg, services)) {
		    return true;
		}
	    }
	    return false;
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
    private static final class ArrayInitializerSVSort extends ProgramSVSort{

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
	    return (t.op() instanceof IProgramMethod && 
		    !((IProgramMethod) t.op()).isModel());
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
    private static final class CatchSort extends ProgramSVSort{

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
    private static final class MethodBodySort extends ProgramSVSort{

	public MethodBodySort() {
	    super(new Name("MethodBody"));
	}

	protected boolean canStandFor(ProgramElement check, Services services) {
	    return (check instanceof MethodBodyStatement);
	}
    }

    /**
     * This sort represents a type of program schema variables that
     * match only on method body statements for nonmodel methods for which
     * an implementation is present.
     */    
    private static final class NonModelMethodBodySort extends ProgramSVSort{

	public NonModelMethodBodySort() {
	    super(new Name("NonModelMethodBody"));
	}

	protected boolean canStandFor(ProgramElement pe, Services services) {
	    if(!(pe instanceof MethodBodyStatement)){
		return false;
	    }
	    
            final IProgramMethod pm = 
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
    private static final class NonSimpleMethodReferenceSort extends ProgramSVSort{

	public NonSimpleMethodReferenceSort() {
	    super(new Name("NonSimpleMethodReference"));
	}

	protected boolean canStandFor(ProgramElement pe,
				      Services services) {
	    if(pe instanceof MethodReference) {
		MethodReference mr = (MethodReference)pe;
		// FIX to bug #1223 (according to CS)
		/*
		if (mr.getReferencePrefix() instanceof SuperReference ||
		    mr.getReferencePrefix() instanceof TypeReference) {
		    return false;
		}
		*/
		if (mr.getReferencePrefix() != null && 
		    NONSIMPLEEXPRESSION.canStandFor
		    (mr.getReferencePrefix(), services)) {
		    return false;
		}
 		if (mr.getArguments() == null) {
 		    return false;
 		}
		for (int i = 0; i < mr.getArguments().size(); i++) {
		    if (NONSIMPLEEXPRESSION.canStandFor(mr.getArgumentAt(i),
							services)) {
			return true;
		    } 
		}		
	    }
	    return false;
	}

	public boolean canStandFor(Term t) {
	    return (t.op() instanceof IProgramMethod);
	}
    }

    /**
     * This sort represents a type of program schema variables that
     * match only on program methods
     */    
    private static final class ProgramMethodSort extends ProgramSVSort {

   public ProgramMethodSort() {
       super(new Name("ProgramMethod"));
   }

   protected boolean canStandFor(ProgramElement check, Services services) {
       return (check instanceof IProgramMethod);
   }
    }

    //-----------Types--------------------------------------------------------

    /**
     * This sort represents a type of program schema variables that
     * match only on type references.
     */    
    private static final class TypeReferenceSort extends ProgramSVSort {

	public TypeReferenceSort() {
	    super(new Name("Type"));
	}

	protected boolean canStandFor(ProgramElement check, Services services) {
	    return (check instanceof TypeReference);
	}
    }
    

    /**
     * This sort represents a type of program schema variables that
     * match anything except byte, char, short, int, and long.
     */    
    private static final class TypeReferenceNotPrimitiveSort extends ProgramSVSort {
        
        private final String matchName;

	public TypeReferenceNotPrimitiveSort() {
	    super(new Name("NonPrimitiveType"));
            this.matchName = null;
	}

	public TypeReferenceNotPrimitiveSort(String name) {
	    super(new Name("NonPrimitiveType"+ (name != null ? "[name="+name+"]" : "")));
            this.matchName = name;
	}

	protected boolean canStandFor(ProgramElement check, Services services) {	    
	    if (!(check instanceof TypeReference)) return false;
            if(((TypeReference)(check)).getKeYJavaType().getJavaType() 
		     instanceof PrimitiveType) return false;
            if(matchName != null) {
                return matchName.equals(((TypeReference)(check)).getKeYJavaType().getJavaType().getFullName());
            }
            return true;
	}

        public ProgramSVSort createInstance(String parameter) {
          return new TypeReferenceNotPrimitiveSort(parameter);
        }
    }

    
    //-----------Names--------------------------------------------------------    
    
    /**
     * This sort represents a type of program schema variables that match
     * on names of method references, i.e. the "m" of o.m(p1,pn).
     * 
     * It can also be made to match only specific method names
     * defined by the parameter "name".
     */
    private static class MethodNameSort extends ProgramSVSort{
        private final ProgramElementName methodName;

	public MethodNameSort() {
	    super(new Name("MethodName"));
            this.methodName = null;
	}

        public MethodNameSort(ProgramElementName name) {
	    super(new Name("MethodName" + (name != null ? "[name="+name+"]" : "")));
            this.methodName = name;
        }
        
	protected boolean canStandFor(ProgramElement pe,
				      Services services) {	    
            if(pe instanceof MethodName) {                
                return methodName == null || pe.equals(methodName);
            }
            return false;
	}

        public ProgramSVSort createInstance(String parameter) {
          return new MethodNameSort(new ProgramElementName(parameter));
        }

        public String declarationString() {
           return name().toString();
        }

    }

    /**
     * This sort represents a type of program schema variables that match
     * on labels.
     */
    private static final class LabelSort extends ProgramSVSort{

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
    public static final class SimpleExpressionStringSort 
	extends SimpleExpressionSort{

	public SimpleExpressionStringSort(String name) {
	    super(new Name(name));
	}

	/* Will only match on String variables */
	public boolean canStandFor(ProgramElement check, 
				   ExecutionContext ec,
				   Services services) {
	    if (!super.canStandFor(check, ec, services)) {
		return false;
	    }
	    //String Literal has SideEffects, but SimpleExpressionSort will not match
	    //if (check instanceof StringLiteral) return false;
	    if (check instanceof ProgramVariable) {
		Namespace ns = services.getNamespaces().sorts();
		Sort stringSort = (Sort)ns.lookup(new Name("java.lang.String"));
		return ((ProgramVariable)check).getKeYJavaType().getSort().equals(stringSort);
	    }
	    return false;
	}
    }
    

    public static class SimpleExpressionNonStringObjectSort 
	extends SimpleExpressionSort{

	public SimpleExpressionNonStringObjectSort(String name) {
	    super(new Name(name));
	}

	public boolean canStandFor(ProgramElement check, 
				   ExecutionContext ec,
				   Services services) {
	    if (!super.canStandFor(check, ec, services)) {
		return false;
	    }
	    if (check instanceof ProgramVariable) {
		final Sort checkSort = ((ProgramVariable)check).sort();
		Namespace ns = services.getNamespaces().sorts();
		Sort stringSort = (Sort)ns.lookup(new Name("java.lang.String"));
		return checkSort.extendsTrans(services.getJavaInfo().objectSort()) 
		       && !checkSort.equals(stringSort);
	    }
	    return false;
	}
    }

    //-----------Specials for primitive types---------------------------------


    /**
     * This sort represents a type of program schema variables that match
     * on simple expressions which have a special primitive type.
     */
    private static final class SimpleExpressionSpecialPrimitiveTypeSort 
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
    private static final class ExpressionSpecialPrimitiveTypeSort 
	extends ExpressionSort{

	private final PrimitiveType[] allowed_types;

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
    

    private static final class LoopInitSort extends ProgramSVSort{

	public LoopInitSort() {
	    super(new Name("LoopInit"));
	}

	protected boolean canStandFor(ProgramElement check, Services services) {
	    return (check instanceof LoopInit);
	}
    }

    private static final class GuardSort extends ProgramSVSort{
	public GuardSort() {
	    super(new Name("Guard"));
	}
	
	protected boolean canStandFor(ProgramElement check, Services services) {
	    return (check instanceof Guard);
	}
    }

    private static final class ForUpdatesSort extends ProgramSVSort{
	public ForUpdatesSort() {
	    super(new Name("ForUpdates"));
	}
	protected boolean canStandFor(ProgramElement check, Services services) {
	    return (check instanceof ForUpdates);

	}
    }
    
    private static final class ForLoopSort extends ProgramSVSort {
        public ForLoopSort() {
            super(new Name("ForLoop"));
        }
        protected boolean canStandFor(ProgramElement check, Services services) {
            return (check instanceof For);
        }
    }
        
    private static final class SwitchSVSort extends ProgramSVSort{
	public SwitchSVSort(){
	    super(new Name("Switch"));
	}

	protected boolean canStandFor(ProgramElement pe, 
				      Services services) {
	    return (pe instanceof Switch);
	}
    }

    private static final class MultipleVariableDeclarationSort extends ProgramSVSort{

	public MultipleVariableDeclarationSort() {
	    super(new Name("MultipleVariableDeclaration"));
	}

	protected boolean canStandFor(ProgramElement pe,
				      Services services) {
        return pe instanceof VariableDeclaration &&
                ((VariableDeclaration) pe).getVariables().size() > 1;
	    }

    }

    private static final class ArrayPostDeclarationSort extends ProgramSVSort{

	public ArrayPostDeclarationSort() {
	    super(new Name("ArrayPostDeclaration"));
	}

	protected boolean canStandFor(ProgramElement pe,
				      Services services) {
        return pe instanceof VariableDeclaration &&
                ((VariableDeclaration) pe).getVariables().size() == 1 &&
                ((VariableDeclaration) pe).getVariables().
                        get(0).getDimensions() > 0;

    }

    }


    //------------------ stuff concerned with explicit and implicit elements----
    
    
    private static final class ConstantProgramVariableSort 
	extends ProgramSVSort {

	private final Name type = new Name("java.lang.String");
	private final boolean isString;

	public ConstantProgramVariableSort(Name svSortName, boolean string) {
	    super(svSortName);
	    isString = string;
	}

	
	public boolean canStandFor(Term t) {	   
	    return t.op () instanceof ProgramConstant && 
	    	isString == t.sort().name().equals(type);
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
				  TermServices services) {
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


    private static final class MethodNameReferenceSort 
	extends NameMatchingSort {

	private ImmutableList<Name> reverseSignature = ImmutableSLList.<Name>nil();
	private final String fullTypeName;

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
	    return (t.op() instanceof IProgramMethod && 
		    !((IProgramMethod) t.op()).isModel());
	}

    }


    private static final class ArrayLengthSort extends ProgramSVSort {

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
    
    private static final class ExecutionContextSort extends ProgramSVSort {

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
	return (pe instanceof MethodReference)
		|| (pe instanceof ConstructorReference);
    }

    public ProgramElement getSVWithSort(ExtList l, Class alternative) {
        for (final Object o : l) {
	    if (o instanceof SchemaVariable
		&& (((SchemaVariable)o).sort()==this)) {
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

    public static Map<Name, ProgramSVSort> name2sort() {
        return name2sort;
    }
   
}
