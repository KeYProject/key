// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java;


import recoder.service.ConstantEvaluator;
import de.uka.ilkd.key.explicitheap.ExplicitHeapConverter;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.ldt.*;
import de.uka.ilkd.key.logic.ProgramInLogic;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.ldt.ListOfLDT;
import de.uka.ilkd.key.ldt.SLListOfLDT;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortDefiningSymbols;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;


public final class TypeConverter {
    
    private static final TermBuilder TB = TermBuilder.DF;
    private static final ExplicitHeapConverter EHC = ExplicitHeapConverter.INSTANCE;

    private final Services services;
      
    private ByteLDT byteLDT;
    private ShortLDT shortLDT;
    private IntLDT intLDT;
    private LongLDT longLDT;
    private CharLDT charLDT;
    private IntegerLDT integerLDT;
    private IntegerDomainLDT integerDomainLDT;
    private BooleanLDT booleanLDT;
    private PairLDT pairLDT;
    private SetLDT setLDT;
    private HeapLDT heapLDT;
    
    private ListOfLDT models = SLListOfLDT.EMPTY_LIST;

    public static StringConverter stringConverter = new StringConverter();
    

    TypeConverter(Services s){
        services = s;       
    }

    
    /**
     * initializes the type converter with an LDT
     */
    public void init(LDT ldt) {	
        if (ldt instanceof ByteLDT) {
            this.byteLDT = (ByteLDT)ldt;
        } else if (ldt instanceof ShortLDT) {
            this.shortLDT = (ShortLDT)ldt;
        } else if (ldt instanceof IntLDT) {
            this.intLDT = (IntLDT)ldt;
        } else if (ldt instanceof LongLDT) {
            this.longLDT = (LongLDT)ldt;
        } else if (ldt instanceof CharLDT) {
            this.charLDT = (CharLDT)ldt;
        } else if (ldt instanceof IntegerLDT) {
            this.integerLDT = (IntegerLDT)ldt;
        } else if (ldt instanceof IntegerDomainLDT) {
            this.integerDomainLDT = (IntegerDomainLDT)ldt;
        } else if (ldt instanceof BooleanLDT) {
            this.booleanLDT = (BooleanLDT)ldt;
        } else if (ldt instanceof PairLDT) {
            this.pairLDT = (PairLDT) ldt;
        } else if (ldt instanceof SetLDT) {
            this.setLDT = (SetLDT) ldt;
        } else if (ldt instanceof HeapLDT) {
            this.heapLDT = (HeapLDT)ldt;
        }

        this.models = this.models.prepend(ldt);
        Debug.out("Initialize LDTs: ", ldt);
    }
    
    
    public void init(ListOfLDT ldts) {
	for(LDT ldt : ldts) {
	    init(ldt);
	}
    }
    
    
    public ListOfLDT getModels() {
        return models;
    }

    
    public Services getServices() {
	return services;
    }
    

    public LDT getModelFor(Type t) {	
	for(LDT ldt : models) {	    
	    if(t.equals(ldt.javaType())) {
		return ldt;		
	    }
	}
        Debug.out("typeconverter: No LDT found for ", t);
        return null;
    }
    

    public LDT getModelFor(Sort s) {
	for(LDT ldt : models) {
	    if(s.equals(ldt.targetSort())) {
		return ldt;
	    }
	}
        Debug.out("No LDT found for ", s);
        return null;
    }

    
    public IntegerLDT getIntegerLDT() {
        return integerLDT;
    }
    
    
    public IntegerDomainLDT getIntegerDomainLDT() {
        return integerDomainLDT;
    }
    
    
    public ByteLDT getByteLDT() {
        return  byteLDT;
    }
    
    
    public ShortLDT getShortLDT() {
        return  shortLDT;
    }
    
    
    public IntLDT getIntLDT() {
        return  intLDT;
    }
    
    
    public LongLDT getLongLDT() {
        return  longLDT;
    }
    
    
    public CharLDT getCharLDT() {
        return  charLDT;
    }
    

    public BooleanLDT getBooleanLDT() {
	return booleanLDT;
    }

 
    public PairLDT getPairLDT() {
	return pairLDT;
    }

    
    public SetLDT getSetLDT() {
	return setLDT;
    }

    
    public HeapLDT getHeapLDT() {
	return heapLDT;
    }
    

    private Term translateOperator
	(de.uka.ilkd.key.java.expression.Operator op,
	 LDT intLDT, LDT booleanLDT, ExecutionContext ec) {

	final Term[] subs  = new Term[op.getArity()];
	if (op.getArity() >= 1) {
	    subs[0] = convertToLogicElement(op.getExpressionAt(0), ec);
	}
	if (op.getArity() == 2) {
	    subs[1] = convertToLogicElement(op.getExpressionAt(1), ec);	  
	}	
	
	LDT responsibleLDT = null;
	if (intLDT.isResponsible(op, subs, services, ec)) {
	    responsibleLDT = intLDT;
	} else if (booleanLDT.isResponsible(op, subs, services, ec)) {
	    responsibleLDT = booleanLDT;
	} else{
	    Debug.out("typeconverter: no data type model "+
		      "available to convert:", op, op.getClass());		
	    throw new IllegalArgumentException("TypeConverter could not handle"
					       +" this");
	}
	return TB.func(responsibleLDT.getFunctionFor(op, services, ec), subs);
    }
   

    private Term convertReferencePrefix(ReferencePrefix prefix, 
					ExecutionContext ec) {
	Debug.out("typeconverter: (prefix, class)", prefix, 
		  (prefix != null ? prefix.getClass() : null));		
	if (prefix instanceof FieldReference) {
	    return convertVariableReference((FieldReference) prefix, ec);
	} else if (prefix instanceof MetaClassReference) {
	    Debug.out("typeconverter: "+
		      "WARNING: metaclass-references not supported yet");
	    throw new IllegalArgumentException("TypeConverter could not handle"
					       +" this");
	} else 	if (prefix instanceof ProgramVariable) {
	    // the base case: the leftmost item is a local variable
	    return TB.var((ProgramVariable)prefix);
	} else 	if (prefix instanceof VariableReference) {
	    Debug.out("typeconverter: "+
		      "variablereference:", (((VariableReference)prefix).getProgramVariable()));
	    return TB.var(((VariableReference)prefix).getProgramVariable());
	}  else if (prefix instanceof ArrayReference) {	   
	    return convertArrayReference((ArrayReference)prefix, ec);
	} else if (prefix instanceof ThisReference) {	 
	    if(prefix.getReferencePrefix()!=null && (prefix.getReferencePrefix() instanceof TypeReference)){
	        TypeReference tr = (TypeReference) prefix.getReferencePrefix();
	        KeYJavaType kjt = tr.getKeYJavaType();
	        return findThisForSortExact(kjt.getSort(), ec);
	    }
	    return convertToLogicElement(ec.getRuntimeInstance());
	} else {            
	    Debug.out("typeconverter: WARNING: unknown reference prefix:", 
		      prefix, prefix == null ? null : prefix.getClass());
	    throw new IllegalArgumentException("TypeConverter failed to convert "
					       + prefix);
	}
    }
    
    
    public Term findThisForSortExact(Sort s, ExecutionContext ec){
        ProgramElement pe = ec.getRuntimeInstance();
        if(pe == null) return null;
        Term inst = convertToLogicElement(pe, ec);
        return findThisForSort(s, inst, ec.getTypeReference().getKeYJavaType(), true);
    
    }
    
    public Term findThisForSort(Sort s, ExecutionContext ec){
        ProgramElement pe = ec.getRuntimeInstance();
        if(pe == null) return null;
        Term inst = convertToLogicElement(pe, ec);
        return findThisForSort(s, inst, ec.getTypeReference().getKeYJavaType(), false);
    }
    
    
    public Term findThisForSort(Sort s, Term self, KeYJavaType context, boolean exact){
        Term result = self;
        ProgramVariable inst;
        while(!exact && !context.getSort().extendsTrans(s) ||
                 exact && !context.getSort().equals(s)){
            inst = services.getJavaInfo().getAttribute(
                    ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS, context);
            final Function fieldSymbol = EHC.getFieldSymbol(inst, services);
            result = TB.dot(services, inst.sort(), result, fieldSymbol);
            context = inst.getKeYJavaType();
        }
        return result;      
    }

    
    public Term convertVariableReference(VariableReference fr,
					 ExecutionContext ec) {	       
	Debug.out("TypeConverter: FieldReference: ",fr);
	final ReferencePrefix prefix = fr.getReferencePrefix();
	final ProgramVariable var = fr.getProgramVariable();
	if (var.isStatic()) {
	    final Function fieldSymbol = EHC.getFieldSymbol(var, services);
	    return TB.staticDot(services, var.sort(), fieldSymbol);
	} else if (prefix == null) {
	    if (var.isMember()) {
		final Function fieldSymbol = EHC.getFieldSymbol(var, services);
		return TB.dot(services, var.sort(), findThisForSort(var.getContainerType().getSort(), ec), 
		        fieldSymbol);
	    }
	    return TB.var(var); 
	} else if (!(prefix instanceof PackageReference) ) {
	    final Function fieldSymbol = EHC.getFieldSymbol(var, services);
	    return TB.dot(services, var.sort(), convertReferencePrefix(prefix, ec), fieldSymbol);
	} 
	Debug.out("typeconverter: Not supported reference type (fr, class):",
		  fr, fr.getClass());
	throw new IllegalArgumentException
	    ("TypeConverter could not handle this");	
    }
    

    public Term convertArrayReference(ArrayReference ar, 
				      ExecutionContext ec){
        final Term[] index = new Term[ar.getDimensionExpressions().size()];
        final Term t = convertToLogicElement(ar.getReferencePrefix(), ec);
        for (int i=0; i<index.length; i++) { 
            index[i] = 
                convertToLogicElement(ar.getDimensionExpressions().getExpression(i), ec);
        }
        assert index.length == 1 : "multi-dimensional arrays not implemented";
        return TB.array(services, t, index[0]);
    }

    private Term convertToInstanceofTerm(Instanceof io, 
					 ExecutionContext ec) {
	final KeYJavaType type = ((TypeReference)io.getChildAt(1)).
	    getKeYJavaType();
	final Term obj = convertToLogicElement(io.getChildAt(0), ec);
	final SortDefiningSymbols s = (SortDefiningSymbols) type.getSort();
	final InstanceofSymbol instanceOfSymbol = 
	    (InstanceofSymbol)s.lookupSymbol(InstanceofSymbol.NAME);
	
	// in JavaDL S::instance(o) is also true if o (for reference types S)
	// is null in opposite to Java
	// we create here if (obj = null) then FALSE else S::instance(obj) 				      
	return TB.ife(TB.equals(obj, TB.NULL(services)), TB.FALSE(services), 
                TB.func(instanceOfSymbol, obj));
    }
  

    public Term convertToLogicElement(ProgramElement pe) {
	return convertToLogicElement(pe, null);	
    }

    
    public Term convertToLogicElement(ProgramElement pe, 				    
				      ExecutionContext ec) {
	Debug.out("typeconverter: called for:", pe, pe.getClass());
	if (pe instanceof ProgramVariable) {	  
	    return TB.var((ProgramVariable)pe);
	} else if (pe instanceof FieldReference) {
	    return convertVariableReference((FieldReference)pe, ec);
	} else if (pe instanceof VariableReference) {
	    return convertVariableReference((VariableReference)pe, ec);
	} else if (pe instanceof ArrayReference){
	    return convertArrayReference((ArrayReference)pe, ec);
	} else if (pe instanceof Literal) {
	    return convertLiteralExpression((Literal)pe);
	} else if (pe instanceof Negative
	        && ((Negative)pe).getChildAt(0) instanceof IntLiteral) {
	    String val = ((IntLiteral)((Negative)pe).getChildAt(0)).getValue();
	    if (val.charAt(0)=='-') {
		return intLDT.translateLiteral
		    (new IntLiteral(val.substring(1)));
	    } else {
		return intLDT.translateLiteral
		    (new IntLiteral("-"+val));
	    }
	} else if (pe instanceof Negative 
		   && ((Negative)pe).getChildAt(0) instanceof LongLiteral ) {
	    String val = ((LongLiteral)
			  ((Negative)pe).getChildAt(0)).getValue();
	    if (val.charAt(0)=='-') {
		return intLDT.translateLiteral
		    (new LongLiteral(val.substring(1)));
	    } else {
		return intLDT.translateLiteral
		    (new LongLiteral("-"+val));
	    }
	} else if (pe instanceof ThisReference) {
	    return convertReferencePrefix((ThisReference)pe, ec);
	} else if (pe instanceof ParenthesizedExpression) {
            return convertToLogicElement
                (((ParenthesizedExpression)pe).getChildAt(0), ec);
        } else if (pe instanceof Instanceof) {
	    return convertToInstanceofTerm((Instanceof)pe, ec);
	} else if (pe instanceof de.uka.ilkd.key.java.expression.Operator) {
	    return translateOperator
		((de.uka.ilkd.key.java.expression.Operator)pe,
		 intLDT, booleanLDT, ec);
	} else if (pe instanceof PrimitiveType) {
	    throw new IllegalArgumentException("TypeConverter could not handle"
					       +" this primitive type");
	} else if (pe instanceof MetaClassReference) {
	    assert false : "not supported";
        }  
	throw new IllegalArgumentException
	    ("TypeConverter: Unknown or not convertable ProgramElement " + pe+
             " of type "+pe.getClass());
    }

    
    /**
     * dispatches the given literal and converts it
     * @param lit the Literal to be converted
     * @return the Term representing <tt>lit</tt> in the logic
     */
    private Term convertLiteralExpression(Literal lit) {      
        if (lit instanceof BooleanLiteral) {   
            return booleanLDT.translateLiteral(lit);
        } else if (lit instanceof NullLiteral) {
            return services.getJavaInfo().getNullConst();
        } else if (lit instanceof IntLiteral) {
            return intLDT.translateLiteral(lit);
        } else if (lit instanceof CharLiteral) {
            return intLDT.translateLiteral(lit);
        } else if (lit instanceof LongLiteral) {
            return intLDT.translateLiteral(lit);
        } else if (lit instanceof StringLiteral) {
            return stringConverter.translateLiteral(lit,intLDT,services);
        } else {
            Debug.fail("Unknown literal type", lit);                 
            return null;
        }
    }
    

    public static boolean isArithmeticOperator
	(de.uka.ilkd.key.java.expression.Operator op) {
	if (op instanceof Divide || op instanceof Times || 
	    op instanceof Plus || op instanceof Minus || 
	    op instanceof Modulo || op instanceof ShiftLeft ||
	    op instanceof ShiftRight || op instanceof BinaryAnd || 
	    op instanceof BinaryNot || op instanceof BinaryOr || 
	    op instanceof BinaryXOr || op instanceof Negative || 
	    op instanceof PreIncrement || op instanceof PostIncrement ||
	    op instanceof PreDecrement || op instanceof PostDecrement) {
	    return true;
	} 
	return false;
    }

    
    /**
     * performs binary numeric promotion on the argument types
     */
    public KeYJavaType getPromotedType(KeYJavaType type1, 
            KeYJavaType type2) {
        final Type t1 = type1.getJavaType();
        final Type t2 = type2.getJavaType();

        if ((t1 == PrimitiveType.JAVA_BOOLEAN &&
                t2 == PrimitiveType.JAVA_BOOLEAN))
            return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BOOLEAN);
        if ((t1 == PrimitiveType.JAVA_BYTE ||
                t1 == PrimitiveType.JAVA_SHORT ||
                t1 == PrimitiveType.JAVA_CHAR||
                t1 == PrimitiveType.JAVA_INT) &&
                (t2 == PrimitiveType.JAVA_BYTE||
                        t2 == PrimitiveType.JAVA_SHORT||
                        t2 == PrimitiveType.JAVA_CHAR||
                        t2 == PrimitiveType.JAVA_INT))
            return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_INT);
        if ((t2 == PrimitiveType.JAVA_LONG) &&
                (t1 == PrimitiveType.JAVA_BYTE||
                        t1 == PrimitiveType.JAVA_SHORT||
                        t1 == PrimitiveType.JAVA_INT||
                        t1 == PrimitiveType.JAVA_CHAR||
                        t1 == PrimitiveType.JAVA_LONG)) 
            return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_LONG);
        if ((t1 == PrimitiveType.JAVA_LONG) &&
                (t2 == PrimitiveType.JAVA_BYTE||
                        t2 == PrimitiveType.JAVA_SHORT||
                        t2 == PrimitiveType.JAVA_INT||
                        t2 == PrimitiveType.JAVA_CHAR||
                        t2 == PrimitiveType.JAVA_LONG)) 
            return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_LONG);		    
        throw new RuntimeException("Could not determine promoted type "+
                "of "+t1+" and "+t2);
    }


    // this method performs unary numeric promotion on the arguments
    public KeYJavaType getPromotedType(KeYJavaType type1) {
        final Type t1 = type1.getJavaType();
	if (t1 == PrimitiveType.JAVA_BOOLEAN)
	    // not really numeric ...
	    return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BOOLEAN);
	if (t1 == PrimitiveType.JAVA_BYTE ||
	    t1 == PrimitiveType.JAVA_SHORT||
	    t1 == PrimitiveType.JAVA_CHAR||
	    t1 == PrimitiveType.JAVA_INT)
	    return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_INT);
	if (t1 == PrimitiveType.JAVA_LONG)
	    return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_LONG);
	throw new RuntimeException("Could not determine promoted type "+
				   "of "+type1);
    }


    public KeYJavaType getBooleanType() {
	return booleanLDT.getKeYJavaType();
    }

    
    public Sort getPrimitiveSort(Type t) {
	LDT result = getModelFor(t);
        return (result == null ? null : result.targetSort());
    }

    
    /** 
     * Retrieves the static type of the expression. This method may only be called
     * if the expressions type can be determined without knowledge of context 
     * information, i.e. it must not be a expression with an ex-/or implicit this 
     * reference like this.a or a methodcall whose value can only be determined
     * when one knows the exact invocation context. 
     * 
     * For these cases please use @link #getKeYJavaType(Expression, ExecutionContext)
     * 
     * This method behaves same as invoking <code>getKeYJavaType(e, null)</code>
     */
    public KeYJavaType getKeYJavaType(Expression e){
	return getKeYJavaType(e, null);
    }
    

    /** 
     * retrieves the type of the expression <tt>e</tt> with respect to 
     * the context in which it is evaluated
     * @param e the Expression whose type has to be retrieved
     * @param ec the ExecutionContext of expression <tt>e</tt>
     * @return the KeYJavaType of expression <tt>e</tt>
     */
    public KeYJavaType getKeYJavaType(Expression e, ExecutionContext ec) {
	if(e instanceof ThisReference){
	    return ec.getTypeReference().getKeYJavaType();
	}	
	return e.getKeYJavaType(services, ec);
    }

    
    /**
     * converts a logical term to an AST node if possible. If this fails
     * it throws a runtime exception.
     * @param term the Term to be converted
     * @return the Term as an program AST node of type expression
     * @throws RuntimeException iff a conversion is not possible
     */
    public Expression convertToProgramElement(Term term) {
	if (term.op()==Function.NULL) {
	    return NullLiteral.NULL;
	} else if (term.op() instanceof Function) {
	    for(LDT model : models) {
                if (model.hasLiteralFunction((Function)term.op())) {
                    return model.translateTerm(term, null);	       
                }
            }
	}
        
	final ExtList children = new ExtList();
	for (int i=0; i<term.arity(); i++) {
	    children.add(convertToProgramElement(term.sub(i)));
	}
	if (term.op() instanceof ProgramInLogic) {
	    return ((ProgramInLogic)term.op()).convertToProgram(term, children);
	} else if (term.op() instanceof Function) {
	    for(LDT model : models) {
                if (model.containsFunction((Function)term.op())) {             
                    return model.translateTerm(term, children);
                }  
	    }
	} 
	throw new RuntimeException("Cannot convert term to program: "+term
				   +" "+term.op().getClass());
    }

    
    public KeYJavaType getKeYJavaType(Term t) {
        KeYJavaType result = services.getJavaInfo().getKeYJavaType(t.sort());        
        if (result == null) {
           result = getKeYJavaType(convertToProgramElement(t));
        }
 
	return result;
    }

    
    public KeYJavaType getKeYJavaType(Type t) {        
	if ( t instanceof KeYJavaType )
	    return (KeYJavaType)t;
	final LDT model = getModelFor(t);
	if (model != null) {
	    return model.getKeYJavaType();
	} else {
	    Debug.out("javainfo: no predefined model for type ",t);
	    return null;
	}	
    }


    /** These methods are taken from recoder (and modified) */
    public boolean isWidening(PrimitiveType from, PrimitiveType to) {
	// we do not handle null's
	if (from == null || to == null) return false;
	// equal types can be coerced
	if (from == to ) return true;
	// boolean types cannot be coerced into something else
	if (from == PrimitiveType.JAVA_BOOLEAN ||
	    to == PrimitiveType.JAVA_BOOLEAN)	    
	    return false;
	// everything else can be coerced to a double
	if (to == PrimitiveType.JAVA_DOUBLE) return true;
	// but a double cannot be coerced to anything else
	if (from == PrimitiveType.JAVA_DOUBLE) return false;
	// everything except doubles can be coerced to a float
	if (to == PrimitiveType.JAVA_FLOAT) return true;
	// but a float cannot be coerced to anything but float or double
	if (from == PrimitiveType.JAVA_FLOAT) return false;	
	// everything except float or double can be coerced to a long
	if (to == PrimitiveType.JAVA_LONG) return true;
	// but a long cannot be coerced to anything but float, double or long
	if (from == PrimitiveType.JAVA_LONG) return false;
	// everything except long, float or double can be coerced to an int
	if (to == PrimitiveType.JAVA_INT) return true;
	// but an int cannot be coerced to the remaining byte, char, short
	if (from == PrimitiveType.JAVA_INT) return false;
	// between byte, char, short, only one conversion is admissible
	return (from == PrimitiveType.JAVA_BYTE &&
		to == PrimitiveType.JAVA_SHORT);
    }

    
    public boolean isWidening(ClassType from, ClassType to) {
	return isWidening ( getKeYJavaType ( from ),
			    getKeYJavaType ( to   ) );
    }
    

    public boolean isWidening(ArrayType from, ArrayType to) {
	KeYJavaType toBase   =  to.getBaseType().getKeYJavaType();
	if (toBase == 
	    services.getJavaInfo().getJavaLangObject() ) { // seems incorrect
	    return true;
	}
	KeYJavaType fromBase = from.getBaseType().getKeYJavaType();
	if (toBase.getJavaType () instanceof PrimitiveType) {
	    return toBase == fromBase;
	}
	return isWidening(fromBase, toBase);
    }
    
    
    public boolean isWidening(Type from, Type to) {
	if ( from instanceof KeYJavaType )
	    return isWidening ( (KeYJavaType)from,
				getKeYJavaType ( to ) );
	if ( to   instanceof KeYJavaType )
	    return isWidening ( getKeYJavaType ( from ),
				(KeYJavaType)to );

	if (from instanceof ClassType) {
	    return isWidening ( getKeYJavaType ( from ),
				getKeYJavaType ( to   ) );
	} else if (from instanceof PrimitiveType) {
	    if (to instanceof PrimitiveType) {
		return isWidening((PrimitiveType)from, (PrimitiveType)to);
	    }
	} else if (from instanceof ArrayType) {
	    if (to instanceof ClassType) {
                final Sort toSort = getKeYJavaType ( to ).getSort(); 		
		return services.getJavaInfo().isAJavaCommonSort(toSort);
	    } else if (to instanceof ArrayType) {
		return isWidening((ArrayType)from, (ArrayType)to);
	    }
	}
	return false;
    }    

    
    // this also handles class types
    public boolean isWidening(KeYJavaType from, KeYJavaType to) {
	Type a = from.getJavaType ();
	Type b = to  .getJavaType ();

	if ( a instanceof ClassType || a == null ) {
	    return
		from.getSort ().extendsTrans ( to.getSort () ) ||
		( a == NullType.JAVA_NULL &&
		  b instanceof ArrayType );
	} else {
	    if ( b == null )
		return
		    to == services.getJavaInfo().
		    getJavaLangObject () &&
		    a instanceof ArrayType;
	    else
		return isWidening ( a, b );
	}
    }


    public boolean isImplicitNarrowing
	(Expression expr, PrimitiveType to) {
	
	int minValue, maxValue;
	if (to == PrimitiveType.JAVA_BYTE) {
	    minValue = Byte.MIN_VALUE;
	    maxValue = Byte.MAX_VALUE;
	} else if (to == PrimitiveType.JAVA_CHAR) {
	    minValue = Character.MIN_VALUE;
	    maxValue = Character.MAX_VALUE;
	} else if (to == PrimitiveType.JAVA_SHORT) {
	    minValue = Short.MIN_VALUE;
	    maxValue = Short.MAX_VALUE;
	} else {
	    return false;
	}

	ConstantExpressionEvaluator cee = 
	    services.getConstantExpressionEvaluator();

	ConstantEvaluator.EvaluationResult res = 
	    new ConstantEvaluator.EvaluationResult();

	if (!cee.isCompileTimeConstant(expr, res) || 
	    res.getTypeCode() != ConstantEvaluator.INT_TYPE) {
	    return false;
	}
	int value = res.getInt();
	return (minValue <= value) && (value <= maxValue);	
    }

    
    public boolean isIdentical ( Type from, Type to ) {
	from = getKeYJavaType ( from );
	to   = getKeYJavaType ( to   );
	return from == to;
    }

    
    public boolean isAssignableTo ( Type from, Type to ) {
	return isIdentical ( from, to ) || isWidening ( from, to );
    }

    
    public boolean isAssignableTo ( Expression expr, Type to, ExecutionContext ec ) {
	return
	    ( to instanceof PrimitiveType &&
	      isImplicitNarrowing ( expr, (PrimitiveType)to ) ) ||
	    isIdentical ( expr.getKeYJavaType ( getServices (), ec ), to ) ||
	    isWidening  ( expr.getKeYJavaType ( getServices (), ec ), to );
    }

    
    // this also handles class types
    public boolean isNarrowing(KeYJavaType from, KeYJavaType to) {
	Type a = from.getJavaType ();
	Type b = to  .getJavaType ();

	if ( a instanceof ClassType || a == null ) {
	    return
		to.getSort ().extendsTrans ( from.getSort () ) ||
		( from == services.
		  getJavaInfo().getJavaLangObject () &&
		  a instanceof ArrayType );
	} else {
	    if ( b == null )
		return false;
	    else
		return isNarrowing ( a, b );
	}
    }

    
    public boolean isNarrowing(PrimitiveType from, PrimitiveType to) {
	// we do not handle null's
	if (from == null || to == null) return false;

	if (from == PrimitiveType.JAVA_BYTE) {
	    return (to == PrimitiveType.JAVA_CHAR );
	}
	if (from == PrimitiveType.JAVA_SHORT) {
	    return (to == PrimitiveType.JAVA_BYTE ||
		    to == PrimitiveType.JAVA_CHAR);
	}
	if (from == PrimitiveType.JAVA_CHAR) {
	    return (to == PrimitiveType.JAVA_BYTE ||
		    to == PrimitiveType.JAVA_SHORT);
	}
	if (from == PrimitiveType.JAVA_INT) {
	    return (to == PrimitiveType.JAVA_BYTE ||
		    to == PrimitiveType.JAVA_SHORT ||
		    to == PrimitiveType.JAVA_CHAR);
	}
	if (from == PrimitiveType.JAVA_LONG) {
	    return (to == PrimitiveType.JAVA_BYTE ||
		    to == PrimitiveType.JAVA_SHORT ||
		    to == PrimitiveType.JAVA_CHAR ||
		    to == PrimitiveType.JAVA_INT);
	}
	if (from == PrimitiveType.JAVA_FLOAT) {
	    return (to == PrimitiveType.JAVA_BYTE ||
		    to == PrimitiveType.JAVA_SHORT ||
		    to == PrimitiveType.JAVA_CHAR ||
		    to == PrimitiveType.JAVA_INT ||
		    to == PrimitiveType.JAVA_LONG);
	}
	if (from == PrimitiveType.JAVA_DOUBLE) {
	    return (to == PrimitiveType.JAVA_BYTE ||
		    to == PrimitiveType.JAVA_SHORT ||
		    to == PrimitiveType.JAVA_CHAR ||
		    to == PrimitiveType.JAVA_INT ||
		    to == PrimitiveType.JAVA_LONG ||
		    to == PrimitiveType.JAVA_FLOAT);
	}
	return false;
    }
    

    public boolean isNarrowing(ClassType from, ClassType to) {
	return isNarrowing ( getKeYJavaType ( from ),
			     getKeYJavaType ( to   ) );
    }
    

    public boolean isNarrowing(ArrayType from, ArrayType to) {
	KeYJavaType toBase   = to.getBaseType().getKeYJavaType();
	KeYJavaType fromBase = from.getBaseType().getKeYJavaType();
	return
	    isReferenceType ( toBase   ) &&
	    isReferenceType ( fromBase ) &&
	    isNarrowing(fromBase, toBase);
    }
    

    public boolean isNarrowing(Type from, Type to) {
	if ( from instanceof KeYJavaType )
	    return isNarrowing ( (KeYJavaType)from,
				getKeYJavaType ( to ) );
	if ( to   instanceof KeYJavaType )
	    return isNarrowing ( getKeYJavaType ( from ),
				(KeYJavaType)to );

	if (from instanceof ClassType) {
	    return isNarrowing ( getKeYJavaType ( from ),
				 getKeYJavaType ( to   ) );
	} else if (from instanceof PrimitiveType) {
	    if (to instanceof PrimitiveType) {
		return isNarrowing((PrimitiveType)from, (PrimitiveType)to);
	    }
	} else if (from instanceof ArrayType) {
	    if (to instanceof ArrayType) {
		return isNarrowing((ArrayType)from, (ArrayType)to);
	    }
	}
	return false;
    }

    
    public boolean isCastingTo ( Type from, Type to ) {
	// there is currently no interface handling

	// identity conversion
	if ( isIdentical ( from, to ) )
	    return true;

	// conversions between numeric types are always possible
	if ( isArithmeticType ( from ) &&
	     isArithmeticType ( to   ) )
	    return true;

	// all widening conversions
	if ( isWidening ( from, to ) )
	    return true;

	// narrowing
	return isNarrowing ( from, to );
    }

    
    public boolean isArithmeticType ( Type t ) {
	if ( t instanceof KeYJavaType )
	    t = ((KeYJavaType)t).getJavaType ();
	return
	    t == PrimitiveType.JAVA_BYTE   ||
	    t == PrimitiveType.JAVA_SHORT  ||
	    t == PrimitiveType.JAVA_INT    ||
	    t == PrimitiveType.JAVA_CHAR   ||
	    t == PrimitiveType.JAVA_LONG   ||
	    t == PrimitiveType.JAVA_FLOAT  ||
	    t == PrimitiveType.JAVA_DOUBLE;
    }

    
    public boolean isIntegralType ( Type t ) {
	if ( t instanceof KeYJavaType )
	    t = ((KeYJavaType)t).getJavaType ();
	return
	    t == PrimitiveType.JAVA_BYTE   ||
	    t == PrimitiveType.JAVA_SHORT  ||
	    t == PrimitiveType.JAVA_INT    ||
	    t == PrimitiveType.JAVA_CHAR   ||
	    t == PrimitiveType.JAVA_LONG;
    }

    
    public boolean isReferenceType ( Type t ) {
	if ( t instanceof KeYJavaType )
	    t = ((KeYJavaType)t).getJavaType ();
	return
	    // there is currently no interface handling
	    t == null ||
	    ( t instanceof ClassType && !( t instanceof NullType ) ) ||
	    t instanceof ArrayType;
    }
    

    public boolean isNullType ( Type t ) {
	if ( t instanceof KeYJavaType )
	    t = ((KeYJavaType)t).getJavaType ();
	return
	    t == NullType.JAVA_NULL;
    }
    

    public boolean isBooleanType ( Type t ) {
	if ( t instanceof KeYJavaType )
	    t = ((KeYJavaType)t).getJavaType ();
	return
	    t == PrimitiveType.JAVA_BOOLEAN;
    }
    

    public TypeConverter copy(Services services) {
	final TypeConverter tc = new TypeConverter(services);
	tc.init(models);
	return tc;
    }
}
