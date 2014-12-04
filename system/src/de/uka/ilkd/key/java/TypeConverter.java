// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java;


import recoder.service.ConstantEvaluator;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.expression.operator.adt.Singleton;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.ldt.*;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramInLogic;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;
import java.util.Map;

public final class TypeConverter {

    private final TermBuilder tb;
    private final Services services;

    // Maps LDT names to LDT instances.
    private Map<Name,LDT> LDTs = null;
    
    private ImmutableList<LDT> models = ImmutableSLList.<LDT>nil();
    
    private HeapLDT heapLDT = null;
    private IntegerLDT integerLDT = null;
    
    TypeConverter(Services s) {
        this.services = s;
        this.tb = services.getTermBuilder();
    }
    
    public void init(){
        init(LDT.getNewLDTInstances(services));
    }
    
    private void init(Map<Name, LDT> map) {
        LDTs = map;
        models = ImmutableSLList.<LDT>nil();
        if (LDTs != null) {
            for (LDT ldt : LDTs.values()) {
                models = models.prepend(ldt);
            }
        }
        heapLDT = getHeapLDT();
        integerLDT = getIntegerLDT();
    }

    public ImmutableList<LDT> getModels() {
        return models;
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
    
    private LDT getLDT(Name ldtName) {
        if (LDTs == null) {
            return null;
        } else {
            return LDTs.get(ldtName);
        }
    }
    
    public IntegerLDT getIntegerLDT() {
        return (IntegerLDT) getLDT(IntegerLDT.NAME);
    }

    public BooleanLDT getBooleanLDT() {
        return (BooleanLDT) getLDT(BooleanLDT.NAME);
    }

    public LocSetLDT getLocSetLDT() {
	return (LocSetLDT) getLDT(LocSetLDT.NAME);
    }

    public HeapLDT getHeapLDT() {
        return (HeapLDT) getLDT(HeapLDT.NAME);
    }

    public SeqLDT getSeqLDT() {
	return (SeqLDT) getLDT(SeqLDT.NAME);
    }
    
    public MapLDT getMapLDT() {
	return (MapLDT) getLDT(MapLDT.NAME);
    }

    public CharListLDT getCharListLDT() {
	return (CharListLDT) getLDT(CharListLDT.NAME);
    }

    private Term translateOperator(de.uka.ilkd.key.java.expression.Operator op, ExecutionContext ec) {

        final Term[] subs = new Term[op.getArity()];
        for (int i = 0, n = op.getArity(); i < n; i++) {
            subs[i] = convertToLogicElement(op.getExpressionAt(i), ec);
        }

        //hack: convert object singleton to location singleton
        if (op instanceof Singleton) {
            assert heapLDT.getSortOfSelect(subs[0].op()) != null : "unexpected argument of \\singleton: " + subs[0];
            return tb.singleton(subs[0].sub(1), subs[0].sub(2));
        }

        LDT responsibleLDT = getResponsibleLDT(op, subs, services, ec);
        if (responsibleLDT != null) {
            return tb.func(responsibleLDT.getFunctionFor(op, services, ec), subs);
        } else if (op instanceof Equals) {
            assert subs.length == 2;
            return tb.equals(subs[0], subs[1]);
        } else if (op instanceof NotEquals) {
            assert subs.length == 2;
            return tb.not(tb.equals(subs[0], subs[1]));
        } else if (op instanceof Conditional) {
            assert subs.length == 3;
            return tb.ife(subs[0], subs[1], subs[2]);
        } else if (op instanceof DLEmbeddedExpression) {
            DLEmbeddedExpression emb = (DLEmbeddedExpression) op;
            return emb.makeTerm(heapLDT.getHeap(), subs, services);
        } else if (op instanceof TypeCast) {
            TypeCast tc = (TypeCast) op;
            return tb.cast(tc.getKeYJavaType(services).getSort(), subs[0]);
        } else {
            Debug.out("typeconverter: no data type model "
                      + "available to convert:", op, op.getClass());
            throw new IllegalArgumentException("TypeConverter could not handle"
                                               + " this operator: " + op);
        }
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
	    return tb.var((ProgramVariable)prefix);
	} else 	if (prefix instanceof VariableReference) {
	    Debug.out("typeconverter: "+
		      "variablereference:", (((VariableReference)prefix).getProgramVariable()));
	    return tb.var(((VariableReference)prefix).getProgramVariable());
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


    public Term findThisForSort(Sort s,
	    			Term self,
	    			KeYJavaType context,
	    			boolean exact) {
        Term result = self;
        LocationVariable inst;
        while(!exact && !context.getSort().extendsTrans(s)
              || exact && !context.getSort().equals(s)){
            inst = (LocationVariable)
                    services.getJavaInfo().getAttribute(
                       ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS, context);
            final Function fieldSymbol
            	= heapLDT.getFieldSymbolForPV(inst, services);
            result = tb.dot(inst.sort(), result, fieldSymbol);
            context = inst.getKeYJavaType();
        }
        return result;
    }

    public Term convertMethodReference(MethodReference mr, ExecutionContext ec) {
        Debug.out("TypeConverter: MethodReference: ", mr);
    	// FIXME this needs to handle two state?
    	final ReferencePrefix prefix = mr.getReferencePrefix();
    	Term p = convertReferencePrefix(prefix, ec);
    	IProgramMethod pm = mr.method(services, services.getTypeConverter().getKeYJavaType(p), ec);
    	if(pm.isModel()) {
    	  ImmutableArray<? extends Expression> args = mr.getArguments();
    	  Term[] argTerms = new Term[args.size()+2]; // heap, self, 
    	  int index = 0;
    	  for(LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps(services)) {
    		  if(h == services.getTypeConverter().getHeapLDT().getSavedHeap()) {
    			  continue;
    		  }
        	  argTerms[index++] = tb.var(h);
    	  }
    	  argTerms[index++] = p;
    	  for(Expression e : args) {
    	       argTerms[index++] = convertToLogicElement(e, ec);
    	  }
    	  return tb.func(pm, argTerms);
    	}
    	throw new IllegalArgumentException ("TypeConverter could not handle this");
    }
 
    public Term convertVariableReference(VariableReference fr,
					 ExecutionContext ec) {
	Debug.out("TypeConverter: FieldReference: ", fr);
	final ReferencePrefix prefix = fr.getReferencePrefix();
	final ProgramVariable var = fr.getProgramVariable();
	if(var instanceof ProgramConstant) {
	    return tb.var(var);
	} else if(var == services.getJavaInfo().getArrayLength()) {
	    return tb.dotLength(convertReferencePrefix(prefix, ec));
	} else if(var.isStatic()) {
	    final Function fieldSymbol
	    	= heapLDT.getFieldSymbolForPV((LocationVariable)var, services);
	    return tb.staticDot(var.sort(), fieldSymbol);
	} else if(prefix == null) {
	    if(var.isMember()) {
		final Function fieldSymbol
			= heapLDT.getFieldSymbolForPV((LocationVariable)var,
						      services);
		return tb.dot(var.sort(),
			      findThisForSort(var.getContainerType().getSort(),
				              ec),
			      fieldSymbol);
	    } else {
		return tb.var(var);
	    }
	} else if (!(prefix instanceof PackageReference) ) {
	    final Function fieldSymbol
	    	= heapLDT.getFieldSymbolForPV((LocationVariable)var, services);
	    return tb.dot(var.sort(), convertReferencePrefix(prefix, ec), fieldSymbol);
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
                convertToLogicElement(ar.getDimensionExpressions().get(i), ec);
        }
        assert index.length == 1 : "multi-dimensional arrays not implemented";
        return tb.dotArr(t, index[0]);
    }

    private Term convertToInstanceofTerm(Instanceof io,
					 ExecutionContext ec) {
	final KeYJavaType type = ((TypeReference)io.getChildAt(1)).
	    getKeYJavaType();
	final Term obj = convertToLogicElement(io.getChildAt(0), ec);
	final Sort s = type.getSort();
	final Function instanceOfSymbol = s.getInstanceofSymbol(services);

	// in JavaDL S::instance(o) is also true if o (for reference types S)
	// is null in opposite to Java
	// we create here if (obj = null) then FALSE else S::instance(obj)
	return tb.ife(tb.equals(obj, tb.NULL()), tb.FALSE(),
                tb.func(instanceOfSymbol, obj));
    }


    public Term convertToLogicElement(ProgramElement pe) {
	return convertToLogicElement(pe, null);
    }


    public Term convertToLogicElement(ProgramElement pe,
				      ExecutionContext ec) {
	Debug.out("typeconverter: called for:", pe, pe.getClass());
	if (pe instanceof ProgramVariable) {
	    return tb.var((ProgramVariable)pe);
	} else if (pe instanceof FieldReference) {
	    return convertVariableReference((FieldReference)pe, ec);
	} else if (pe instanceof MethodReference) {
	    return convertMethodReference((MethodReference)pe, ec);
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
		return integerLDT.translateLiteral
		    (new IntLiteral(val.substring(1)), services);
	    } else {
		return integerLDT.translateLiteral
		    (new IntLiteral("-"+val), services);
	    }
	} else if (pe instanceof Negative
		   && ((Negative)pe).getChildAt(0) instanceof LongLiteral ) {
	    String val = ((LongLiteral)
			  ((Negative)pe).getChildAt(0)).getValue();
	    if (val.charAt(0)=='-') {
		return integerLDT.translateLiteral
		    (new LongLiteral(val.substring(1)), services);
	    } else {
		return integerLDT.translateLiteral
		    (new LongLiteral("-"+val), services);
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
		((de.uka.ilkd.key.java.expression.Operator)pe, ec);
	} else if (pe instanceof recoder.abstraction.PrimitiveType) {
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
        if (lit instanceof NullLiteral) {
            return tb.NULL();
        } else {
            LDT ldt = LDTs.get(lit.getLDTName());
            if (ldt != null) {
                return ldt.translateLiteral(lit, services);
            } else {
                Debug.fail("Unknown literal type", lit);
                return null;
            }
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

        if ((t1 == PrimitiveType.JAVA_REAL && isNumericalType(t2)
                || (isNumericalType(t1) && t2 == PrimitiveType.JAVA_REAL)))
                return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_REAL);
        else if ((t1 == PrimitiveType.JAVA_BOOLEAN &&
                t2 == PrimitiveType.JAVA_BOOLEAN)) {
            return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BOOLEAN);
        } else if ((t1 == PrimitiveType.JAVA_BYTE ||
                t1 == PrimitiveType.JAVA_SHORT ||
                t1 == PrimitiveType.JAVA_CHAR||
                t1 == PrimitiveType.JAVA_INT) &&
                (t2 == PrimitiveType.JAVA_BYTE||
                        t2 == PrimitiveType.JAVA_SHORT||
                        t2 == PrimitiveType.JAVA_CHAR||
                        t2 == PrimitiveType.JAVA_INT)) {
            return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_INT);
    	} else if ((t2 == PrimitiveType.JAVA_LONG) &&
                (t1 == PrimitiveType.JAVA_BYTE||
                        t1 == PrimitiveType.JAVA_SHORT||
                        t1 == PrimitiveType.JAVA_INT||
                        t1 == PrimitiveType.JAVA_CHAR||
                        t1 == PrimitiveType.JAVA_LONG)) {
            return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_LONG);
    	} else if ((t1 == PrimitiveType.JAVA_LONG) &&
                (t2 == PrimitiveType.JAVA_BYTE||
                        t2 == PrimitiveType.JAVA_SHORT||
                        t2 == PrimitiveType.JAVA_INT||
                        t2 == PrimitiveType.JAVA_CHAR||
                        t2 == PrimitiveType.JAVA_LONG)) {
            return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_LONG);
    	} else if ((t1 == PrimitiveType.JAVA_BIGINT) && isIntegerType(t2)) {
    	    return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BIGINT);
        } else if ((t2 == PrimitiveType.JAVA_BIGINT) && isIntegerType(t2)) {
            return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BIGINT);
    	} else if (t1 == PrimitiveType.JAVA_LOCSET && t2 == PrimitiveType.JAVA_LOCSET) {
            return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_LOCSET);
    	} else if (t1 == PrimitiveType.JAVA_SEQ && t2 == PrimitiveType.JAVA_SEQ) {
            return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_SEQ);
    	} else if (type1.equals(services.getJavaInfo().getKeYJavaType("java.lang.String"))) {
            return type1;
    	} else if (type2.equals(services.getJavaInfo().getKeYJavaType("java.lang.String"))) {
            return type2;
        } else {
            throw new RuntimeException("Could not determine promoted type "
        	    	               + "of " + t1 + " and " + t2);
        }
    }

    public boolean isIntegerType(Type t2){
        return (t2 == PrimitiveType.JAVA_BYTE || t2 == PrimitiveType.JAVA_CHAR || t2 == PrimitiveType.JAVA_INT
                || t2 == PrimitiveType.JAVA_LONG || t2 == PrimitiveType.JAVA_SHORT || t2 == PrimitiveType.JAVA_BIGINT);
    }


    // this method performs unary numeric promotion on the arguments
    public KeYJavaType getPromotedType(KeYJavaType type1) {
        final Type t1 = type1.getJavaType();
	if (t1 == PrimitiveType.JAVA_BOOLEAN)
	    // not really numeric ...
	    return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BOOLEAN);
	else if (t1 == PrimitiveType.JAVA_BYTE ||
	    t1 == PrimitiveType.JAVA_SHORT||
	    t1 == PrimitiveType.JAVA_CHAR||
	    t1 == PrimitiveType.JAVA_INT)
	    return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_INT);
	else if (t1 == PrimitiveType.JAVA_LONG)
	    return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_LONG);
	else if (t1 == PrimitiveType.JAVA_LOCSET)
	    return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_LOCSET);
	else if (t1 == PrimitiveType.JAVA_SEQ)
	    return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_SEQ);
	else if (t1 == PrimitiveType.JAVA_BIGINT)
	    return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BIGINT);
	else if (t1 == PrimitiveType.JAVA_REAL)
        return services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_REAL);
	else throw new RuntimeException("Could not determine promoted type "+
				   "of "+type1);
    }


    public KeYJavaType getBooleanType() {
	return services.getJavaInfo()
	               .getKeYJavaType(PrimitiveType.JAVA_BOOLEAN);
    }


    public Sort getPrimitiveSort(Type t) {
	return services.getJavaInfo().getKeYJavaType(t).getSort();
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
        assert term != null;
        if (term.op() == heapLDT.getNull()) {
            return NullLiteral.NULL;
        } else if (term.op() instanceof Function) {
            Function function = (Function)term.op();
            for(LDT model : models) {
                if (model.hasLiteralFunction(function)) {
                    return model.translateTerm(term, null, services);
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
            Function function = (Function)term.op();
            for(LDT model : models) {
                if (model.containsFunction(function)) {
                    return model.translateTerm(term, children, services);
                }
            }
            Expression tryTranslate = translateJavaCast(term, children);
            if(tryTranslate != null) {
                return tryTranslate;
            }
        }
        throw new RuntimeException("Cannot convert term to program: "+term
                +" "+term.op().getClass());
    }


    private Expression translateJavaCast(Term term, ExtList children) {
        if (term.op() instanceof Function) {
            Function function = (Function)term.op();
            if (function instanceof SortDependingFunction) {
                SortDependingFunction sdf = (SortDependingFunction) function;
                SortDependingFunction castFunction =
                        SortDependingFunction.getFirstInstance(Sort.CAST_NAME, services);
                if(sdf.isSimilar(castFunction)) {
                    Sort s = sdf.getSortDependingOn();
                    KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(s);
                    if(kjt != null) {
                        children.add(new TypeRef(kjt));
                        return new ParenthesizedExpression(new TypeCast(children));
                    }
                }
            }
        }
        return null;
    }


    public KeYJavaType getKeYJavaType(Term t) {
	KeYJavaType result = null;
	if(t.sort().extendsTrans(services.getJavaInfo().objectSort())) {
	    result = services.getJavaInfo().getKeYJavaType(t.sort());
	} else if(t.op() instanceof Function) {
	    for(LDT ldt : models) {
		if(ldt.containsFunction((Function)t.op())) {
		    Type type = ldt.getType(t);
		    result = services.getJavaInfo().getKeYJavaType(type);
		    break;
		}
	    }
	}

        if(result == null) {
            //HACK
            result = services.getJavaInfo().getKeYJavaType(t.sort().toString());
        }
        if (result == null) {
           result = getKeYJavaType(convertToProgramElement(t));
        }

	return result;
    }


    public KeYJavaType getKeYJavaType(Type t) {
	return services.getJavaInfo().getKeYJavaType(t);
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
    // everything else can be coerced to a \real
	if (to == PrimitiveType.JAVA_REAL) return true;
	// everything except \real and \bigint can be coerced to a double
	if (to == PrimitiveType.JAVA_DOUBLE) return from != PrimitiveType.JAVA_BIGINT;
	// but a double cannot be coerced to anything else
	if (from == PrimitiveType.JAVA_DOUBLE) return from != PrimitiveType.JAVA_BIGINT;
	// everything except doubles can be coerced to a float
	if (to == PrimitiveType.JAVA_FLOAT) return true;
	// but a float cannot be coerced to anything but float or double
	if (from == PrimitiveType.JAVA_FLOAT) return false;
	// any integral type can be coerced to a \bigint
	if (to == PrimitiveType.JAVA_BIGINT) return true;
	// everything except the above can be coerced to a long
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
    	// XXX causes bug #1163
//		from = getKeYJavaType ( from );
//		to   = getKeYJavaType ( to   );
    	return from == to;
    }


    public boolean isAssignableTo ( Type from, Type to ) {
	return isIdentical ( from, to ) || isWidening ( from, to );
    }


    public boolean isAssignableTo ( Expression expr, Type to, ExecutionContext ec ) {
	return
	    ( to instanceof PrimitiveType &&
	      isImplicitNarrowing ( expr, (PrimitiveType)to ) ) ||
	    isIdentical ( expr.getKeYJavaType ( services, ec ), to ) ||
	    isWidening  ( expr.getKeYJavaType ( services, ec ), to );
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
	if (from == PrimitiveType.JAVA_BIGINT) {
	    return (to != PrimitiveType.JAVA_REAL && to != from);
		}
	if (from == PrimitiveType.JAVA_REAL) {
	    return (to != from);
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
	if ( isNumericalType ( from ) &&
	     isNumericalType ( to   ) )
	    return true;

	// all widening conversions
	if ( isWidening ( from, to ) )
	    return true;

	// narrowing
	return isNarrowing ( from, to );
    }


    public boolean isNumericalType ( Type t ) {
	if ( t instanceof KeYJavaType )
	    t = ((KeYJavaType)t).getJavaType ();
	return
	    t == PrimitiveType.JAVA_BYTE   ||
	    t == PrimitiveType.JAVA_SHORT  ||
	    t == PrimitiveType.JAVA_INT    ||
	    t == PrimitiveType.JAVA_CHAR   ||
	    t == PrimitiveType.JAVA_LONG   ||
	    t == PrimitiveType.JAVA_BIGINT ||
	    t == PrimitiveType.JAVA_FLOAT  ||
	    t == PrimitiveType.JAVA_DOUBLE ||
	    t == PrimitiveType.JAVA_REAL
	    ;
    }


    public boolean isIntegralType ( Type t ) {
	if ( t instanceof KeYJavaType )
	    t = ((KeYJavaType)t).getJavaType ();
	return
	    t == PrimitiveType.JAVA_BYTE   ||
	    t == PrimitiveType.JAVA_SHORT  ||
	    t == PrimitiveType.JAVA_INT    ||
	    t == PrimitiveType.JAVA_CHAR   ||
	    t == PrimitiveType.JAVA_LONG   ||
	    t == PrimitiveType.JAVA_BIGINT;
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
        TypeConverter TC = new TypeConverter(services);
        TC.init(LDTs);
        return TC;
    }

    private LDT getResponsibleLDT(de.uka.ilkd.key.java.expression.Operator op, Term[] subs, Services services, ExecutionContext ec) {
        for (LDT ldt : LDTs.values()) {
            if (ldt.isResponsible(op, subs, services, ec)) {
                return ldt;
            }
        }
        return null;
    }

}
