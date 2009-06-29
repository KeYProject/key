// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * <p>Use this class if you intend to build complex terms by hand. It is 
 * more convenient than the @link{TermFactory} class.</p>
 * 
 * <p>Attention: some methods of this class try to simplify some terms. So if you 
 * want to be sure that the term looks exactly as you built it, you
 * will have to use the TermFactory.</p>
 */
public final class TermBuilder {
    
    public static final TermBuilder DF = new TermBuilder();
    
    protected final static TermFactory tf = TermFactory.DEFAULT;
    
    private final static Term tt = TermFactory.DEFAULT.createJunctorTerm(Op.TRUE); 
    private final static Term ff = TermFactory.DEFAULT.createJunctorTerm(Op.FALSE); 
    
    public TermBuilder() {     
    }
    
    public Term TRUE(Services services) {
        return services.getTypeConverter().getBooleanLDT().getTrueTerm();
    }
    
    public Term FALSE(Services services) {
        return services.getTypeConverter().getBooleanLDT().getFalseTerm();
    }
    
    public Term tt() {
        return tt;
    }
    
    public Term ff() {
        return ff;
    }
    

    public Term all(QuantifiableVariable qv, Term t2) {
        if ( !t2.freeVars().contains ( qv ) ) return t2;
        return tf.createQuantifierTerm ( Op.ALL, qv, t2 );
    }
    
    public Term all(QuantifiableVariable[] qv, Term t2) {
        Term result = t2;
        for (int i=qv.length-1; i>=0; i--) {
            result = all(qv[i], result); 
        }
        return result;
    }
    
    public Term ex(QuantifiableVariable qv, Term t2) {
        if ( !t2.freeVars().contains ( qv ) ) return t2;
        return tf.createQuantifierTerm(Op.EX, qv, t2);
    }
    
    public Term ex(QuantifiableVariable[] qv, Term t2) {
        Term result = t2;
        for (int i=qv.length-1; i>=0; i--) {
            result = ex(qv[i], result);
        }
        return result;
    }
    
    public Term not(Term t) {
        return tf.createJunctorTermAndSimplify(Op.NOT, t);
    }
    
    
    public Term and(Term t1, Term t2) {
        return tf.createJunctorTermAndSimplify(Op.AND, t1, t2);
    }

    public Term and(Term[] subTerms) {
        Term result = tt();
        for (int i=0; i<subTerms.length; i++) {
            result = and( result, subTerms[i]);
        }

        return result;
    }
    
    public Term and(ListOfTerm subTerms) {
	Term result = tt();
	IteratorOfTerm it = subTerms.iterator();
	while(it.hasNext()) {
	    result = and(result, it.next());
	}
	return result;
    }
    
    public Term or(Term t1, Term t2) {
        return tf.createJunctorTermAndSimplify(Op.OR, t1, t2);
    }
    
    public Term or(Term[] subTerms) {
        Term result = ff();
        for (int i=0; i<subTerms.length; i++) {
            result = or( result, subTerms[i]);
        }

        return result;
    }
    
    public Term or(ListOfTerm subTerms) {
	Term result = ff();
	IteratorOfTerm it = subTerms.iterator();
	while(it.hasNext()) {
	    result = or(result, it.next());
	}
	return result;
    }

    
    public Term imp(Term t1, Term t2) {
        return tf.createJunctorTermAndSimplify(Op.IMP, t1, t2);
    }
    
    public Term equals(Term t1, Term t2) {
        if (t1.sort() == Sort.FORMULA ||
                t2.sort() == Sort.FORMULA) {
            throw new IllegalArgumentException("Equals is defined betweens terms, not forumulas: " + 
                    t1 + ", " + t2);
        }
        if ( t1.equals ( t2 ) ) return tt ();
        return tf.createEqualityTerm ( t1, t2 );
    }
    
    public Term equiv(Term t1, Term t2) {
        if (t1.sort() != Sort.FORMULA ||
                t2.sort() != Sort.FORMULA) {
            throw new IllegalArgumentException("Equivalence is defined on formulas not terms: " + 
                    t1 + ", " + t2);
        }
        return tf.createJunctorTermAndSimplify(Op.EQV, t1, t2);
    }
    
    public Term geq(Term t1, Term t2, Services services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return tf.createFunctionTerm(integerLDT.getGreaterOrEquals(), t1, t2);
    }
    
    public Term gt(Term t1, Term t2, Services services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return tf.createFunctionTerm(integerLDT.getGreaterThan(), t1, t2);
    }
    
    public Term lt(Term t1, Term t2, Services services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return tf.createFunctionTerm(integerLDT.getLessThan(), t1, t2);
    }    
    
    public Term leq(Term t1, Term t2, Services services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return tf.createFunctionTerm(integerLDT.getLessOrEquals(), t1, t2);
    }    
    
    public Term zero(Services services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return integerLDT.translateLiteral(new IntLiteral(0));        
    }

    public Term one(Services services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return integerLDT.translateLiteral(new IntLiteral(1));        
    }
    
    public Term NULL(Services services) {
        return services.getJavaInfo().getNullTerm();
    }
    
    public Term array(Term ref, Term idx) {
        if (ref == null || idx == null) {
            throw new TermCreationException("Tried to build an array access "+
                    "term without providing an " +
                    (ref==null ? "array reference." : "index.") + 
                    "("+ref+"["+idx+"])");
        }        
        return tf.createArrayTerm(ArrayOp.getArrayOp(ref.sort()), ref, idx);
    }
    
    public Term dot(Term o, ProgramVariable a) {
        return tf.createAttributeTerm(a, o);
    }

    public Term var(LogicVariable v) {
        return tf.createVariableTerm(v);
    }
    
    public Term var(ProgramVariable v) {   
        if (!v.isStatic() && v.isMember()) {
            throw new IllegalArgumentException("Wrong programvariable kind.");
        }
        return tf.createVariableTerm(v);
    }
    
    public Term var(SchemaVariable v) {
	return tf.createVariableTerm(v);
    }
    
    
    public Term var(ParsableVariable v) {
	if (v instanceof ProgramVariable) {
	    return var((ProgramVariable) v);
	} else if(v instanceof LogicVariable) {
	    return var((LogicVariable) v);
	} else if(v instanceof SchemaVariable) {
	    return var((SchemaVariable) v); 
	} else {
	    throw new IllegalArgumentException("Wrong parsablevariable kind: " 
	                                        + v.getClass());
	}
    }

    public Term func(TermSymbol op) {
        return tf.createFunctionTerm(op);
    }
    
    public Term func(TermSymbol op, Term s) {
        return tf.createFunctionTerm(op, s);
    }
    
    public Term func(TermSymbol op, Term s1, Term s2) {
        return tf.createFunctionTerm(op, s1, s2);
    }
    
    public Term func(TermSymbol op, Term[] s) {
        return tf.createFunctionTerm(op, s);
    }
    
    public Term box(JavaBlock jb, Term t) {
        return tf.createBoxTerm(jb, t);
    }
    
    public Term dia(JavaBlock jb, Term t) {
        return tf.createDiamondTerm(jb, t);
    }
    
    public Term prog(Modality mod, JavaBlock jb, Term t) {
        return tf.createProgramTerm(mod, jb, t);
    }

    public Term ife(Term cond, Term _then, Term _else) {        
        return tf.createIfThenElseTerm(cond, _then, _else);
    }
    
    public TermFactory tf() {
        return tf;
    }

    
    /**
     * builds a Term from a number, given by a String
     * 
     * @param services Services which contains the number-functions
     * @param numberString String representing an integer
     * @return Term in Z-Notation representing the given number
     */
    public Term zTerm(Services services, String numberString){
        Operator v;
        Term t;
        boolean negate = false;
        int j = 0;
        
        Namespace funcNS = services.getNamespaces().functions();
        
        if (numberString.substring(0,1).equals("-")) {
            negate = true;
            j=1;
        }
        v=(Function)  funcNS.lookup(new Name("#"));
        t = func((Function)v);
        v = (Function) funcNS.lookup(new Name(numberString.substring(j,j+1)));
        t = func((Function)v,t);
        for(int i=j+1;i<numberString.length();i++){
            v = (Function)funcNS.lookup(new Name(numberString.substring(i,i+1)));
            t = func((Function)v,t);
        }   
        if (negate) {
            v=(Function) funcNS.lookup(new Name("neglit"));
            t = func((Function) v, t);
        }
        v = (Function) funcNS.lookup(new Name("Z"));
        t = func((Function)v,t);
        return t;
    }
    
    
    public Term inReachableState(Services services) {
        return func(services.getJavaInfo().getInReachableState());
    }
    
    
    
    
    public Term heap(Services services) {
        return var(services.getTypeConverter().getHeapLDT().getHeap());
    }
    
    public Term select(Services services, Term h, Term o, Term f) {
        return func(services.getTypeConverter().getHeapLDT().getSelect(), new Term[]{h, o, f});
    }
    
    public Term store(Services services, Term h, Term o, Term f, Term v) {
        return func(services.getTypeConverter().getHeapLDT().getStore(), new Term[]{h, o, f, v});
    }
        
    public Term dot(Services services, Term o, Function f) {
        return select(services, heap(services), o, func(f));
    }
    
    public Term staticDot(Services services, Function f) {
        return select(services, heap(services), NULL(services), func(f));
    }
    
    public Term arr(Services services, Term o, Term i) {
        return select(services, heap(services), o, func(services.getTypeConverter().getHeapLDT().getArr(), i));
    }
   
    public Term fieldStore(Services services, Term o, Function f, Term v) {
        return store(services, heap(services), o, func(f), v);
    }
    
    public Term staticFieldStore(Services services, Function f, Term v) {
	return fieldStore(services, NULL(services), f, v);
    }
    
    public Term arrayStore(Services services, Term o, Term i, Term v) {
        return store(services, heap(services), o, func(services.getTypeConverter().getHeapLDT().getArr(), i), v);
    }
        
    public Term wellFormedHeap(Services services) {
        return func(services.getTypeConverter().getHeapLDT().getWellFormed(), heap(services));
    }
    
    public Term changeHeapAtLocs(Services services, Term h1, Term s, Term h2) {
	return func(services.getTypeConverter().getHeapLDT().getChangeHeapAtLocs(), new Term[]{h1, s, h2});
    }
    
    public Term empty(Services services) {
	return func(services.getTypeConverter().getSetLDT().getEmpty());
    }
    
    public Term singleton(Services services, Term o, Term f) {
	return func(services.getTypeConverter().getSetLDT().getSingleton(), o, f);
    }
    
    public Term union(Services services, Term s1, Term s2) {
	return func(services.getTypeConverter().getSetLDT().getUnion(), s1, s2);
    }
    
    public Term intersect(Services services, Term s1, Term s2) {
	return func(services.getTypeConverter().getSetLDT().getIntersect(), s1, s2);
    }
    
    public Term setMinus(Services services, Term s1, Term s2) {
	return func(services.getTypeConverter().getSetLDT().getSetMinus(), s1, s2);
    }
    
    public Term complement(Services services, Term s) {
	return func(services.getTypeConverter().getSetLDT().getComplement(), s);
    }
    
    /*public Term allFields(Services services, Term o) {
	return func(services.getJavaInfo().getAllFields(), o);
    }*/
    
    public Term everything(Services services) {
	return func(services.getTypeConverter().getSetLDT().getEverything());
    }
    
    public Term elementOf(Services services, Term o, Term f, Term s) {
	return func(services.getTypeConverter().getSetLDT().getElementOf(), new Term[]{o, f, s});
    }
}
