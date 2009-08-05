// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.*;


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
    
    private static final TermFactory tf = TermFactory.DEFAULT;    
    private static final Term tt = TermFactory.DEFAULT.createTerm(Junctor.TRUE); 
    private static final Term ff = TermFactory.DEFAULT.createTerm(Junctor.FALSE); 

    
    private TermBuilder() {
    }
    
    
        
    public TermFactory tf() {
        return tf;
    }
    
    
    //-------------------------------------------------------------------------
    //constructors for special classes of term operators
    //-------------------------------------------------------------------------
    
    public Term var(LogicVariable v) {
        return tf.createTerm(v);
    }
    
    
    public Term var(ProgramVariable v) { 
//	if(v.isMember()) {
//	    throw new TermCreationException(
//		    "Cannot create term for \"member\" "
//		    + "program variable \"" + v + "\". Use field symbols "
//		    + "like your mother told you!");
//	}
        return tf.createTerm(v);
    }
    
    
    public Term var(SchemaVariable v) {
	return tf.createTerm(v);
    }
    
    
    public Term var(ParsableVariable v) {
	return tf.createTerm(v);
    }

    
    public Term func(Function f) {
        return tf.createTerm(f);
    }
    
    
    public Term func(Function f, Term s) {
        return tf.createTerm(f, s);
    }
    
    
    public Term func(Function f, Term s1, Term s2) {
        return tf.createTerm(f, s1, s2);
    }
    
    
    public Term func(Function f, Term[] s) {
        return tf.createTerm(f, s, null, null);
    }
    
    public Term func(Function f, 
	    	     Term[] s, 
	    	     ArrayOfQuantifiableVariable boundVars) {
        return tf.createTerm(f, s, boundVars, null);
    }
    
    
    public Term mod(Modality mod, JavaBlock jb, Term t) {
	return tf.createTerm(mod, new Term[]{t}, null, jb);
    }
    
    
    public Term box(JavaBlock jb, Term t) {
        return mod(Modality.BOX, jb, t);
    }
    
    
    public Term dia(JavaBlock jb, Term t) {
        return mod(Modality.DIA, jb, t);
    }
    
    
    public Term ife(Term cond, Term _then, Term _else) {        
        return tf.createTerm(IfThenElse.IF_THEN_ELSE, 
        	             new Term[]{cond, _then, _else});
    }
    
    
    public Term cast(Services services, Sort s, Term t) {
	return tf.createTerm(s.getCastSymbol(services), t);
    }
    
    
    public Term tt() {
        return tt;
    }
    
    
    public Term ff() {
        return ff;
    }
    

    public Term all(QuantifiableVariable qv, Term t) {
        return tf.createTerm(Quantifier.ALL, 
    	                     new ArrayOfTerm(t), 
    	                     new ArrayOfQuantifiableVariable(qv), 
    	                     null);
    }
    
    
    public Term all(ArrayOfQuantifiableVariable qv, Term t2) {
	if(qv.size() == 0) {
	    throw new TermCreationException("Cannot quantify over 0 variables");
	}
        Term result = t2;
        for (int i = qv.size() - 1; i >= 0; i--) {
            result = all(qv.getQuantifiableVariable(i), result); 
        }
        return result;
    }    
    
    
    public Term all(QuantifiableVariable[] qv, Term t2) {
	return all(new ArrayOfQuantifiableVariable(qv), t2);
    }
    
    
    public Term ex(QuantifiableVariable qv, Term t) {
	return tf.createTerm(Quantifier.EX, 
			     new ArrayOfTerm(t),
			     new ArrayOfQuantifiableVariable(qv),
			     null);
    }
    
    
    public Term ex(ArrayOfQuantifiableVariable qv, Term t2) {
	if(qv.size() == 0) {
	    throw new TermCreationException("Cannot quantify over 0 variables");
	}	
        Term result = t2;
        for (int i = qv.size() - 1; i >= 0; i--) {
            result = ex(qv.getQuantifiableVariable(i), result); 
        }
        return result;
    }        
    
    
    public Term ex(QuantifiableVariable[] qv, Term t2) {
        return ex(new ArrayOfQuantifiableVariable(qv), t2);
    }
    
    
    public Term not(Term t) {
	if(t.op() == Junctor.TRUE) {
	    return ff();
	} else if(t.op() == Junctor.FALSE) {
	    return tt();
	} else if(t.op() == Junctor.NOT) {
	    return t.sub(0);
	} else {
	    return tf.createTerm(Junctor.NOT, t);
	}
    }
    
    
    public Term and(Term t1, Term t2) {
	if(t1.op() == Junctor.FALSE || t2.op() == Junctor.FALSE) {
	    return ff();
	} else if(t1.op() == Junctor.TRUE) {
	    return t2;
	} else if(t2.op() == Junctor.TRUE) {
	    return t1;
	} else {
	    return tf.createTerm(Junctor.AND, t1, t2);
	}
    }

    
    public Term and(Term[] subTerms) {
        Term result = tt();
        for(int i = 0; i < subTerms.length; i++) {
            result = and(result, subTerms[i]);
        }

        return result;
    }
    
    
    public Term and(ListOfTerm subTerms) {
	Term result = tt();
	for(Term sub : subTerms) {
	    result = and(result, sub);
	}
	return result;
    }
    
    
    public Term or(Term t1, Term t2) {
	if(t1.op() == Junctor.TRUE || t2.op() == Junctor.TRUE) {
	    return tt();
	} else if(t1.op() == Junctor.FALSE) {
	    return t2;
	} else if(t2.op() == Junctor.FALSE) {
	    return t1;
	} else {
	    return tf.createTerm(Junctor.OR, t1, t2);
	}
    }
    
    
    public Term or(Term[] subTerms) {
        Term result = ff();
        for(int i = 0; i < subTerms.length; i++) {
            result = or(result, subTerms[i]);
        }
        return result;
    }
    
    
    public Term or(ListOfTerm subTerms) {
	Term result = ff();
	for(Term sub : subTerms) {
	    result = or(result, sub);
	}
	return result;
    }

    
    public Term imp(Term t1, Term t2) {
	if(t1.op() == Junctor.FALSE || t2.op() == Junctor.TRUE) {
	    return tt();
	} else if(t1.op() == Junctor.TRUE) {
	    return t2;
	} else if(t2.op() == Junctor.FALSE) {
	    return not(t1);
	} else {
	    return tf.createTerm(Junctor.IMP, t1, t2);
	}
    }
    
    
    /** 
     * Creates a term with the correct equality symbol for
     * the sorts involved
     */
    public Term equals(Term t1, Term t2) {
	if(t1.sort() == Sort.FORMULA) {
            if(t1.op() == Junctor.TRUE) {
        	return t2;
            } else if(t2.op() == Junctor.TRUE) {
        	return t1;
            } else if(t1.op() == Junctor.FALSE) {
                return not(t2);
            } else if(t2.op() == Junctor.FALSE) {
                return not(t1);
            } else {
        	return tf.createTerm(Equality.EQV, t1, t2);
            }
	} else {
	    return tf.createTerm(Equality.EQUALS, t1, t2);
	} 
    }
    
    
    /** 
     * Creates a substitution term
     * @param substVar the QuantifiableVariable to be substituted
     * @param substTerm the Term that replaces substVar
     * @param origTerm the Term that is substituted
     */
    public Term subst(SubstOp op, 
	              QuantifiableVariable substVar, 
	              Term substTerm, 
	              Term origTerm) {
	return tf.createTerm(op, 
		             new ArrayOfTerm(new Term[]{substTerm, origTerm}), 
		             new ArrayOfQuantifiableVariable(substVar), 
		             null);
    }
    
    
    
    //-------------------------------------------------------------------------
    //updates    
    //-------------------------------------------------------------------------
    
    public Term elementary(Services services, 
	                   UpdateableOperator lhs, 
	                   Term rhs) {
	ElementaryUpdate eu = ElementaryUpdate.getInstance(lhs);
	
	//XXX, weird integers
	if(services.getTypeConverter().getIntegerLDT() != null) {
	    Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();	
	    if(!rhs.sort().extendsTrans(eu.argSort(0))
	        && eu.argSort(0).extendsTrans(intSort)
	        && rhs.sort().extendsTrans(intSort)) {
		rhs = cast(services, eu.argSort(0), rhs);
	    }
	}
	
	return tf.createTerm(eu, rhs);
    }
    
    
    public Term elementary(Services services, Term lhs, Term rhs) {
	HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	if(lhs.op() instanceof UpdateableOperator) {
	    assert lhs.arity() == 0 : "uh oh: " + lhs;
	    return elementary(services, (UpdateableOperator)lhs.op(), rhs);
	} else if(heapLDT.getSortOfSelect(lhs.op()) != null
		  && lhs.sub(0).op().equals(heapLDT.getHeap())) {
	    final Term heapTerm   = lhs.sub(0);
	    final Term objectTerm = lhs.sub(1);
	    final Term fieldTerm  = lhs.sub(2);
                
	    final Term fullRhs = store(services, 
               		               heapTerm, 
                		       objectTerm, 
                		       fieldTerm, 
                		       rhs);
	    return elementary(services, heapLDT.getHeap(), fullRhs);
	} else {
	    throw new TermCreationException("Not a legal lhs: " + lhs);
	}
    }    
    
    
    public Term skip() {
	return tf.createTerm(UpdateJunctor.SKIP);
    }
    
    
    public Term parallel(Term u1, Term u2) {
	if(u1.sort() != Sort.UPDATE) {
	    throw new TermCreationException("Not an update: " + u1);
	} else if(u2.sort() != Sort.UPDATE) {
	    throw new TermCreationException("Not an update: " + u2);
	}
	if(u1.op() == UpdateJunctor.SKIP) {
	    return u2;
	} else if(u2.op() == UpdateJunctor.SKIP) {
	    return u1;
	}
	return tf.createTerm(UpdateJunctor.PARALLEL_UPDATE, u1, u2);
    }
    
    
    public Term parallel(Term[] updates) {
	Term result = skip();
	for(int i = 0; i < updates.length; i++) {
	    result = parallel(result, updates[i]);
	}
	return result;
    }
    
    
    public Term parallel(ListOfTerm updates) {
	return parallel(updates.toArray());
    }
    
    
    public Term parallel(Services services, Term[] lhss, Term[] values) {
	if(lhss.length != values.length) {
	    throw new TermCreationException(
		    "Tried to create parallel update with " 
		    + lhss.length + " locs and " + values.length + " values");
	}
	Term[] updates = new Term[lhss.length];
	for(int i = 0; i < updates.length; i++) {
	    updates[i] = elementary(services, lhss[i], values[i]);
	}
	return parallel(updates);
    }
    
    
    public Term sequential(Term u1, Term u2) {
	return parallel(u1, apply(u1, u2));
    }
    
    
    public Term sequential(ListOfTerm updates) {
	if(updates.size() == 0) {
	    return skip();
	} else if(updates.size() == 1) {
	    return updates.head();
	} else {
	    return sequential(updates.head(), sequential(updates.tail()));
	}    
    }
    

    public Term apply(Term update, Term target) {
	if(update.sort() != Sort.UPDATE) {
	    throw new TermCreationException("Not an update: " + update);
	} else if(update.op() == UpdateJunctor.SKIP) {
	    return target;
	} else {
	    return tf.createTerm(UpdateApplication.UPDATE_APPLICATION,
		        	 update, 
		        	 target);
	}
    }
    
    
    public Term applyElementary(Services services,
	                        Term loc,
	                        Term value,
	                        Term target) {
	return apply(elementary(services, loc, value), target);
    }
    
    
    public Term applyParallel(Term[] updates, Term target) {
	return apply(parallel(updates), target);
    }
    
    
    public Term applyParallel(ListOfTerm updates, Term target) {	
	return apply(parallel(updates), target);
    }
    
    
    public Term applyParallel(Services services, 
	                      Term[] lhss, 
	                      Term[] values, 
	                      Term target) {
	return apply(parallel(services, lhss, values), target);
    }
    
    
    public Term applySequential(ListOfTerm updates, Term target) {
	if(updates.size() == 0) {
	    return target;
	} else {
	    return apply(updates.head(), 
		         applySequential(updates.tail(), target));
	}    	
    }    
    
    
    
    //-------------------------------------------------------------------------
    //boolean operators    
    //-------------------------------------------------------------------------
    
    public Term TRUE(Services services) {
        return services.getTypeConverter().getBooleanLDT().getTrueTerm();
    }
    
    
    public Term FALSE(Services services) {
        return services.getTypeConverter().getBooleanLDT().getFalseTerm();
    }
    
    
    
    //-------------------------------------------------------------------------
    //integer operators     
    //-------------------------------------------------------------------------
    
    public Term geq(Term t1, Term t2, Services services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return func(integerLDT.getGreaterOrEquals(), t1, t2);
    }
    
    
    public Term gt(Term t1, Term t2, Services services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return func(integerLDT.getGreaterThan(), t1, t2);
    }
    
    
    public Term lt(Term t1, Term t2, Services services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return func(integerLDT.getLessThan(), t1, t2);
    }    
    
    
    public Term leq(Term t1, Term t2, Services services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return func(integerLDT.getLessOrEquals(), t1, t2);
    }    
    
    
    public Term zero(Services services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return integerLDT.translateLiteral(new IntLiteral(0));        
    }

    
    public Term one(Services services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return integerLDT.translateLiteral(new IntLiteral(1));        
    }
    
    /**
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
    
    
    //-------------------------------------------------------------------------
    //pair operators    
    //-------------------------------------------------------------------------
    
    public Term pair(Services services, Term t1, Term t2) {
	return func(services.getTypeConverter().getPairLDT().getPair(), t1, t2);
    }
    
    
    public Term pairSingleton(Services services, Term t1, Term t2) {
	return singleton(services, pair(services, t1, t2));
    }
        
    
    public Term pairElementOf(Services services, Term t1, Term t2, Term s) {
	return elementOf(services, pair(services, t1, t2), s);
    }    
    
    
    
    //-------------------------------------------------------------------------
    //set operators    
    //-------------------------------------------------------------------------
    
    public Term empty(Services services) {
	return func(services.getTypeConverter().getSetLDT().getEmpty());
    }
    
    
    public Term singleton(Services services, Term e) {
	return func(services.getTypeConverter().getSetLDT().getSingleton(), e);
    }
    
    
    public Term union(Services services, Term s1, Term s2) {
	return func(services.getTypeConverter().getSetLDT().getUnion(), s1, s2);
    }
    
    
    public Term intersect(Services services, Term s1, Term s2) {
	return func(services.getTypeConverter().getSetLDT().getIntersect(), 
		    s1, 
		    s2);
    }
    
    
    public Term setMinus(Services services, Term s1, Term s2) {
	return func(services.getTypeConverter().getSetLDT().getSetMinus(), 
		    s1, 
		    s2);
    }
    
    
    public Term setComprehension(Services services, 
	                         QuantifiableVariable qv, 
	                         Term a, 
	                         Term s) {
	Function f 
		= services.getTypeConverter()
		          .getSetLDT()
		          .getSetComprehension();
	return tf.createTerm(f, new Term[]{a,s}, new ArrayOfQuantifiableVariable(qv), null);
    }
    
    
    public Term elementOf(Services services, Term e, Term s) {
	return func(services.getTypeConverter().getSetLDT().getElementOf(), 
		    e,
		    s);
    }
    
    
    public Term subset(Services services, Term s1, Term s2) {
	return func(services.getTypeConverter().getSetLDT().getSubset(), 
		    s1, 
		    s2);
    }
    
    
    public Term disjoint(Services services, Term s1, Term s2) {
	return func(services.getTypeConverter().getSetLDT().getDisjoint(), 
		    s1, 
		    s2);
    }
    
    
    
    //-------------------------------------------------------------------------
    //heap operators    
    //-------------------------------------------------------------------------
    
    public Term NULL(Services services) {
        return services.getJavaInfo().getNullTerm();
    }

    
    public Term heap(Services services) {
        return var(services.getTypeConverter().getHeapLDT().getHeap());
    }
    
    
    public Term wellFormedHeap(Services services) {
        return func(services.getTypeConverter().getHeapLDT().getWellFormed(), heap(services));
    }
    

    public Term inReachableState(Services services) {
        return wellFormedHeap(services);
    }

    
    public Term select(Services services, Sort asSort, Term h, Term o, Term f) {
	return func(services.getTypeConverter().getHeapLDT().getSelect(
		    asSort, 
		    services), 
		    new Term[]{h, o, f});
    }

    
    public Term dot(Services services, Sort asSort, Term o, Term f) {
        return select(services, asSort, heap(services), o, f);
    }

    
    public Term dot(Services services, Sort asSort, Term o, Function f) {
        return dot(services, asSort, o, func(f));
    }
    
    
    public Term dotLength(Services services, Term a) {
	return dot(services, 
		   services.getTypeConverter().getIntegerLDT().targetSort(), 
		   a, 
		   services.getTypeConverter().getHeapLDT().getLength());
    }
    
    
    public Term dotCreated(Services services, Term o) {
	return dot(services,
		   services.getTypeConverter().getBooleanLDT().targetSort(),
		   o,
		   services.getTypeConverter().getHeapLDT().getCreated());
    }

    
    public Term staticDot(Services services, Sort asSort, Term f) {
        return dot(services, asSort, NULL(services), f);
    }
    
    
    public Term staticDot(Services services, Sort asSort, Function f) {
	return staticDot(services, asSort, func(f));
    }
    
    
    public Term nextToCreate(Services services) {
	return staticDot(services, 
		         services.getTypeConverter()
		                 .getIntegerLDT()
		                 .targetSort(),
		         services.getTypeConverter()
		                 .getHeapLDT()
		                 .getNextToCreate());
    }
    
    
    public Term arr(Services services, Term idx) {
	return func(services.getTypeConverter().getHeapLDT().getArr(), idx);
    }
    

    public Term dotArr(Services services, Term ref, Term idx) {
        if (ref == null || idx == null) {
            throw new TermCreationException("Tried to build an array access "+
                    "term without providing an " +
                    (ref==null ? "array reference." : "index.") + 
                    "("+ref+"["+idx+"])");
        }   
                
        final Sort elementSort;
        if(ref.sort() instanceof ArraySort) {
            elementSort = ((ArraySort) ref.sort()).elementSort();
        } else {
            throw new TermCreationException("Tried to build an array access "+
                    "on an inacceptable sort: " + ref.sort().getClass() + "\n" +
                    "("+ref+"["+idx+"])");
        }
        
        return select(services, 
        	      elementSort, 
        	      heap(services), 
        	      ref, 
        	      arr(services, idx));
    }
    
    
    public Term store(Services services, Term h, Term o, Term f, Term v) {
        return func(services.getTypeConverter().getHeapLDT().getStore(), 
        	    new Term[]{h, o, f, v});
    }
    
    
    public Term changeHeapAtLocs(Services services, Term h1, Term s, Term h2) {
	return func(services.getTypeConverter().getHeapLDT()
		                               .getChangeHeapAtLocs(), 
		    new Term[]{h1, s, h2});
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
    
    
    public Term allLocs(Services services) {
	return func(services.getTypeConverter().getHeapLDT().allLocs());
    }
    
    
    public Term allFields(Services services, Term o) {
	return func(services.getTypeConverter().getHeapLDT().allFields(), o);
    }
    
    
    public Term locComprehension(Services services, 
	                         QuantifiableVariable qv, 
	                         Term o, 
	                         Term f) {
	return setComprehension(services, 
		                qv, 
		                pair(services, o, f), 
		                allLocs(services));
    }
    
    public Term guardedLocComprehension(Services services, 
	                         	QuantifiableVariable qv,
	                         	Term cond,
	                         	Term o, 
	                         	Term f) {
	return setComprehension(services, 
		                qv, 
		                ife(cond, pair(services, o, f), empty(services)),
		                allLocs(services));
    }    
}
