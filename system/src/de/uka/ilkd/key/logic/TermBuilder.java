// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import java.io.StringReader;
import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.BooleanLDT;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SubstOp;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.UpdateableOperator;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.OpReplacer;


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
    // build terms using the KeY parser
    //-------------------------------------------------------------------------

    /**
     * Parses the given string that represents the term (or formula) using the
     * service's namespaces.
     * 
     * @param s
     *            the String to parse
     * @param services
     *            the services to be used for parsing
     */
    public Term parseTerm(String s, Services services)
        throws ParserException
    {
	return parseTerm(s, services, services.getNamespaces());
    }

    /**
     * Parses the given string that represents the term (or formula) using the
     * provided namespaces.
     * 
     * @param s
     *            the String to parse
     * @param services
     *            the services to be used for parsing
     * @param namespaces
     *            the namespaces used for name lookup.
     */
    public Term parseTerm(String s, Services services, NamespaceSet namespaces)
        throws ParserException
    {
        AbbrevMap abbr = (services.getProof() == null)
                       ? null : services.getProof().abbreviations();
        Term term = new DefaultTermParser().parse(
           new StringReader(s), null, services, namespaces, abbr);
        return term;
    }
    
    //-------------------------------------------------------------------------
    //naming
    //-------------------------------------------------------------------------
    
    public String shortBaseName(Sort s) {
	String result = s.name().toString();
	int index = result.lastIndexOf(".");
	if(index == -1) {
	    result = result.charAt(0) + "";
	} else {
	    result = result.substring(index).charAt(1) + "";
	}
	return result.toLowerCase();
    }
    
    
    /**
     * Returns an available name constructed by affixing a counter to the passed
     * base name.
     */
    public String newName(Services services, String baseName) {
	final Name savedName = services.getNameRecorder().getProposal();
	if(savedName != null) {
	    return savedName.toString();
	}
	
        final NamespaceSet namespaces = services.getNamespaces();
            
        int i = 0;
        String result = baseName;
        while(namespaces.lookup(new Name(result)) != null) {
            result = baseName + "_" + i++;
        }
        
        services.getNameRecorder().addProposal(new Name(result));
        
        return result;
    }
    

    /**
     * Returns an available name constructed by affixing a counter to a self-
     * chosen base name for the passed sort.
     */
    public String newName(Services services, Sort sort) {
	return newName(services, shortBaseName(sort));
    }
    
    
    
    
    //-------------------------------------------------------------------------
    //common variable constructions
    //-------------------------------------------------------------------------
    
    /**
     * Creates a program variable for "self". Take care to register it
     * in the namespaces!
     */
    public LocationVariable selfVar(Services services, 
                                    KeYJavaType kjt,
                                    boolean makeNameUnique) {
	String name = "self";
	if(makeNameUnique) {
	    name = newName(services, name);
	}
	return new LocationVariable(new ProgramElementName(name), kjt);
    }    
    
    
    /**
     * Creates a program variable for "self". Take care to register it
     * in the namespaces!
     */
    public LocationVariable selfVar(Services services, 
                                    ProgramMethod pm,
                                    KeYJavaType kjt,
                                    boolean makeNameUnique) {
        if(pm.isStatic()) {
            return null;
        } else {
            return selfVar(services, kjt, makeNameUnique);
        }
    }

    
    /**
     * Creates program variables for the parameters. Take care to register them
     * in the namespaces!
     */
    public ImmutableList<ProgramVariable> paramVars(Services services, 
                                                    ObserverFunction obs,
                                                    boolean makeNamesUnique) {
        ImmutableList<ProgramVariable> result 
        	= ImmutableSLList.<ProgramVariable>nil(); 
        for(int i = 0, n = obs.getNumParams(); i < n; i++) {
            final KeYJavaType paramType = obs.getParamType(i);
            String name; 
            if(obs instanceof ProgramMethod) {
        	name = ((ProgramMethod)obs).getParameterDeclarationAt(i)
        	                           .getVariableSpecification()
        	                           .getName();
            } else {
        	name = paramType.getSort().name().toString().charAt(0) + "";
            }
            if(makeNamesUnique) {
        	name = newName(services, name);
            }
            final LocationVariable paramVar
            	= new LocationVariable(new ProgramElementName(name), paramType);
            result = result.append(paramVar);
        }        
        return result;
    }
    
    
    /**
     * Creates program variables for the parameters. Take care to register them
     * in the namespaces!
     */
    public ImmutableList<ProgramVariable> paramVars(Services services,
	    String postfix, ObserverFunction obs, boolean makeNamesUnique) {
	final ImmutableList<ProgramVariable> paramVars 
		= paramVars(services, obs, true);
	ImmutableList<ProgramVariable> result 
        	= ImmutableSLList.<ProgramVariable>nil();
        for(ProgramVariable paramVar : paramVars) {
            ProgramElementName pen 
                = new ProgramElementName(paramVar.name() + postfix);            
            LocationVariable formalParamVar
            	= new LocationVariable(pen, paramVar.getKeYJavaType());
            result = result.append(formalParamVar);
        }
        return result;
    }
    
    
    /**
     * Creates a program variable for the result. Take care to register it
     * in the namespaces.
     */
    public LocationVariable resultVar(Services services, 
                                      ProgramMethod pm,
                                      boolean makeNameUnique) {
	return resultVar(services, "result", pm, makeNameUnique);
    }
    
    
    /**
     * Creates a program variable for the result with passed name. Take care to
     * register it in the namespaces.
     */
    public LocationVariable resultVar(Services services, String name,
	    ProgramMethod pm, boolean makeNameUnique) {
	if(pm.getKeYJavaType() == null || pm.isConstructor()) {
	    return null;
	} else {
	    if(makeNameUnique) {
		name = newName(services, name);
	    }
	    return new LocationVariable(new ProgramElementName(name),
				    	pm.getKeYJavaType());
	}
    }
    
    
    /**
     * Creates a program variable for the thrown exception. Take care to 
     * register it in the namespaces.
     */
    public LocationVariable excVar(Services services, 
                                   ProgramMethod pm,
                                   boolean makeNameUnique) {
	return excVar(services, "exc", pm, makeNameUnique);
    }
    
    
    /**
     * Creates a program variable for the thrown exception. Take care to 
     * register it in the namespaces.
     */
    public LocationVariable excVar(Services services,
	    			   String name,
                                   ProgramMethod pm,
                                   boolean makeNameUnique) {
	if(makeNameUnique) {
	    name = newName(services, name);
	}	
        return new LocationVariable(new ProgramElementName(name),
                                    services.getJavaInfo().getTypeByClassName(
                                                   "java.lang.Exception"));
    }
    
    
    /**
     * Creates a program variable for the atPre heap. Take care to register it
     * in the namespaces.
     */
    public LocationVariable heapAtPreVar(Services services,
	    				 String baseName,
	    			         boolean makeNameUnique) {
	if(makeNameUnique) {
	    baseName = newName(services, baseName);
	}	
	return new LocationVariable(new ProgramElementName(baseName),
		            	    new KeYJavaType(services.getTypeConverter()
		            	            		    .getHeapLDT()
		            	            		    .targetSort()));
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
    
    
    public ImmutableList<Term> var(ProgramVariable ... vs) {
	return var(vs);
    }
    
    
    public ImmutableList<Term> var(Iterable<ProgramVariable> vs) {
	ImmutableList<Term> result = ImmutableSLList.<Term>nil();
	for (ProgramVariable v : vs) {
	    result = result.append(var(v));
	}
        return result;
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
    
    
    public Term func(Function f, Term ... s) {
        return tf.createTerm(f, s, null, null);
    }
    
    public Term func(Function f, 
	    	     Term[] s, 
	    	     ImmutableArray<QuantifiableVariable> boundVars) {
        return tf.createTerm(f, s, boundVars, null);
    }
    
    
    public Term prog(Modality mod, JavaBlock jb, Term t) {
	return tf.createTerm(mod, new Term[]{t}, null, jb);
    }
    
    
    public Term box(JavaBlock jb, Term t) {
        return prog(Modality.BOX, jb, t);
    }
    
    
    public Term dia(JavaBlock jb, Term t) {
        return prog(Modality.DIA, jb, t);
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
    	                     new ImmutableArray<Term>(t), 
    	                     new ImmutableArray<QuantifiableVariable>(qv), 
    	                     null);
    }


    public Term all(Iterable<QuantifiableVariable> qvs, Term t) {
        Term result = t;
        for (QuantifiableVariable fv : qvs) {
            result = all(fv, result);
        }
        return result;
    }


    public Term allClose(Term t) {
	return all(t.freeVars(), t);
    }


    public Term ex(QuantifiableVariable qv, Term t) {
	return tf.createTerm(Quantifier.EX, 
			     new ImmutableArray<Term>(t),
			     new ImmutableArray<QuantifiableVariable>(qv),
			     null);
    }


    public Term ex(Iterable<QuantifiableVariable> qvs, Term t) {
        Term result = t;
        for (QuantifiableVariable fv : qvs) {
            result = ex(fv, result);
        }
        return result;
    }


    public Term bsum(QuantifiableVariable qv,
                     Term a,
                     Term b,
                     Term t,
                     Services services) {
        Function bsum = services.getTypeConverter().getIntegerLDT().getBsum();
        return func(bsum,
                    new Term[]{a, b, t},
                    new ImmutableArray<QuantifiableVariable>(qv));
    }


//    public Term min(QuantifiableVariable qv, Term t, Services services) {
//        Quantifier q =
//                (Quantifier)services.getNamespaces().functions().lookup(
//                    Quantifier.MIN_NAME);
//        return tf.createTerm(q,
//    	                     new ImmutableArray<Term>(t),
//    	                     new ImmutableArray<QuantifiableVariable>(qv),
//    	                     null);
//    }
//
//
//    public Term max(QuantifiableVariable qv, Term t, Services services) {
//        Quantifier q =
//                (Quantifier)services.getNamespaces().functions().lookup(
//                    Quantifier.MAX_NAME);
//        return tf.createTerm(q,
//    	                     new ImmutableArray<Term>(t),
//    	                     new ImmutableArray<QuantifiableVariable>(qv),
//    	                     null);
//    }

    
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

    
    public Term and(Term ... subTerms) {
        Term result = tt();
        for(Term sub : subTerms) {
	    result = and(result, sub);
	}
        return result;
    }
    
    
    public Term and(ImmutableList<Term> subTerms) {
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
    
    
    public Term or(Term... subTerms) {
        Term result = ff();
        for(Term sub : subTerms) {
            result = or(result, sub);
        }
        return result;
    }


    public Term or(Iterable<Term> subTerms) {
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
		             new ImmutableArray<Term>(new Term[]{substTerm, origTerm}), 
		             new ImmutableArray<QuantifiableVariable>(substVar), 
		             null);
    }
    
    
    public Term instance(Services services, Sort s, Term t) {
	return equals(func(s.getInstanceofSymbol(services), t),
		      TRUE(services));
    }
    
    
    public Term exactInstance(Services services, Sort s, Term t) {
	return equals(func(s.getExactInstanceofSymbol(services), t), 
		      TRUE(services));
    }


    /**
     * If a is a boolean literal, the method returns the literal as a Formula.
     */
    public Term convertToFormula(Term a, Services services) {
        BooleanLDT booleanLDT = services.getTypeConverter().getBooleanLDT();
	if(a.sort() == booleanLDT.targetSort()) {
	    return equals(a, TRUE(services));
	}

	return a;
    }
    
    
    
    //-------------------------------------------------------------------------
    //updates    
    //-------------------------------------------------------------------------
    
    public Term elementary(Services services, 
	                   UpdateableOperator lhs, 
	                   Term rhs) {
	ElementaryUpdate eu = ElementaryUpdate.getInstance(lhs);	
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


    public Term elementary(Services services, Term heapTerm) {
        return elementary(services, heap(services), heapTerm);
    }


    public Term elementary(Services services, LocationVariable heap) {
        return elementary(services, var(heap));
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
    
    
    public Term parallel(ImmutableList<Term> updates) {
	return parallel(updates.toArray(new Term[updates.size()]));
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
    
    
    public Term sequential(Term[] updates) {
	if(updates.length == 0) {
	    return skip();
	} else {
	    Term result = updates[updates.length - 1];
	    for(int i = updates.length - 2; i >= 0; i++) {
		result = sequential(updates[i], result);
	    }
	    return result;
	}
    }
    
    
    public Term sequential(ImmutableList<Term> updates) {
	if(updates.isEmpty()) {
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
	} else if(target.equals(tt())) {
            return tt();
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
    
    
    public Term applyParallel(ImmutableList<Term> updates, Term target) {	
	return apply(parallel(updates), target);
    }
    
    
    public Term applyParallel(Services services, 
	                      Term[] lhss, 
	                      Term[] values, 
	                      Term target) {
	return apply(parallel(services, lhss, values), target);
    }
    
    
    public Term applySequential(Term[] updates, Term target) {
	if(updates.length == 0) {
	    return target;
	} else {
	    ImmutableList<Term> updateList = ImmutableSLList.<Term>nil()
	                                        .append(updates)
	                                        .tail();
	    return apply(updates[0],
		         applySequential(updateList, target));
	}    	
    }    
    
    
    public Term applySequential(ImmutableList<Term> updates, Term target) {
	if(updates.isEmpty()) {
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
	return services.getTypeConverter().getIntegerLDT().zero();
    }

    
    public Term one(Services services) {
        return services.getTypeConverter().getIntegerLDT().one();
    }

    
    /**
     * @param services Services which contains the number-functions
     * @param numberString String representing an integer
     * @return Term in Z-Notation representing the given number
     */
    public Term zTerm(Services services, String numberString) {
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
    
    
    public Term add(Services services, Term t1, Term t2) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        final Term zero = integerLDT.zero();
        if(t1.equals(zero)) {
            return t2;
        } else if(t2.equals(zero)) {
            return t1;
        } else {
            return func(integerLDT.getAdd(), t1, t2);
        }
    }


    public Term inInt(Term var,
                      Services services) {
        Function f =
                (Function) services.getNamespaces().functions().lookup(
                new Name("inInt"));
        return func(f, var);
    }

    
    
    //-------------------------------------------------------------------------
    //location set operators    
    //-------------------------------------------------------------------------
    
    public Term empty(Services services) {
	return func(services.getTypeConverter().getLocSetLDT().getEmpty());
    }
    
    
    public Term allLocs(Services services) {
	return func(services.getTypeConverter().getLocSetLDT().getAllLocs());
    }    
    
    
    public Term singleton(Services services, Term o, Term f) {
	return func(services.getTypeConverter().getLocSetLDT().getSingleton(), 
		    o, 
		    f);
    }
    
    
    public Term union(Services services, Term s1, Term s2) {
	final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
	if(s1.op() == ldt.getEmpty()) {
	    return s2;
	} else if(s2.op() == ldt.getEmpty()) {
	    return s1;
	} else {
	    return func(ldt.getUnion(), s1, s2);
	}
    }
    
    
    public Term intersect(Services services, Term s1, Term s2) {
	final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
	if(s1.op() == ldt.getEmpty() || s2.op() == ldt.getEmpty()) {
	    return empty(services);
	} else {
	    return func(ldt.getIntersect(), s1, s2);
	}
    }
    
    
    public Term setMinus(Services services, Term s1, Term s2) {
	final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
	if(s1.op() == ldt.getEmpty() || s2.op() == ldt.getEmpty()) {
	    return s1;
	} else {
	    return func(ldt.getSetMinus(), s1, s2);
	}
    }
    
    
    public Term infiniteUnion(Services services, 
	                      QuantifiableVariable[] qvs, 
	                      Term s) {
	final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
	return tf.createTerm(ldt.getInfiniteUnion(), 
		             new Term[]{s}, 
		             new ImmutableArray<QuantifiableVariable>(qvs), 
		             null);
    }
    
    
    public Term guardedInfiniteUnion(Services services, 
	    			     QuantifiableVariable[] qvs, 
	    			     Term guard, 
	    			     Term s) {
	return infiniteUnion(services, 
		             qvs, 
		             ife(guard, s, empty(services)));
    }
    
    
    public Term setComprehension(Services services, 
	                         QuantifiableVariable[] qvs, 
	                         Term o, 
	                         Term f) {
	return infiniteUnion(services, qvs, singleton(services, o, f));
    }
    
    
    public Term guardedSetComprehension(Services services, 
	                         	QuantifiableVariable[] qvs,
	                         	Term guard,
	                         	Term o,
	                         	Term f) {
	return guardedInfiniteUnion(services, 
		                    qvs, 
		                    guard, 
		                    singleton(services, o, f));
    }
    
    
    public Term allFields(Services services, Term o) {
	return func(services.getTypeConverter().getLocSetLDT().getAllFields(), o);
    }
    
    
    public Term allObjects(Services services, Term f) {
	return func(services.getTypeConverter().getLocSetLDT().getAllObjects(), f);
    }
    
    
    public Term arrayRange(Services services, Term o, Term lower, Term upper) {
	return func(services.getTypeConverter().getLocSetLDT().getArrayRange(), 
		    new Term[]{o, lower, upper});
    }        
    
    
    public Term freshLocs(Services services, Term h) {
	return func(services.getTypeConverter().getLocSetLDT().getFreshLocs(), h);
    }    
    
    
    public Term elementOf(Services services, Term o, Term f, Term s) {
	final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
	if(s.op() == ldt.getEmpty()) {
	    return ff();
	} else {
	    return func(ldt.getElementOf(), new Term[]{o, f, s});
	}
    }
    
    
    public Term subset(Services services, Term s1, Term s2) {
	final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
	if(s1.op() == ldt.getEmpty()) {
	    return tt();
	} else {
	    return func(ldt.getSubset(), s1, s2);
	}
    }
    
    
    public Term disjoint(Services services, Term s1, Term s2) {
	final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
	if(s1.op() == ldt.getEmpty() || s2.op() == ldt.getEmpty()) {
	    return tt();
	} else {
	    return func(ldt.getDisjoint(), s1, s2);
	}
    }
    
    
    public Term createdInHeap(Services services, Term s, Term h) {
	final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
	if(s.op() == ldt.getEmpty()) {
	    return tt();
	} else {
	    return func(ldt.getCreatedInHeap(), s, h);
	}
    }    
    
    
    public Term createdLocs(Services services) {
        return setMinus(services, 
        	        allLocs(services), 
                        freshLocs(services, heap(services))); 
    }    
    
    
    
    //-------------------------------------------------------------------------
    //heap operators    
    //-------------------------------------------------------------------------
    
    public Term NULL(Services services) {
        return func(services.getTypeConverter().getHeapLDT().getNull());
    }

    
    public Term heap(Services services) {
        return var(services.getTypeConverter().getHeapLDT().getHeap());
    }

    public Term savedHeap(Services services) {
        return var(services.getTypeConverter().getHeapLDT().getSavedHeap());
    }
    
    
    public Term wellFormed(Services services, Term h) {
        return func(services.getTypeConverter().getHeapLDT().getWellFormed(), 
        	    h);
    }
    

    public Term wellFormedHeap(Services services) {
        return wellFormed(services, heap(services));
    }
    
    
    public Term inv(Services services, Term h, Term o) {
	return func(services.getJavaInfo().getInv(),
		    h,
		    o);
    }    
    
    
    public Term inv(Services services, Term o) {
	return inv(services, heap(services),  o);
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
	final Sort fieldSort 
		= services.getTypeConverter().getHeapLDT().getFieldSort();
        return f.sort() == fieldSort
               ? dot(services, asSort, o, func(f))
               : func(f, heap(services), o);
    }
    

    public Term staticDot(Services services, Sort asSort, Term f) {
        return dot(services, asSort, NULL(services), f);
    }
    
    
    public Term staticDot(Services services, Sort asSort, Function f) {
	final Sort fieldSort 
		= services.getTypeConverter().getHeapLDT().getFieldSort();
	return f.sort() == fieldSort
	       ? staticDot(services, asSort, func(f))
	       : func(f, heap(services));
    }
    

    public Term arr(Services services, Term idx) {
	return func(services.getTypeConverter().getHeapLDT().getArr(), idx);
    }
    

    public Term dotArr(Services services, Term ref, Term idx) {
        if(ref == null || idx == null) {
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
    
    
    public Term dotLength(Services services, Term a) {
	final TypeConverter tc = services.getTypeConverter();
	return func(tc.getHeapLDT().getLength(), a); 
    }
    
    
    public Term created(Services services, Term h, Term o) {
	final TypeConverter tc = services.getTypeConverter();	
	return equals(select(services,
		              tc.getBooleanLDT().targetSort(),
			      h,
		              o,
		              func(tc.getHeapLDT().getCreated())),
		       TRUE(services));
    }


    public Term created(Services services, Term o) {
	return created(services, heap(services), o);
    }

    
    
    public Term initialized(Services services, Term o) {
	final TypeConverter tc = services.getTypeConverter();	
	return equals(dot(services,
		          tc.getBooleanLDT().targetSort(),
		          o,
		          tc.getHeapLDT().getInitialized()),
		      TRUE(services));
    }

    
    public Term classPrepared(Services services, Sort classSort) {
	final TypeConverter tc = services.getTypeConverter();	
	return equals(staticDot(services,
		                tc.getBooleanLDT().targetSort(),
		                tc.getHeapLDT().getClassPrepared(classSort, 
		                				 services)),
		      TRUE(services));	
    }
    
    public Term classInitialized(Services services, Sort classSort) {
	final TypeConverter tc = services.getTypeConverter();	
	return equals(staticDot(services,
		                tc.getBooleanLDT().targetSort(),
		                tc.getHeapLDT().getClassInitialized(classSort, 
		        				            services)),
		      TRUE(services));
    }

    public Term classInitializationInProgress(Services services, 
	    				      Sort classSort) {
	final TypeConverter tc = services.getTypeConverter();	
	return equals(staticDot(services,
		                tc.getBooleanLDT().targetSort(),
		                tc.getHeapLDT()
		                  .getClassInitializationInProgress(classSort, 
		        	   			            services)),
		      TRUE(services));
    }

        
    public Term classErroneous(Services services, Sort classSort) {
	final TypeConverter tc = services.getTypeConverter();	
	return equals(staticDot(services,
		                tc.getBooleanLDT().targetSort(),
		                tc.getHeapLDT().getClassErroneous(classSort, 
		        	 			          services)),
		      TRUE(services));
    }

    
    public Term store(Services services, Term h, Term o, Term f, Term v) {
        return func(services.getTypeConverter().getHeapLDT().getStore(), 
        	    new Term[]{h, o, f, v});
    }


    public Term create(Services services, Term h, Term o) {
        return func(services.getTypeConverter().getHeapLDT().getCreate(), 
        	     new Term[]{h, o});
    }

    
    public Term anon(Services services, Term h1, Term s, Term h2) {
	return func(services.getTypeConverter().getHeapLDT().getAnon(), 
		    new Term[]{h1, s, h2});
    }
    
               
    public Term fieldStore(Services services, Term o, Function f, Term v) {
        return store(services, heap(services), o, func(f), v);
    }
    
    
    public Term staticFieldStore(Services services, Function f, Term v) {
	return fieldStore(services, NULL(services), f, v);
    }
    
    
    public Term arrayStore(Services services, Term o, Term i, Term v) {
        return store(services, 
        	     heap(services), 
        	     o, 
        	     func(services.getTypeConverter().getHeapLDT().getArr(), i),
        	     v);
    }        
    
    
    public Term reachableValue(Services services, 
	    		       Term h, 
	    		       Term t, 
	    		       KeYJavaType kjt) {
	assert t.sort().extendsTrans(kjt.getSort()) 
	       || t.sort() instanceof ProgramSVSort;
	final Sort s = t.sort() instanceof ProgramSVSort ? kjt.getSort() : t.sort();
	final IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();
	final LocSetLDT setLDT = services.getTypeConverter().getLocSetLDT();
	if(s.extendsTrans(services.getJavaInfo().objectSort())) {
	    return or(created(services, h, t), equals(t, NULL(services)));
	} else if(s.equals(setLDT.targetSort())) {
	    return createdInHeap(services, t, h);
	} else if(s.equals(intLDT.targetSort())) {
	    return func(intLDT.getInBounds(kjt.getJavaType()), t);
	} else {
	    return tt();
	}
    }


    public Term reachableValue(Services services, Term t, KeYJavaType kjt) {
	return reachableValue(services, heap(services), t, kjt);
    }
    
    
    public Term reachableValue(Services services, ProgramVariable pv) {
	return reachableValue(services, var(pv), pv.getKeYJavaType());
    }
    
    
    public Term frame(Services services, Term heapTerm,
	    	      Map<Term,Term> normalToAtPre, 
	    	      Term mod) {
	final Sort objectSort = services.getJavaInfo().objectSort();
	final Sort fieldSort = services.getTypeConverter()
	                               .getHeapLDT()
	                               .getFieldSort();
	
	final Name objVarName   = new Name(newName(services, "o"));
	final Name fieldVarName = new Name(newName(services, "f"));
	final LogicVariable objVar   
		= new LogicVariable(objVarName, objectSort);
	final LogicVariable fieldVar 
		= new LogicVariable(fieldVarName, fieldSort);
	final Term objVarTerm = var(objVar);
	final Term fieldVarTerm = var(fieldVar);
	
	final OpReplacer or = new OpReplacer(normalToAtPre);
	final Term modAtPre = or.replace(mod);
	final Term createdAtPre = or.replace(created(services, objVarTerm));

        ImmutableList<QuantifiableVariable> quantVars =
                ImmutableSLList.<QuantifiableVariable>nil();
        quantVars = quantVars.append(objVar);
        quantVars = quantVars.append(fieldVar);
	return all(quantVars,
		   or(elementOf(services,
                                objVarTerm,
                                fieldVarTerm,
                                modAtPre),
                      and(not(equals(objVarTerm, NULL(services))),
                      not(createdAtPre)),
                      equals(select(services,
                                    Sort.ANY,
                                    heapTerm,
                                    objVarTerm,
                                    fieldVarTerm),
                             select(services,
                                    Sort.ANY,
                                    or.replace(heapTerm),
                                    objVarTerm,
                                    fieldVarTerm))));
    }
    
    
    public Term anonUpd(Services services, Term mod, Term anonHeap, boolean savedHeap) {
	return elementary(services,
		          savedHeap ? services.getTypeConverter().getHeapLDT().getSavedHeap()
		                    : services.getTypeConverter().getHeapLDT().getHeap(),
		          anon(services, 
		               savedHeap ? savedHeap(services) : heap(services), 
		               mod, 
		               anonHeap));
    }
    
        
    public Term forallHeaps(Services services, Term t) {
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final LogicVariable heapLV 
		= new LogicVariable(new Name("h"), heapLDT.targetSort());
	final Map<LocationVariable, LogicVariable> map
		= new HashMap<LocationVariable, LogicVariable>();
	map.put(heapLDT.getHeap(), heapLV);
	final OpReplacer or = new OpReplacer(map);
	t = or.replace(t);
	return all(heapLV, t);
    }
    
    
    
    //-------------------------------------------------------------------------
    //reachability operators    
    //-------------------------------------------------------------------------
    
    public Term acc(Services services, Term h, Term s, Term o1, Term o2) {
	return func(services.getTypeConverter().getHeapLDT().getAcc(), 
		    new Term[]{h, s, o1, o2});
    }
    
    
    public Term reach(Services services, 
	    	      Term h, 
	    	      Term s, 
	    	      Term o1, 
	    	      Term o2, 
	    	      Term n) {
	return func(services.getTypeConverter().getHeapLDT().getReach(), 
		    new Term[]{h, s, o1, o2, n});
    }    
    
    
    //-------------------------------------------------------------------------
    //sequence operators    
    //-------------------------------------------------------------------------
    
    public Term seqGet(Services services, Sort asSort, Term s, Term idx) {
	return func(services.getTypeConverter().getSeqLDT().getSeqGet(asSort, 
		    						      services), 
		    s,
		    idx);
    }
    
    
    public Term seqLen(Services services, Term s) {
	return func(services.getTypeConverter().getSeqLDT().getSeqLen(), s);
    }
    
    /** Function representing the least index of an element x in a sequence s (or underspecified) */
    public Term indexOf(Services services, Term s, Term x){
	return func(services.getTypeConverter().getSeqLDT().getSeqIndexOf(),s,x);
    }
    
    
    public Term seqEmpty(Services services) {
	return func(services.getTypeConverter().getSeqLDT().getSeqEmpty());
    }
    
    
    public Term seqSingleton(Services services, Term x) {
	return func(services.getTypeConverter().getSeqLDT().getSeqSingleton(), 
		    x);
    }
    
    
    public Term seqConcat(Services services, Term s, Term s2) {
	return func(services.getTypeConverter().getSeqLDT().getSeqConcat(), 
		    s, 
		    s2);
    }
    
    
    public Term seqSub(Services services, Term s, Term from, Term to) {
	return func(services.getTypeConverter().getSeqLDT().getSeqSub(), 
		    new Term[]{s, from, to});
    }
    
    
    public Term seqReverse(Services services, Term s) {
	return func(services.getTypeConverter().getSeqLDT().getSeqReverse(), s);
    }    
}
