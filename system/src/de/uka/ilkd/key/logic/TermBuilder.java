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

package de.uka.ilkd.key.logic;


import java.io.StringReader;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.ldt.BooleanLDT;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IfExThenElse;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SubstOp;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.UpdateableOperator;
import de.uka.ilkd.key.logic.op.WarySubstOp;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.inst.SVInstantiations.UpdateLabelPair;
import de.uka.ilkd.key.util.Pair;


/**
 * <p>Use this class if you intend to build complex terms by hand. It is
 * more convenient than the @link{TermFactory} class.</p>
 *
 * <p>Attention: some methods of this class try to simplify some terms. So if you
 * want to be sure that the term looks exactly as you built it, you
 * will have to use the TermFactory.</p>
 */
public class TermBuilder {

    public static final TermBuilder DF = new TermBuilder();

    private static final TermFactory tf = TermFactory.DEFAULT;
    private static final Term tt = TermFactory.DEFAULT.createTerm(Junctor.TRUE);
    private static final Term ff = TermFactory.DEFAULT.createTerm(Junctor.FALSE);

    public TermBuilder() {
    }


    public TermFactory tf() {
        return tf;
    }


    //-------------------------------------------------------------------------
    // build terms using the KeY parser
    //-------------------------------------------------------------------------

    /**
     * Parses the given string that represents the term (or createTerm) using the
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
     * Parses the given string that represents the term (or createTerm) using the
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
                                    IProgramMethod pm,
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
                                                    IObserverFunction obs,
                                                    boolean makeNamesUnique) {
        ImmutableList<ProgramVariable> result
            = ImmutableSLList.<ProgramVariable>nil();
        for(int i = 0, n = obs.getNumParams(); i < n; i++) {
            final KeYJavaType paramType = obs.getParamType(i);
            String name;
            if(obs instanceof IProgramMethod) {
            name = ((IProgramMethod)obs).getParameterDeclarationAt(i)
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
        String postfix, IObserverFunction obs, boolean makeNamesUnique) {
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
                                      IProgramMethod pm,
                                      boolean makeNameUnique) {
    return resultVar(services, "result", pm, makeNameUnique);
    }


    /**
     * Creates a program variable for the result with passed name. Take care to
     * register it in the namespaces.
     */
    public LocationVariable resultVar(Services services, String name,
        IProgramMethod pm, boolean makeNameUnique) {
    if(pm.isVoid() || pm.isConstructor()) {
        return null;
    } else {
        if(makeNameUnique) {
        name = newName(services, name);
        }
        return new LocationVariable(new ProgramElementName(name),
                        pm.getReturnType());
    }
    }


    /**
     * Creates a program variable for the thrown exception. Take care to
     * register it in the namespaces.
     */
    public LocationVariable excVar(Services services,
                                   IProgramMethod pm,
                                   boolean makeNameUnique) {
    return excVar(services, "exc", pm, makeNameUnique);
    }


    /**
     * Creates a program variable for the thrown exception. Take care to
     * register it in the namespaces.
     */
    public LocationVariable excVar(Services services,
                       String name,
                                   IProgramMethod pm,
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
                                         Sort sort,
                             boolean makeNameUnique) {
        assert sort != null;
    if(makeNameUnique) {
        baseName = newName(services, baseName);
    }
    return new LocationVariable(new ProgramElementName(baseName),
                            new KeYJavaType(sort));
    }

    //-------------------------------------------------------------------------
    //constructors for special classes of term operators
    //-------------------------------------------------------------------------

    public Term var(LogicVariable v) {
        return tf.createTerm(v);
    }


    public Term var(ProgramVariable v) {
//  if(v.isMember()) {
//      throw new TermCreationException(
//          "Cannot create term for \"member\" "
//          + "program variable \"" + v + "\". Use field symbols "
//          + "like your mother told you!");
//  }
        return tf.createTerm(v);
    }


    public ImmutableList<Term> var(ProgramVariable ... vs) {
        ImmutableList<Term> result = ImmutableSLList.<Term>nil();
        for (ProgramVariable v : vs) {
            result = result.append(var(v));
        }
        return result;
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

    public Term func(IObserverFunction f, Term ... s) {
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


    public Term prog(Modality mod, JavaBlock jb, Term t, ImmutableArray<ITermLabel> labels) {
    return tf.createTerm(mod, new Term[]{t}, null, jb, labels);
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
    
    /** Construct a term with the \ifEx operator. */
    public Term ifEx(QuantifiableVariable qv, Term cond, Term _then, Term _else) {
        return tf.createTerm(IfExThenElse.IF_EX_THEN_ELSE,
                            new ImmutableArray<Term>(cond,_then,_else),
                            new ImmutableArray<QuantifiableVariable>(qv),
                            null);
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

    /**
     * Removes universal quantifiers from a formula.
     */
    public Term open(Term formula) {
    assert formula.sort() == Sort.FORMULA;
    if(formula.op() == Quantifier.ALL) {
        return open(formula.sub(0));
    } else {
        return formula;
    }
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



    /** Constructs a bounded product comprehension expression. */
    public Term bprod(QuantifiableVariable qv,
                     Term a,
                     Term b,
                     Term t,
                     Services services) {
        Function bprod = services.getTypeConverter().getIntegerLDT().getBprod();
        return func(bprod,
                    new Term[]{a, b, t},
                    new ImmutableArray<QuantifiableVariable>(qv));
    }


    /** Translation of JML's \min operator using \ifEx operator. */
    public Term min(QuantifiableVariable qv, Term guard, Term t, boolean bigInt, Services services) {
        final Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();
        final QuantifiableVariable x = new LogicVariable(new Name("x"),intSort);
        final Term xvar = var(x);
        final Term subst = subst(qv, xvar, guard);
        final Term lhs = bigInt? subst: and(inInt(xvar,services),subst);
        final Term qvar = var(qv);
        if (!bigInt) guard = and(inInt(qvar,services),guard);
        final Term minForm = and(guard,all(x,imp(lhs,leq(qvar,xvar, services))));
        final Term undef = func(new Function(new Name("undefMin"), intSort));
        return ifEx(qv, minForm, t, undef);
    }


    /** Translation of JML's \max operator using \ifEx operator. */
    public Term max(QuantifiableVariable qv, Term guard, Term t, boolean bigInt, Services services) {
        final Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();
        final QuantifiableVariable x = new LogicVariable(new Name("x"),intSort);
        final Term xvar = var(x);
        final Term subst = subst(qv, xvar, guard);
        final Term lhs = bigInt? subst: and(inInt(xvar,services),subst);
        final Term qvar = var(qv);
        if (!bigInt) guard = and(inInt(qvar,services),guard);
        final Term maxForm = and(guard,all(x,imp(lhs,geq(qvar,xvar, services))));
        final Term undef = func(new Function(new Name("undefMax"), intSort));
        return ifEx(qv, maxForm, t, undef);
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


    public Term and(Term ... subTerms) {
        Term result = tt();
        for(Term sub : subTerms) {
        result = and(result, sub);
    }
        return result;
    }


    public Term and(Iterable<Term> subTerms) {
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
       return imp(t1, t2, null);
    }


    public Term imp(Term t1, Term t2, ImmutableArray<ITermLabel> labels) {
    if(t1.op() == Junctor.FALSE || t2.op() == Junctor.TRUE) {
        return tt();
    } else if(t1.op() == Junctor.TRUE) {
        return t2;
    } else if(t2.op() == Junctor.FALSE) {
        return not(t1);
    } else {
        return tf.createTerm(Junctor.IMP, t1, t2, labels);
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

    public Term subst(QuantifiableVariable substVar,
                  Term substTerm,
                  Term origTerm) {
    return tf.createTerm(WarySubstOp.SUBST,
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
        if (a.sort() == Sort.FORMULA) {
            return a;
        } else if (a.sort() == booleanLDT.targetSort()) {
            // special case where a is the result of convertToBoolean
            if (a.op() == IfThenElse.IF_THEN_ELSE) {
                assert a.subs().size() == 3;
                assert a.sub(0).sort() == Sort.FORMULA;
                if (a.sub(1) == booleanLDT.getTrueTerm() && a.sub(2) == booleanLDT.getFalseTerm())
                    return a.sub(0);
                else if (a.sub(1) == booleanLDT.getFalseTerm() && a.sub(2) == booleanLDT.getTrueTerm())
                    return not(a.sub(0));
            }
            return equals(a, TRUE(services));
        } else {
            throw new TermCreationException("Term " + a + " cannot be converted"
                                            + " into a formula.");
        }
    }

    /** For a formula a, convert it to a boolean expression. */
    public Term convertToBoolean(Term a, Services services){
        BooleanLDT booleanLDT = services.getTypeConverter().getBooleanLDT();
        if (a.sort() == booleanLDT.targetSort()) {
            return a;
        } else if (a.sort() == Sort.FORMULA) {
            // special case where a is the result of convertToFormula
            if (a.op() == Equality.EQUALS && a.sub(1) == booleanLDT.getTrueTerm() ) {
                return a.sub(0);
            }
            return ife(a, TRUE(services), FALSE(services));
        } else {
            throw new TermCreationException("Term " + a + " cannot be converted"
                    + " into a boolean.");
}
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
        return elementary(services, getBaseHeap(services), heapTerm);
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


    public Term parallel(Term... updates) {
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


    public Term parallel(Services services,
                         Iterable<Term> lhss,
                         Iterable<Term> values) {
        ImmutableList<Term> updates = ImmutableSLList.<Term>nil();
        Iterator<Term> lhssIt = lhss.iterator();
        Iterator<Term> rhssIt = values.iterator();
        while (lhssIt.hasNext()) {
            assert rhssIt.hasNext();
            updates = updates.append(elementary(services, lhssIt.next(),
                                                rhssIt.next()));
        }
        return parallel(updates);
    }


    public Term sequential(Term u1, Term u2) {
    return parallel(u1, apply(u1, u2, null));
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

    public Term apply(Term update, Term target, ImmutableArray<ITermLabel> labels) {
    if(update.sort() != Sort.UPDATE) {
        throw new TermCreationException("Not an update: " + update);
    } else if(update.op() == UpdateJunctor.SKIP) {
        return target;
    } else if(target.equals(tt())) {
            return tt();
        } else {
        return tf.createTerm(UpdateApplication.UPDATE_APPLICATION,
                     update,
                     target,
                     labels);
    }
    }


    public Term applyElementary(Services services,
                            Term loc,
                            Term value,
                            Term target) {
    return apply(elementary(services, loc, value), target, null);
    }


    public Term applyElementary(Services services,
                            Term heap,
                            Term target) {
    return apply(elementary(services, heap), target, null);
    }


    public ImmutableList<Term> applyElementary(Services services,
                            Term heap,
                            Iterable<Term> targets) {
        ImmutableList<Term> result = ImmutableSLList.<Term>nil();
        for (Term target : targets) {
            result = result.append(apply(elementary(services, heap), target, null));
        }
    return result;
    }


    public Term applyParallel(Term[] updates, Term target) {
    return apply(parallel(updates), target, null);
    }


    public Term applyParallel(ImmutableList<Term> updates, Term target) {
    return apply(parallel(updates), target, null);
    }


    public Term applyParallel(Services services,
                          Term[] lhss,
                          Term[] values,
                          Term target) {
    return apply(parallel(services, lhss, values), target, null);
    }


    public Term applySequential(Term[] updates, Term target) {
    if(updates.length == 0) {
        return target;
    } else {
        ImmutableList<Term> updateList = ImmutableSLList.<Term>nil()
                                            .append(updates)
                                            .tail();
        return apply(updates[0],
                 applySequential(updateList, target), null);
    }
    }


    public Term applySequential(ImmutableList<Term> updates, Term target) {
    if(updates.isEmpty()) {
        return target;
    } else {
        return apply(updates.head(),
                 applySequential(updates.tail(), target), null);
    }
    }

    public Term applyUpdatePairsSequential(ImmutableList<UpdateLabelPair> updates, Term target) {
       if(updates.isEmpty()) {
           return target;
       } else {
           return apply(updates.head().getUpdate(),
                 applyUpdatePairsSequential(updates.tail(), target), updates.head().getUpdateApplicationlabels());
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

    public Term index(Services services){
        return func(services.getTypeConverter().getIntegerLDT().getIndex());
    }



    //-------------------------------------------------------------------------
    //location set operators
    //-------------------------------------------------------------------------

    /**
     * This value is only used as a marker for "\strictly_nothing" in JML. It
     * may return any term. Preferably of type LocSet, but this is not
     * necessary.
     *
     * @return an arbitrary but fixed term.
     */
    public Term strictlyNothing() {
        return ff();
    }

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


    public Term union(Services services, Term ... subTerms) {
        Term result = empty(services);
        for(Term sub : subTerms) {
        result = union(services, result, sub);
    }
        return result;
    }


    public Term union(Services services, Iterable<Term> subTerms) {
        Term result = empty(services);
        for(Term sub : subTerms) {
        result = union(services, result, sub);
    }
        return result;
    }


    public Term intersect(Services services, Term s1, Term s2) {
    final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
    if(s1.op() == ldt.getEmpty() || s2.op() == ldt.getEmpty()) {
        return empty(services);
    } else {
        return func(ldt.getIntersect(), s1, s2);
    }
    }


    public Term intersect(Services services, Term ... subTerms) {
        Term result = empty(services);
        for(Term sub : subTerms) {
        result = intersect(services, result, sub);
    }
        return result;
    }


    public Term intersect(Services services, Iterable<Term> subTerms) {
        Term result = empty(services);
        for(Term sub : subTerms) {
        result = intersect(services, result, sub);
    }
        return result;
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
                        freshLocs(services, getBaseHeap(services)));
    }



    //-------------------------------------------------------------------------
    //heap operators
    //-------------------------------------------------------------------------

    public Term NULL(Services services) {
        return func(services.getTypeConverter().getHeapLDT().getNull());
    }

    public Term wellFormed(Term heap, Services services) {
        return func(services.getTypeConverter().getHeapLDT().getWellFormed(heap.sort()),
                heap);
    }


    public Term wellFormed(LocationVariable heap, Services services) {
        return wellFormed(var(heap), services);
    }


    public Term inv(Services services, Term h, Term o) {
    return func(services.getJavaInfo().getInv(),
            h,
            o);
    }


    public Term inv(Services services, Term o) {
    return inv(services, getBaseHeap(services),  o);
    }

    public Term staticInv(Services services, Term h, KeYJavaType t){
        return func(services.getJavaInfo().getStaticInv(t), h);
    }

    public Term staticInv(Services services, KeYJavaType t){
        return func(services.getJavaInfo().getStaticInv(t), getBaseHeap(services));
    }


    public Term select(Services services, Sort asSort, Term h, Term o, Term f) {
    return func(services.getTypeConverter().getHeapLDT().getSelect(
            asSort,
            services),
            new Term[]{h, o, f});
    }


    public Term dot(Services services, Sort asSort, Term o, Term f) {
        return select(services, asSort, getBaseHeap(services), o, f);
    }

    public Term getBaseHeap(Services services) {
        return var(services.getTypeConverter().getHeapLDT().getHeap());
    }

    public Term dot(Services services, Sort asSort, Term o, Function f) {
    final Sort fieldSort
        = services.getTypeConverter().getHeapLDT().getFieldSort();
        return f.sort() == fieldSort
               ? dot(services, asSort, o, func(f))
               : func(f, getBaseHeap(services), o);
    }


    public Term staticDot(Services services, Sort asSort, Term f) {
        return dot(services, asSort, NULL(services), f);
    }


    public Term staticDot(Services services, Sort asSort, Function f) {
    final Sort fieldSort
        = services.getTypeConverter().getHeapLDT().getFieldSort();
    return f.sort() == fieldSort
           ? staticDot(services, asSort, func(f))
           : func(f, getBaseHeap(services));
    }


    public Term arr(Services services, Term idx) {
    return func(services.getTypeConverter().getHeapLDT().getArr(), idx);
    }
    
    public Term label(Term term, ImmutableArray<ITermLabel> labels) {
        if ((labels == null || labels.isEmpty())) {
            return term;
        } else {
            return TermFactory.DEFAULT.createTerm(term.op(), term.subs(), term.boundVars(), 
                    term.javaBlock(), labels);
        }
    }

    public Term label(Term term, ITermLabel label) {
        if (label == null) {
            return term;
        } else {
            return label(term, new ImmutableArray<ITermLabel>(label));
        }
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
                  getBaseHeap(services),
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
    return created(services, getBaseHeap(services), o);
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
        return store(services, getBaseHeap(services), o, func(f), v);
    }


    public Term staticFieldStore(Services services, Function f, Term v) {
    return fieldStore(services, NULL(services), f, v);
    }


    public Term arrayStore(Services services, Term o, Term i, Term v) {
        return store(services,
                getBaseHeap(services),
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
    } else if(s.equals(intLDT.targetSort()) && kjt.getJavaType() != PrimitiveType.JAVA_BIGINT) {
        return func(intLDT.getInBounds(kjt.getJavaType()), t);
    } else {
        return tt();
    }
    }


    public Term reachableValue(Services services, Term t, KeYJavaType kjt) {
    return reachableValue(services, getBaseHeap(services), t, kjt);
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
    final Term createdAtPre = or.replace(created(services, heapTerm, objVarTerm));

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

    /**
     * Returns the framing condition that the resulting heap is identical (i.e.
     * has the same value in all locations) to the before-heap.
     *
     * @see #frame(Services, Term, Map, Term)
     */
    public Term frameStrictlyEmpty(Services services, Term heapTerm,
            Map<Term,Term> normalToAtPre) {
        final Sort objectSort = services.getJavaInfo().objectSort();
        final Sort fieldSort = services.getTypeConverter()
                .getHeapLDT()
                .getFieldSort();

        final Name objVarName   = new Name(newName(services, "o"));
        final Name fieldVarName = new Name(newName(services, "f"));
        final LogicVariable objVar = new LogicVariable(objVarName, objectSort);
        final LogicVariable fieldVar = new LogicVariable(fieldVarName, fieldSort);
        final Term objVarTerm = var(objVar);
        final Term fieldVarTerm = var(fieldVar);

        final OpReplacer or = new OpReplacer(normalToAtPre);

        ImmutableList<QuantifiableVariable> quantVars =
                ImmutableSLList.<QuantifiableVariable>nil();
        quantVars = quantVars.append(objVar);
        quantVars = quantVars.append(fieldVar);

        return all(quantVars,
                equals(select(services,
                        Sort.ANY,
                        heapTerm,
                        objVarTerm,
                        fieldVarTerm),
                        select(services,
                                Sort.ANY,
                                or.replace(heapTerm),
                                objVarTerm,
                                fieldVarTerm)));
    }

    public Term anonUpd(LocationVariable heap, Services services, Term mod, Term anonHeap) {
    return elementary(services,
                  heap,
                  anon(services,
                       var(heap),
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

    //-------------------------------------------------------------------------
    // misc    (moved from key.util.MiscTools)
    //-------------------------------------------------------------------------



    public ImmutableSet<Term> unionToSet(Term s, Services services) {
    final LocSetLDT setLDT = services.getTypeConverter().getLocSetLDT();
    assert s.sort().equals(setLDT.targetSort());
    final Function union = setLDT.getUnion();
    ImmutableSet<Term> result = DefaultImmutableSet.<Term>nil();
        ImmutableList<Term> workingList = ImmutableSLList.<Term>nil().prepend(s);
        while(!workingList.isEmpty()) {
            Term f = workingList.head();
            workingList = workingList.tail();
            if(f.op() == union) {
                workingList = workingList.prepend(f.sub(1)).prepend(f.sub(0));
            } else {
                result = result.add(f);
            }
        }
        return result;
    }



    /**
     * Removes leading updates from the passed term.
     */
    public Term goBelowUpdates(Term term) {
        while(term.op() instanceof UpdateApplication) {
            term = UpdateApplication.getTarget(term);
        }
        return term;
    }



    /**
     * Removes leading updates from the passed term.
     */
    public Pair<ImmutableList<Term>,Term> goBelowUpdates2(Term term) {
    ImmutableList<Term> updates = ImmutableSLList.<Term>nil();
        while(term.op() instanceof UpdateApplication) {
            updates = updates.append(UpdateApplication.getUpdate(term));
            term = UpdateApplication.getTarget(term);
        }
        return new Pair<ImmutableList<Term>,Term>(updates, term);
    }



    public Term seqDef(QuantifiableVariable qv,
                       Term a,
                       Term b,
                       Term t,
                       Services services) {
        return func(services.getTypeConverter().getSeqLDT().getSeqDef(),
                    new Term[]{a, b, t},
                    new ImmutableArray<QuantifiableVariable>(qv));
    }

    public Term values(Services services){
        return func(services.getTypeConverter().getSeqLDT().getValues());
    }

    /**
      * Returns the {@link Sort}s of the given {@link Term}s.
      * @param terms The given {@link Term}s.
      * @return The {@link Term} {@link Sort}s.
      */
    public ImmutableList<Sort> getSorts(Iterable<Term> terms) {
       ImmutableList<Sort> result = ImmutableSLList.<Sort>nil();
       for (Term t : terms) {
          result = result.append(t.sort());
       }
       return result;
    }

    public static class Serviced extends TermBuilder {

        protected final Services services;

        public Serviced(final Services services)
        {
            assert services != null;
            this.services = services;
        }

        public String newName(final String baseName)
        {
            return newName(services, baseName);
        }

        public LocationVariable selfVar(final IProgramMethod method, final KeYJavaType type, final boolean makeNameUnique)
        {
            return selfVar(services, method, type, makeNameUnique);
        }

        public LocationVariable resultVar(final IProgramMethod method, final boolean makeNameUnique)
        {
            return resultVar(services, method, makeNameUnique);
        }

        public LocationVariable excVar(final IProgramMethod method, final boolean makeNameUnique)
        {
            return excVar(services, method, makeNameUnique);
        }

        public LocationVariable heapAtPreVar(final String baseName, final Sort sort, final boolean makeNameUnique)
        {
            return heapAtPreVar(services, baseName, sort, makeNameUnique);
        }

        public Term convertToFormula(final Term term)
        {
            return convertToFormula(term, services);
        }

        public Term elementary(final UpdateableOperator leftHandSide, final Term rightHandSide) {
            return elementary(services, leftHandSide, rightHandSide);
        }

        public Term TRUE()
        {
            return TRUE(services);
        }

        public Term FALSE()
        {
            return FALSE(services);
        }

        public Term NULL()
        {
            return NULL(services);
        }

        public Term wellFormed(final Term heap)
        {
            return wellFormed(heap, services);
        }

        public Term wellFormed(final LocationVariable heap)
        {
            return wellFormed(heap, services);
        }

        public Term reachableValue(final ProgramVariable variable)
        {
            return reachableValue(services, variable);
        }

        public Term frame(final Term heapTerm, final Map<Term, Term> normalToAtPre, final Term modifiesClause)
        {
            return frame(services, heapTerm, normalToAtPre, modifiesClause);
        }

        public Term frameStrictlyEmpty(final Term heapTerm, final Map<Term, Term> normalToAtPre)
        {
            return frameStrictlyEmpty(services, heapTerm, normalToAtPre);
        }

        public Term anonUpd(final LocationVariable heap, final Term modifiesClause, final Term anonymisationHeap)
        {
            return anonUpd(heap, services, modifiesClause, anonymisationHeap);
        }

        public Term union(final Term firstLocationSet, final Term secondLocationSet)
        {
            return union(services, firstLocationSet, secondLocationSet);
        }

    }



}
