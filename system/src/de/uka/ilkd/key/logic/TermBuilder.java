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
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
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
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
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
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SubstOp;
import de.uka.ilkd.key.logic.op.Transformer;
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
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.WellDefinednessCheck;
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

    private static final String JAVA_LANG_THROWABLE = "java.lang.Throwable";

    private final TermFactory tf;
    private final Term tt;
    private final Term ff;

    protected final Services services; // TODO; Make private
    
    public TermBuilder(TermFactory tf, Services services) {
       assert services != null;
       this.services = services;
       this.tf = tf;
       this.tt = tf.createTerm(Junctor.TRUE);
       this.ff = tf.createTerm(Junctor.FALSE);
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
     */
    public Term parseTerm(String s)
        throws ParserException
    {
    return parseTerm(s, services.getNamespaces());
    }

    /**
     * Parses the given string that represents the term (or createTerm) using the
     * provided namespaces.
     *
     * @param s
     *            the String to parse
     * @param namespaces
     *            the namespaces used for name lookup.
     * @throws de.uka.ilkd.key.parser.ParserException
     */
    public Term parseTerm(String s, NamespaceSet namespaces)
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
    public String newName(String baseName) {
        final Name savedName = services.getNameRecorder().getProposal();
        if (savedName != null) {
            // CS: bugfix -- saving name proposals.
            // getProposal() removes the name proposal form the name recorder,
            // but we need to have it again for saving. Therefore I appended
            // the proposal at the and of the list again.
            services.getNameRecorder().addProposal(savedName);

            return savedName.toString();
        }

        final NamespaceSet namespaces = services.getNamespaces();

        int i = 0;
        String result = baseName;
        while (namespaces.lookup(new Name(result)) != null) {
            result = baseName + "_" + i++;
        }

        services.getNameRecorder().addProposal(new Name(result));

        return result;
    }


    /**
     * Returns an available name constructed by affixing a counter to a self-
     * chosen base name for the passed sort.
     */
    public String newName(TermServices services, Sort sort) {
    return newName(shortBaseName(sort));
    }




    //-------------------------------------------------------------------------
    //common variable constructions
    //-------------------------------------------------------------------------

    /**
     * Creates a program variable for "self". Take care to register it
     * in the namespaces!
     */
    public LocationVariable selfVar(KeYJavaType kjt,
                                    boolean makeNameUnique) {
    String name = "self";
    if(makeNameUnique) {
        name = newName(name);
    }
    return new LocationVariable(new ProgramElementName(name), kjt);
    }


    /**
     * Creates a program variable for "self". Take care to register it
     * in the namespaces!
     */
    public LocationVariable selfVar(IProgramMethod pm,
                                    KeYJavaType kjt,
                                    boolean makeNameUnique) {
        if(pm.isStatic()) {
            return null;
        } else {
            return selfVar(kjt, makeNameUnique);
        }
    }


    /**
     * Creates program variables for the parameters. Take care to register them
     * in the namespaces!
     */
    public ImmutableList<ProgramVariable> paramVars(IObserverFunction obs,
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
            name = newName(name);
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
    public ImmutableList<ProgramVariable> paramVars(String postfix,
        IObserverFunction obs, boolean makeNamesUnique) {
    final ImmutableList<ProgramVariable> paramVars
        = paramVars(obs, true);
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
    public LocationVariable resultVar(IProgramMethod pm,
                                      boolean makeNameUnique) {
    return resultVar("result", pm, makeNameUnique);
    }


    /**
     * Creates a program variable for the result with passed name. Take care to
     * register it in the namespaces.
     */
    public LocationVariable resultVar(String name, IProgramMethod pm,
        boolean makeNameUnique) {
    if(pm.isVoid() || pm.isConstructor()) {
        return null;
    } else {
        if(makeNameUnique) {
        name = newName(name);
        }
        return new LocationVariable(new ProgramElementName(name),
                        pm.getReturnType());
    }
    }


    /**
     * Creates a program variable for the thrown exception. Take care to
     * register it in the namespaces.
     */
    public LocationVariable excVar(IProgramMethod pm,
                                   boolean makeNameUnique) {
    return excVar("exc", pm, makeNameUnique);
    }


    /**
     * Creates a program variable for the thrown exception. Take care to
     * register it in the namespaces.
     */
    public LocationVariable excVar(String name,
                       IProgramMethod pm,
                                   boolean makeNameUnique) {
    if(makeNameUnique) {
        name = newName(name);
    }
        return new LocationVariable(new ProgramElementName(name),
                                    services.getJavaInfo().getTypeByClassName(JAVA_LANG_THROWABLE));
    }


    /**
     * Creates a program variable for the atPre heap. Take care to register it
     * in the namespaces.
     */
    public LocationVariable heapAtPreVar(String baseName,
                                         Sort sort,
                                         boolean makeNameUnique) {
        assert sort != null;
    if(makeNameUnique) {
        baseName = newName(baseName);
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


    public Term prog(Modality mod, JavaBlock jb, Term t, ImmutableArray<TermLabel> labels) {
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

    /** Construct a term with the \ifEx operator. */
    public Term ifEx(ImmutableList<QuantifiableVariable> qvs, Term cond, Term _then, Term _else) {
        if (qvs.isEmpty()) throw new TermCreationException("no quantifiable variables in ifEx term");
        if (qvs.size()==1) {
            return ifEx(qvs.head(), cond, _then, _else);
        } else {
            return ifEx(qvs.head(), tt(), ifEx(qvs.tail(), cond, _then, _else), _else);
        }
    }

    public Term cast(TermServices services, Sort s, Term t) {
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

    /** General (unbounded) sum */
    public Term sum (ImmutableList<QuantifiableVariable> qvs, Term range, Term t, TermServices services) {
        final Function sum = (Function)services.getNamespaces().functions().lookup("sum");
        final Iterator<QuantifiableVariable> it = qvs.iterator();
        Term res = func(sum, new Term[]{convertToBoolean(range), t}, new ImmutableArray<QuantifiableVariable>(it.next()));
        while (it.hasNext()) {
            res = func(sum, new Term[]{TRUE(), res}, new ImmutableArray<QuantifiableVariable>(it.next()));
        }
        return res;
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


    /** General (unbounded) product */
    public Term prod (ImmutableList<QuantifiableVariable> qvs, Term range, Term t, TermServices services) {
        final Function prod = (Function)services.getNamespaces().functions().lookup("prod");
        final Iterator<QuantifiableVariable> it = qvs.iterator();
        Term res = func(prod, new Term[]{convertToBoolean(range), t}, new ImmutableArray<QuantifiableVariable>(it.next()));
        while (it.hasNext()) {
            res = func(prod, new Term[]{TRUE(), res}, new ImmutableArray<QuantifiableVariable>(it.next()));
        }
        return res;
    }


    /** minimum operator */
    public Term min (ImmutableList<QuantifiableVariable> qvs, Term range, Term t, TermServices services) {
        final Function min = (Function)services.getNamespaces().functions().lookup("min");
        final Iterator<QuantifiableVariable> it = qvs.iterator();
        Term res = func(min, new Term[]{convertToBoolean(range), t}, new ImmutableArray<QuantifiableVariable>(it.next()));
        while (it.hasNext()) {
            res = func(min, new Term[]{TRUE(), res}, new ImmutableArray<QuantifiableVariable>(it.next()));
        }
        return res;
    }


    /** minimum operator */
    public Term max (ImmutableList<QuantifiableVariable> qvs, Term range, Term t, TermServices services) {
        final Function max = (Function)services.getNamespaces().functions().lookup("max");
        final Iterator<QuantifiableVariable> it = qvs.iterator();
        Term res = func(max, new Term[]{convertToBoolean(range), t}, new ImmutableArray<QuantifiableVariable>(it.next()));
        while (it.hasNext()) {
            res = func(max, new Term[]{TRUE(), res}, new ImmutableArray<QuantifiableVariable>(it.next()));
        }
        return res;
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

    public Term andSC(Term t1, Term t2) {
        if(t1.op() == Junctor.TRUE || t1.op() == Junctor.FALSE
                || t2.op() == Junctor.FALSE || t2.op() == Junctor.TRUE) {
            return and(t1, t2);
        } else {
            return shortcut(and(t1, t2));
        }
    }

    public Term and(Term ... subTerms) {
        Term result = tt();
        for(Term sub : subTerms) {
            result = and(result, sub);
        }
        return result;
    }

    public Term andSC(Term ... subTerms) {
        Term result = tt();
        if (subTerms.length == 1) {
            return and(subTerms);
        }
        for(Term sub : subTerms) {
            result = andSC(result, sub);
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

    public Term andSC(Iterable<Term> subTerms) {
        Term result = tt();
        int i = 0;
        for(Term sub : subTerms) {
            result = andSC(result, sub);
            i++;
        }
        if (i == 1) {
            return and(subTerms);
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

    public Term orSC(Term t1, Term t2) {
        if(t1.op() == Junctor.TRUE || t1.op() == Junctor.FALSE
                || t2.op() == Junctor.FALSE || t2.op() == Junctor.TRUE) {
            return or(t1, t2);
        } else {
            return shortcut(or(t1, t2));
        }
    }

    public Term or(Term... subTerms) {
        Term result = ff();
        for(Term sub : subTerms) {
            result = or(result, sub);
        }
        return result;
    }

    public Term orSC(Term... subTerms) {
        Term result = ff();
        if (subTerms.length == 1) {
            return or(subTerms);
        }
        for(Term sub : subTerms) {
            result = orSC(result, sub);
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

    public Term orSC(Iterable<Term> subTerms) {
        Term result = ff();
        int i = 0;
        for(Term sub : subTerms) {
            result = orSC(result, sub);
            i++;
        }
        if (i == 1) {
            return or(subTerms);
        }
        return result;
    }

    public Term imp(Term t1, Term t2) {
        return imp(t1, t2, null);
    }


    public Term imp(Term t1, Term t2, ImmutableArray<TermLabel> labels) {
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
        return subst(WarySubstOp.SUBST,
                     substVar,
                     substTerm,
                     origTerm);
    }


    public Term instance(Sort s, Term t) {
    return equals(func(s.getInstanceofSymbol(services), t),
              TRUE());
    }


    public Term exactInstance(Sort s, Term t) {
    return equals(func(s.getExactInstanceofSymbol(services), t),
              TRUE());
    }

    // Functions for wellfoundedness
    //------------------------------

    public Term pair(Term first, Term second) {
        final Namespace funcNS = services.getNamespaces().functions();
        final Function f = (Function)funcNS.lookup(new Name("pair"));
        if (f == null)
            throw new RuntimeException("LDT: Function pair not found.\n" +
                    "It seems that there are definitions missing from the .key files.");

        return func(f, first, second);

    }

    public Term prec(Term mby, Term mbyAtPre) {
        final Namespace funcNS = services.getNamespaces().functions();
        final Function f = (Function)funcNS.lookup(new Name("prec"));
        if (f == null)
                throw new RuntimeException("LDT: Function prec not found.\n" +
                                "It seems that there are definitions missing from the .key files.");

        return func(f, mby, mbyAtPre);
    }

    public Term measuredByCheck(Term mby) {
        final Namespace funcNS = services.getNamespaces().functions();
        final Function f = (Function)funcNS.lookup(new Name("measuredByCheck"));
        if (f == null)
                throw new RuntimeException("LDT: Function measuredByCheck not found.\n" +
                                "It seems that there are definitions missing from the .key files.");
        return func(f, mby);
    }

    public Term measuredBy(Term mby) {
        final Namespace funcNS = services.getNamespaces().functions();
        final Function f = (Function)funcNS.lookup(new Name("measuredBy"));
        if (f == null)
                throw new RuntimeException("LDT: Function measuredBy not found.\n" +
                                "It seems that there are definitions missing from the .key files.");
        return func(f, mby);
    }

    public Term measuredByEmpty() {
        final Namespace funcNS = services.getNamespaces().functions();
        final Function f = (Function)funcNS.lookup(new Name("measuredByEmpty"));
        if (f == null)
                throw new RuntimeException("LDT: Function measuredByEmpty not found.\n" +
                                "It seems that there are definitions missing from the .key files.");
        return func(f);
    }

    /**
     * If a is a boolean literal, the method returns the literal as a Formula.
     */
    public Term convertToFormula(Term a) {
        BooleanLDT booleanLDT = services.getTypeConverter().getBooleanLDT();
        if (a.sort() == Sort.FORMULA) {
            return a;
        } else if (a.sort() == booleanLDT.targetSort()) {
            // special case where a is the result of convertToBoolean
            if (a.op() == IfThenElse.IF_THEN_ELSE) {
                assert a.subs().size() == 3;
                assert a.sub(0).sort() == Sort.FORMULA;
                if (a.sub(1).op() == booleanLDT.getTrueConst() && a.sub(2).op() == booleanLDT.getFalseConst())
                    return a.sub(0);
                else if (a.sub(1).op() == booleanLDT.getFalseConst() && a.sub(2).op() == booleanLDT.getTrueConst())
                    return not(a.sub(0));
            }
            return equals(a, TRUE());
        } else {
            throw new TermCreationException("Term " + a + " cannot be converted"
                                            + " into a formula.");
        }
    }

    /** For a formula a, convert it to a boolean expression. */
    public Term convertToBoolean(Term a){
        BooleanLDT booleanLDT = services.getTypeConverter().getBooleanLDT();
        if (a.sort() == booleanLDT.targetSort()) {
            return a;
        } else if (a.sort() == Sort.FORMULA) {
            // special case where a is the result of convertToFormula
            if (a.op() == Equality.EQUALS && a.sub(1).op() == booleanLDT.getTrueConst() ) {
                return a.sub(0);
            }
            return ife(a, TRUE(), FALSE());
        } else {
            throw new TermCreationException("Term " + a + " cannot be converted"
                    + " into a boolean.");
}
    }


    //-------------------------------------------------------------------------
    //updates
    //-------------------------------------------------------------------------

    public Term elementary(UpdateableOperator lhs, Term rhs) {
    ElementaryUpdate eu = ElementaryUpdate.getInstance(lhs);
    return tf.createTerm(eu, rhs);
    }


    public Term elementary(Term lhs, Term rhs) {
    HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
    if(lhs.op() instanceof UpdateableOperator) {
        assert lhs.arity() == 0 : "uh oh: " + lhs;
        return elementary((UpdateableOperator)lhs.op(), rhs);
    } else if(heapLDT.getSortOfSelect(lhs.op()) != null
          && lhs.sub(0).op().equals(heapLDT.getHeap())) {
        final Term heapTerm   = lhs.sub(0);
        final Term objectTerm = lhs.sub(1);
        final Term fieldTerm  = lhs.sub(2);

        final Term fullRhs = store(heapTerm,
                                   objectTerm,
                               fieldTerm,
                               rhs);
        return elementary(heapLDT.getHeap(), fullRhs);
    } else {
        throw new TermCreationException("Not a legal lhs: " + lhs);
    }
    }


    private Term elementary(Term heapTerm) {
        return elementary(getBaseHeap(), heapTerm);
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


    public Term parallel(Term[] lhss, Term[] values) {
    if(lhss.length != values.length) {
        throw new TermCreationException(
            "Tried to create parallel update with "
            + lhss.length + " locs and " + values.length + " values");
    }
    Term[] updates = new Term[lhss.length];
    for(int i = 0; i < updates.length; i++) {
        updates[i] = elementary(lhss[i], values[i]);
    }
    return parallel(updates);
    }


    public Term parallel(Iterable<Term> lhss,
                         Iterable<Term> values) {
        ImmutableList<Term> updates = ImmutableSLList.<Term>nil();
        Iterator<Term> lhssIt = lhss.iterator();
        Iterator<Term> rhssIt = values.iterator();
        while (lhssIt.hasNext()) {
            assert rhssIt.hasNext();
            updates = updates.append(elementary(lhssIt.next(), rhssIt.next()));
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

    public Term apply(Term update, Term target) {
        return apply(update,target,null);
    }

    public Term apply(Term update, Term target, ImmutableArray<TermLabel> labels) {
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


    public Term applyElementary(Term loc,
                            Term value,
                            Term target) {
    return apply(elementary(loc, value), target, null);
    }


    public Term applyElementary(Term heap,
                            Term target) {
    return apply(elementary(heap), target, null);
    }


    public ImmutableList<Term> applyElementary(Term heap,
                            Iterable<Term> targets) {
        ImmutableList<Term> result = ImmutableSLList.<Term>nil();
        for (Term target : targets) {
            result = result.append(apply(elementary(heap), target, null));
        }
    return result;
    }


    public Term applyParallel(Term[] updates, Term target) {
    return apply(parallel(updates), target, null);
    }


    public Term applyParallel(ImmutableList<Term> updates, Term target) {
    return apply(parallel(updates), target, null);
    }


    public Term applyParallel(Term[] lhss,
                          Term[] values,
                          Term target) {
    return apply(parallel(lhss, values), target, null);
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

    public Term TRUE() {
        return services.getTypeConverter().getBooleanLDT().getTrueTerm();
    }


    public Term FALSE() {
        return services.getTypeConverter().getBooleanLDT().getFalseTerm();
    }



    //-------------------------------------------------------------------------
    //integer operators
    //-------------------------------------------------------------------------

    public Term geq(Term t1, Term t2) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return func(integerLDT.getGreaterOrEquals(), t1, t2);
    }


    public Term gt(Term t1, Term t2) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return func(integerLDT.getGreaterThan(), t1, t2);
    }


    public Term lt(Term t1, Term t2) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return func(integerLDT.getLessThan(), t1, t2);
    }


    public Term leq(Term t1, Term t2) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return func(integerLDT.getLessOrEquals(), t1, t2);
    }


    public Term zero() {
    return services.getTypeConverter().getIntegerLDT().zero();
    }


    public Term one() {
        return services.getTypeConverter().getIntegerLDT().one();
    }

    /**
     * @param numberString String representing an integer
     * @return Term in Z-Notation representing the given number
     * @throws NumberFormatException if <code>numberString</code> is not a number
     */
    public Term zTerm(String numberString) {

        if (numberString == null || numberString.isEmpty()) {
            throw new NumberFormatException(numberString + " is not a number.");
        }

        Term numberLiteralTerm;
        boolean negate = false;
        int j = 0;

        final IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();

        if (numberString.charAt(0) == '-') {
            negate = true;
            j = 1;
        }
        numberLiteralTerm = func(intLDT.getNumberTerminator());

        int digit;
        for (int i = j, sz = numberString.length(); i<sz; i++) {
            switch(numberString.charAt(i)) {
                case '0' : digit = 0; break;
                case '1' : digit = 1; break;
                case '2' : digit = 2; break;
                case '3' : digit = 3; break;
                case '4' : digit = 4; break;
                case '5' : digit = 5; break;
                case '6' : digit = 6; break;
                case '7' : digit = 7; break;
                case '8' : digit = 8; break;
                case '9' : digit = 9; break;
                default:
                    throw new NumberFormatException(numberString + " is not a number.");
            }

            numberLiteralTerm = func(intLDT.getNumberLiteralFor(digit), numberLiteralTerm);
        }
        if (negate) {
            numberLiteralTerm = func(intLDT.getNegativeNumberSign(), numberLiteralTerm);
        }
        numberLiteralTerm = func(intLDT.getNumberSymbol(), numberLiteralTerm);
        return numberLiteralTerm;
    }

    /**
     * @param number an integer
     * @return Term in Z-Notation representing the given number
     */
    public Term zTerm(int number) {
        return zTerm(""+number);
    }


    public Term add(Term t1, Term t2) {
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

    public Term inByte(Term var) {
        Function f =
                (Function) services.getNamespaces().functions().lookup(
                new Name("inByte"));
        return func(f, var);
    }

    public Term inShort(Term var) {
        Function f =
                (Function) services.getNamespaces().functions().lookup(
                new Name("inShort"));
        return func(f, var);
    }

    public Term inChar(Term var) {
        Function f =
                (Function) services.getNamespaces().functions().lookup(
                new Name("inChar"));
        return func(f, var);
    }

    public Term inInt(Term var) {
        Function f =
                (Function) services.getNamespaces().functions().lookup(
                new Name("inInt"));
        return func(f, var);
    }



    public Term inLong(Term var) {
        Function f =
                (Function) services.getNamespaces().functions().lookup(
                new Name("inLong"));
        return func(f, var);
    }

    public Term index(){
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

    public Term empty() {
    return func(services.getTypeConverter().getLocSetLDT().getEmpty());
    }


    public Term allLocs() {
    return func(services.getTypeConverter().getLocSetLDT().getAllLocs());
    }


    public Term singleton(Term o, Term f) {
    return func(services.getTypeConverter().getLocSetLDT().getSingleton(),
            o,
            f);
    }


    public Term union(Term s1, Term s2) {
        final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
        if(s1.op() == ldt.getEmpty()) {
            return s2;
        } else if(s2.op() == ldt.getEmpty()) {
            return s1;
        } else {
            return func(ldt.getUnion(), s1, s2);
        }
    }


    public Term union(Term ... subTerms) {
        Term result = empty();
        for(Term sub : subTerms) {
        result = union(result, sub);
        }
        return result;
    }


    public Term union(Iterable<Term> subTerms) {
        Term result = empty();
        for(Term sub : subTerms) {
        result = union(result, sub);
        }
        return result;
    }


    public Term intersect(Term s1, Term s2) {
        final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
        if(s1.op() == ldt.getEmpty() || s2.op() == ldt.getEmpty()) {
            return empty();
        } else {
            return func(ldt.getIntersect(), s1, s2);
        }
    }


    public Term intersect(Term ... subTerms) {
        Term result = empty();
        for(Term sub : subTerms) {
            result = intersect(result, sub);
        }
        return result;
    }


    public Term intersect(Iterable<Term> subTerms) {
        Term result = empty();
        for(Term sub : subTerms) {
            result = intersect(result, sub);
        }
        return result;
    }


    public Term setMinus(Term s1, Term s2) {
        final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
        if(s1.op() == ldt.getEmpty() || s2.op() == ldt.getEmpty()) {
            return s1;
        } else {
            return func(ldt.getSetMinus(), s1, s2);
        }
    }


    public Term infiniteUnion(QuantifiableVariable[] qvs,
                              Term s) {
        final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
        return tf.createTerm(ldt.getInfiniteUnion(),
                new Term[]{s},
                new ImmutableArray<QuantifiableVariable>(qvs),
                null);
    }


    public Term guardedInfiniteUnion(QuantifiableVariable[] qvs,
                         Term guard,
                         Term s) {
        return infiniteUnion(qvs,
                             ife(guard, s, empty()));
    }


    public Term setComprehension(QuantifiableVariable[] qvs,
                                 Term o,
                                 Term f) {
        return infiniteUnion(qvs, singleton(o, f));
    }


    public Term guardedSetComprehension(QuantifiableVariable[] qvs,
                                Term guard,
                                Term o,
                                Term f) {
        return guardedInfiniteUnion(qvs,
                                    guard,
                                    singleton(o, f));
    }


    public Term allFields(Term o) {
        return func(services.getTypeConverter().getLocSetLDT().getAllFields(), o);
    }


    public Term allObjects(Term f) {
        return func(services.getTypeConverter().getLocSetLDT().getAllObjects(), f);
    }


    public Term arrayRange(Term o, Term lower, Term upper) {
        return func(services.getTypeConverter().getLocSetLDT().getArrayRange(),
                o, lower, upper);
    }


    public Term freshLocs(Term h) {
        return func(services.getTypeConverter().getLocSetLDT().getFreshLocs(), h);
    }


    public Term elementOf(Term o, Term f, Term s) {
        final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
        if(s.op() == ldt.getEmpty()) {
            return ff();
        } else {
            return func(ldt.getElementOf(), o, f, s);
        }
    }


    public Term subset(Term s1, Term s2) {
        final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
        if(s1.op() == ldt.getEmpty()) {
            return tt();
        } else {
            return func(ldt.getSubset(), s1, s2);
        }
    }


    public Term disjoint(Term s1, Term s2) {
        final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
        if(s1.op() == ldt.getEmpty() || s2.op() == ldt.getEmpty()) {
            return tt();
        } else {
            return func(ldt.getDisjoint(), s1, s2);
        }
    }


    public Term createdInHeap(Term s, Term h) {
        final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
        if(s.op() == ldt.getEmpty()) {
            return tt();
        } else {
            return func(ldt.getCreatedInHeap(), s, h);
        }
    }


    public Term createdLocs() {
        return setMinus(allLocs(),
                    freshLocs(getBaseHeap()));
    }

    // The template of the well-definedness transformer for terms.
    public static final Transformer WD_ANY =
            new Transformer(new Name("wd"), Sort.ANY);

    // The template of the well-definedness transformer for formulas.
    public static final Transformer WD_FORMULA =
            new Transformer(new Name("WD"), Sort.FORMULA);

    public Term wd(Term t) {
        if(t.op() == Junctor.FALSE || t.op() == Junctor.TRUE) {
            return tt();
        } else if (t.sort().equals(Sort.FORMULA)) {
            return func(Transformer.getTransformer(WD_FORMULA, services), t);
        } else {
            return func(Transformer.getTransformer(WD_ANY, services), t);
        }
    }

    public ImmutableList<Term> wd(Iterable<Term> l) {
        ImmutableList<Term> res = ImmutableSLList.<Term>nil();
        for (Term t: l) {
            res = res.append(wd(t));
        }
        return res;
    }

    public Term[] wd(Term[] l) {
        Term[] res = new Term[l.length];
        for(int i = 0; i < l.length; i++) {
            res[i] = wd(l[i]);
        }
        return res;
    }


    //-------------------------------------------------------------------------
    //heap operators
    //-------------------------------------------------------------------------

    public Term NULL() {
        return func(services.getTypeConverter().getHeapLDT().getNull());
    }
    
    /** The "deep non null" predicate arising from JML non_null types.
     * Deep non null means that it is recursively defined for arrays.
     * See bug #1392.
     */
    public Term deepNonNull(Term o, Term d) {
        final Function nonNull = (Function) services.getNamespaces().functions().lookup("nonNull");
        final Term heap = getBaseHeap();
        return func(nonNull, heap, o, d);
    }

    public Term wellFormed(Term heap) {
        return func(services.getTypeConverter().getHeapLDT().getWellFormed(heap.sort()),
                heap);
    }

    public Term wellFormed(LocationVariable heap) {
        return wellFormed(var(heap));
    }


    public Term inv(Term[] h, Term o) {
        Term[] p = new Term[h.length + 1];
        System.arraycopy(h, 0, p, 0, h.length);
        p[h.length] = o;
        return func(services.getJavaInfo().getInv(), p);
    }


    public Term inv(Term o) {
        List<LocationVariable> heaps = HeapContext.getModHeaps(services, false);
        Term[] hs = new Term[heaps.size()];
        int i=0;
        for(LocationVariable heap : heaps) {
            hs[i++] = var(heap);
        }
        return inv(hs, o);
    }

    public Term staticInv(Term[] h, KeYJavaType t){
        return func(services.getJavaInfo().getStaticInv(t), h);
    }

    public Term staticInv(KeYJavaType t){
        List<LocationVariable> heaps = HeapContext.getModHeaps(services, false);
        Term[] hs = new Term[heaps.size()];
        int i=0;
        for(LocationVariable heap : heaps) {
            hs[i++] = var(heap);
        }
        return func(services.getJavaInfo().getStaticInv(t), hs);
    }


    public Term select(Sort asSort, Term h, Term o, Term f) {
    return func(services.getTypeConverter().getHeapLDT().getSelect(
            asSort,
            services),
            h, o, f);
    }


    public Term dot(Sort asSort, Term o, Term f) {
        return select(asSort, getBaseHeap(), o, f);
    }

    public Term getBaseHeap() {
        return var(services.getTypeConverter().getHeapLDT().getHeap());
    }

    public Term dot(Sort asSort, Term o, Function f) {
    final Sort fieldSort
        = services.getTypeConverter().getHeapLDT().getFieldSort();
        return f.sort() == fieldSort
               ? dot(asSort, o, func(f))
               : func(f, getBaseHeap(), o);
    }


    public Term staticDot(Sort asSort, Term f) {
        return dot(asSort, NULL(), f);
    }


    public Term staticDot(Sort asSort, Function f) {
    final Sort fieldSort
        = services.getTypeConverter().getHeapLDT().getFieldSort();
    return f.sort() == fieldSort
           ? staticDot(asSort, func(f))
           : func(f, getBaseHeap());
    }


    public Term arr(Term idx) {
    return func(services.getTypeConverter().getHeapLDT().getArr(), idx);
    }

    public Term addLabel(Term term, ImmutableArray<TermLabel> labels) {
        if ((labels == null || labels.isEmpty())
                && !term.hasLabels()) {
            return term;
        } else if (!term.hasLabels()) {
            return tf.createTerm(term.op(), term.subs(), term.boundVars(),
                    term.javaBlock(), labels);
        } else {
            ImmutableList<TermLabel> newLabelList = ImmutableSLList.<TermLabel>nil();
            for (TermLabel l: labels) {
                if (!term.getLabels().contains(l)) {
                    newLabelList = newLabelList.append(l);
                }
            }
            TermLabel[] newLabelArr = new TermLabel[newLabelList.size()];
            Iterator<TermLabel> it = newLabelList.iterator();
            for (int i = 0; i < newLabelArr.length; i++) {
                assert it.hasNext();
                newLabelArr[i] = it.next();
            }
            TermLabel[] newLabels = new TermLabel[labels.size() + newLabelArr.length];
            labels.arraycopy(0, newLabels, 0, labels.size());
            new ImmutableArray<TermLabel>(newLabelArr).arraycopy(0, newLabels, labels.size(),
                                                                  newLabelArr.length);
            return tf.createTerm(term.op(), term.subs(),
                                                  term.boundVars(), term.javaBlock(),
                                                  new ImmutableArray<TermLabel>(newLabels));
        }
    }

    public Term addLabel(Term term, TermLabel label) {
        if (label == null && !term.hasLabels()) {
            return term;
        } else {
            return addLabel(term, new ImmutableArray<TermLabel>(label));
        }
    }

    public Term label(Term term, ImmutableArray<TermLabel> labels) {
        if ((labels == null || labels.isEmpty())) {
            return term;
        } else if (labels.size() == 1
                && (labels.contains(ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL)
                        || labels.contains(ParameterlessTermLabel.SHORTCUT_EVALUATION_LABEL)
                        || labels.contains(ParameterlessTermLabel.UNDEFINED_VALUE_LABEL))
                && !WellDefinednessCheck.isOn()) {
            return term; // FIXME: This case is only for SET Tests
        } else {
            return tf.createTerm(term.op(), term.subs(), term.boundVars(),
                                 term.javaBlock(), labels);
        }
    }

    public Term label(Term term, TermLabel label) {
        if (label == null) {
            return term;
        } else {
            return label(term, new ImmutableArray<TermLabel>(label));
        }
    }

    public Term shortcut(Term term) {
        if ((term.op().equals(Junctor.AND)
                        || term.op().equals(Junctor.OR))
            && WellDefinednessCheck.isOn()) { // FIXME: Last condition is only for SET Tests
            return addLabel(term, ParameterlessTermLabel.SHORTCUT_EVALUATION_LABEL);
        } else {
            return term;
        }
    }

    public Term dotArr(Term ref, Term idx) {
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

        return select(elementSort,
                  getBaseHeap(),
                  ref,
                  arr(idx));
    }


    public Term dotLength(Term a) {
        final TypeConverter tc = services.getTypeConverter();
        return func(tc.getHeapLDT().getLength(), a);
    }


    public Term created(Term h, Term o) {
        final TypeConverter tc = services.getTypeConverter();
        return equals(select(tc.getBooleanLDT().targetSort(),
                             h,
                             o,
                             func(tc.getHeapLDT().getCreated())),
                      TRUE());
    }


    public Term created(Term o) {
        return created(getBaseHeap(), o);
    }

    public Term initialized(Term o) {
        final TypeConverter tc = services.getTypeConverter();
        return equals(dot(tc.getBooleanLDT().targetSort(),
                o,
                tc.getHeapLDT().getInitialized()),
                TRUE());
    }


    public Term classPrepared(Sort classSort) {
        final TypeConverter tc = services.getTypeConverter();
        return equals(staticDot(tc.getBooleanLDT().targetSort(),
                tc.getHeapLDT().getClassPrepared(classSort,
                        services)),
                        TRUE());
    }

    public Term classInitialized(Sort classSort) {
        final TypeConverter tc = services.getTypeConverter();
        return equals(staticDot(tc.getBooleanLDT().targetSort(),
                tc.getHeapLDT().getClassInitialized(classSort,
                        services)),
                        TRUE());
    }

    public Term classInitializationInProgress(Sort classSort) {
        final TypeConverter tc = services.getTypeConverter();
        return equals(staticDot(tc.getBooleanLDT().targetSort(),
                tc.getHeapLDT()
                .getClassInitializationInProgress(classSort,
                        services)),
                        TRUE());
    }


    public Term classErroneous(Sort classSort) {
        final TypeConverter tc = services.getTypeConverter();
        return equals(staticDot(tc.getBooleanLDT().targetSort(),
                tc.getHeapLDT().getClassErroneous(classSort,
                        services)),
                        TRUE());
    }


    public Term store(Term h, Term o, Term f, Term v) {
        return func(services.getTypeConverter().getHeapLDT().getStore(),
                h, o, f, v);
    }


    public Term create(Term h, Term o) {
        return func(services.getTypeConverter().getHeapLDT().getCreate(),
                 new Term[]{h, o});
    }


    public Term anon(Term h1, Term s, Term h2) {
    return func(services.getTypeConverter().getHeapLDT().getAnon(),
            h1, s, h2);
    }


    public Term fieldStore(TermServices services, Term o, Function f, Term v) {
        return store(getBaseHeap(), o, func(f), v);
    }


    public Term staticFieldStore(Function f, Term v) {
    return fieldStore(services, NULL(), f, v);
    }


    public Term arrayStore(Term o, Term i, Term v) {
        return store(getBaseHeap(),
                o,
                 func(services.getTypeConverter().getHeapLDT().getArr(), i),
                 v);
    }


    public Term reachableValue(Term h,
                               Term t,
                               KeYJavaType kjt) {
        assert t.sort().extendsTrans(kjt.getSort()) || t.sort() instanceof ProgramSVSort;
        final Sort s = t.sort() instanceof ProgramSVSort ? kjt.getSort() : t.sort();
        final IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();
        final LocSetLDT setLDT = services.getTypeConverter().getLocSetLDT();
        if(s.extendsTrans(services.getJavaInfo().objectSort())) {
            return orSC(equals(t, NULL()), created(h, t));
        } else if(s.equals(setLDT.targetSort())) {
            return createdInHeap(t, h);
        } else if(s.equals(intLDT.targetSort()) && kjt.getJavaType() != PrimitiveType.JAVA_BIGINT) {
            return func(intLDT.getInBounds(kjt.getJavaType()), t);
        } else {
            return tt();
        }
    }


    public Term reachableValue(Term t, KeYJavaType kjt) {
        return reachableValue(getBaseHeap(), t, kjt);
    }


    public Term reachableValue(ProgramVariable pv) {
        return reachableValue(var(pv), pv.getKeYJavaType());
    }


    public Term frame(Term heapTerm, Map<Term,Term> normalToAtPre,
                  Term mod) {
        final Sort objectSort = services.getJavaInfo().objectSort();
        final Sort fieldSort = services.getTypeConverter()
                .getHeapLDT()
                .getFieldSort();

        final Name objVarName   = new Name(newName("o"));
        final Name fieldVarName = new Name(newName("f"));
        final LogicVariable objVar
        = new LogicVariable(objVarName, objectSort);
        final LogicVariable fieldVar
        = new LogicVariable(fieldVarName, fieldSort);
        final Term objVarTerm = var(objVar);
        final Term fieldVarTerm = var(fieldVar);

        final OpReplacer or = new OpReplacer(normalToAtPre, tf);
        final Term modAtPre = or.replace(mod);
        final Term createdAtPre = or.replace(created(heapTerm, objVarTerm));

        ImmutableList<QuantifiableVariable> quantVars =
                ImmutableSLList.<QuantifiableVariable>nil();
        quantVars = quantVars.append(objVar);
        quantVars = quantVars.append(fieldVar);
        return all(quantVars,
                or(elementOf(objVarTerm,
                        fieldVarTerm,
                        modAtPre),
                        and(not(equals(objVarTerm, NULL())),
                                not(createdAtPre)),
                                equals(select(Sort.ANY,
                                        heapTerm,
                                        objVarTerm,
                                        fieldVarTerm),
                                        select(Sort.ANY,
                                                or.replace(heapTerm),
                                                objVarTerm,
                                                fieldVarTerm))));
    }

    /**
     * Returns the framing condition that the resulting heap is identical (i.e.
     * has the same value in all locations) to the before-heap.
     *
     * @see #frame(Term, Map, Term)
     */
    public Term frameStrictlyEmpty(Term heapTerm, Map<Term,Term> normalToAtPre) {
        final Sort objectSort = services.getJavaInfo().objectSort();
        final Sort fieldSort = services.getTypeConverter()
                .getHeapLDT()
                .getFieldSort();

        final Name objVarName   = new Name(newName("o"));
        final Name fieldVarName = new Name(newName("f"));
        final LogicVariable objVar = new LogicVariable(objVarName, objectSort);
        final LogicVariable fieldVar = new LogicVariable(fieldVarName, fieldSort);
        final Term objVarTerm = var(objVar);
        final Term fieldVarTerm = var(fieldVar);

        final OpReplacer or = new OpReplacer(normalToAtPre, tf);

        ImmutableList<QuantifiableVariable> quantVars =
                ImmutableSLList.<QuantifiableVariable>nil();
        quantVars = quantVars.append(objVar);
        quantVars = quantVars.append(fieldVar);

        return all(quantVars,
                equals(select(Sort.ANY,
                        heapTerm,
                        objVarTerm,
                        fieldVarTerm),
                        select(Sort.ANY,
                                or.replace(heapTerm),
                                objVarTerm,
                                fieldVarTerm)));
    }

    public Term anonUpd(LocationVariable heap, Term mod, Term anonHeap) {
        return elementary(heap, anon(var(heap), mod, anonHeap));
    }


    public Term forallHeaps(Services services, Term t) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final LogicVariable heapLV
        = new LogicVariable(new Name("h"), heapLDT.targetSort());
        final Map<LocationVariable, LogicVariable> map
        = new LinkedHashMap<LocationVariable, LogicVariable>();
        map.put(heapLDT.getHeap(), heapLV);
        final OpReplacer or = new OpReplacer(map, tf);
        t = or.replace(t);
        return all(heapLV, t);
    }


    //-------------------------------------------------------------------------
    //reachability operators
    //-------------------------------------------------------------------------

    public Term acc(Term h, Term s, Term o1, Term o2) {
    return func(services.getTypeConverter().getHeapLDT().getAcc(),
            h, s, o1, o2);
    }


    public Term reach(Term h,
                  Term s,
                  Term o1,
                  Term o2,
                  Term n) {
    return func(services.getTypeConverter().getHeapLDT().getReach(),
            h, s, o1, o2, n);
    }


    //-------------------------------------------------------------------------
    //sequence operators
    //-------------------------------------------------------------------------

    public Term seqGet(Sort asSort, Term s, Term idx) {
    return func(services.getTypeConverter().getSeqLDT().getSeqGet(asSort,
                                          services),
            s,
            idx);
    }


    public Term seqLen(Term s) {
    return func(services.getTypeConverter().getSeqLDT().getSeqLen(), s);
    }

    /** Function representing the least index of an element x in a sequence s (or underspecified) */
    public Term indexOf(Term s, Term x){
    return func(services.getTypeConverter().getSeqLDT().getSeqIndexOf(),s,x);
    }


    public Term seqEmpty() {
    return func(services.getTypeConverter().getSeqLDT().getSeqEmpty());
    }


    public Term seqSingleton(Term x) {
    return func(services.getTypeConverter().getSeqLDT().getSeqSingleton(), x);
    }


    public Term seqConcat(Term s, Term s2) {
    return func(services.getTypeConverter().getSeqLDT().getSeqConcat(), s, s2);
    }


    public Term seqSub(Term s, Term from, Term to) {
    return func(services.getTypeConverter().getSeqLDT().getSeqSub(), s, from, to);
    }


    public Term seqReverse(Term s) {
    return func(services.getTypeConverter().getSeqLDT().getSeqReverse(), s);
    }

    //-------------------------------------------------------------------------
    // misc    (moved from key.util.MiscTools)
    //-------------------------------------------------------------------------



    public ImmutableSet<Term> unionToSet(Term s) {
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
    public static Term goBelowUpdates(Term term) {
        while(term.op() instanceof UpdateApplication) {
            term = UpdateApplication.getTarget(term);
        }
        return term;
    }



    /**
     * Removes leading updates from the passed term.
     */
    public static Pair<ImmutableList<Term>,Term> goBelowUpdates2(Term term) {
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
                       Term t) {
        return func(services.getTypeConverter().getSeqLDT().getSeqDef(),
                    new Term[]{a, b, t},
                    new ImmutableArray<QuantifiableVariable>(qv));
    }

    public Term values(){
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
    
}
