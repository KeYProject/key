/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.ldt.*;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabelFactory;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.inst.SVInstantiations.UpdateLabelPair;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Metavariable;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.TermCreationException;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.UpdateableOperator;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.*;

/**
 * <p>
 * Use this class if you intend to build complex terms by hand. It is more convenient than
 * the @link{TermFactory} class.
 * </p>
 *
 * <p>
 * Attention: some methods of this class try to simplify some terms. So if you want to be sure that
 * the term looks exactly as you built it, you will have to use the TermFactory.
 * </p>
 */
public class TermBuilder {
    private static final String JAVA_LANG_THROWABLE = "java.lang.Throwable";
    private final TermFactory tf;
    private final JTerm tt;
    private final JTerm ff;

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

    // -------------------------------------------------------------------------
    // build terms using the KeY parser
    // -------------------------------------------------------------------------

    /**
     * Parses the given string that represents the term (or createTerm) using the service's
     * namespaces.
     *
     * @param s the String to parse
     */
    public JTerm parseTerm(String s) throws ParserException {
        return parseTerm(s, services.getNamespaces());
    }

    /**
     * Parses the given string that represents the term (or createTerm) using the provided
     * namespaces.
     *
     * @param s the String to parse
     * @param namespaces the namespaces used for name lookup.
     * @throws ParserException if the given String cannot be parsed
     */
    public JTerm parseTerm(String s, NamespaceSet namespaces) throws ParserException {
        final AbbrevMap abbr =
            (services.getProof() == null) ? null : services.getProof().abbreviations();
        final KeyIO parser = new KeyIO(services, namespaces);
        parser.setAbbrevMap(abbr);
        return parser.parseExpression(s);
    }

    // -------------------------------------------------------------------------
    // naming
    // -------------------------------------------------------------------------

    public String shortBaseName(Sort s) {
        String result = s.name().toString();
        int index = result.lastIndexOf('.');
        if (index == -1) {
            result = String.valueOf(result.charAt(0));
        } else {
            result = String.valueOf(result.substring(index).charAt(1));
        }
        return result.toLowerCase();
    }

    /**
     * Returns an available name constructed by affixing a counter to the passed base name.
     * <p>
     * This method looks up the global {@link NamespaceSet} to check whether the {@link Name}s is
     * free. This can be problematic, since {@link Namespace}s are now local to goals. Use
     * {@link #newName(String, NamespaceSet)} to make sure that you have all the {@link Name}s you
     * need available.
     *
     * @param baseName The base name (prefix) for the name to generate.
     * @return An available name constructed by affixing a counter to the passed base name, or some
     *         available free name (please consult comment above).
     * @see #newName(String, NamespaceSet)
     */
    public String newName(String baseName) {
        return newName(baseName, services.getNamespaces());
    }

    /**
     * Returns an available name constructed by affixing a counter to the passed base name.
     * <p>
     * <p>
     * Warning (DS): This method ignores the baseName if there are free name proposals. This can,
     * for instance, cause troubles in loading proofs containing rule apps with more than one
     * introduced (and saved) new name. In this case, the order of new names in the saved proof file
     * matters (the first unused name is returned, regardless of the baseName).
     *
     * @param baseName The base name (prefix) for the name to generate.
     * @param localNamespace The local {@link NamespaceSet} to check.
     * @return An available name constructed by affixing a counter to the passed base name, or some
     *         available free name (please consult comment above).
     */
    public String newName(String baseName, NamespaceSet localNamespace) {
        final Name savedName = services.getNameRecorder().getProposal();
        if (savedName != null) {
            // CS: bugfix -- saving name proposals.
            // getProposal() removes the name proposal form the name recorder,
            // but we need to have it again for saving. Therefore, I appended
            // the proposal at the end of the list again.
            services.getNameRecorder().addProposal(savedName);

            return savedName.toString();
        }

        int i = 0;
        String result = baseName;
        while (localNamespace.lookup(new Name(result)) != null) {
            result = baseName + "_" + i++;
        }

        services.getNameRecorder().addProposal(new Name(result));

        return result;
    }

    /**
     * Returns an available name constructed by affixing a counter to a self- chosen base name for
     * the passed sort.
     */
    public String newName(Sort sort) {
        return newName(shortBaseName(sort));
    }

    // -------------------------------------------------------------------------
    // common variable constructions
    // -------------------------------------------------------------------------

    /**
     * Creates a program variable for "self". Take care to register it in the namespaces!
     */
    public LocationVariable selfVar(KeYJavaType kjt, boolean makeNameUnique) {
        return selfVar(kjt, makeNameUnique, "");
    }

    /**
     * Creates a program variable for "self". Take care to register it in the namespaces!
     */
    public LocationVariable selfVar(KeYJavaType kjt, boolean makeNameUnique, String postfix) {
        String name = "self" + postfix;
        return locationVariable(name, kjt, makeNameUnique);
    }

    /**
     * Creates a program variable for "self". Take care to register it in the namespaces!
     */
    public LocationVariable selfVar(IProgramMethod pm, KeYJavaType kjt, boolean makeNameUnique,
            String postfix) {
        if (pm.isStatic()) {
            return null;
        } else {
            return selfVar(kjt, makeNameUnique, postfix);
        }
    }

    /**
     * Creates a program variable for "self". Take care to register it in the namespaces!
     */
    public LocationVariable selfVar(IProgramMethod pm, KeYJavaType kjt, boolean makeNameUnique) {
        if (pm.isStatic()) {
            return null;
        } else {
            return selfVar(kjt, makeNameUnique);
        }
    }

    /**
     * Creates program variables for the parameters. Take care to register them in the namespaces!
     */
    public ImmutableList<LocationVariable> paramVars(IObserverFunction obs,
            boolean makeNamesUnique) {
        ImmutableList<LocationVariable> result = ImmutableSLList.nil();
        for (int i = 0, n = obs.getNumParams(); i < n; i++) {
            final KeYJavaType paramType = obs.getParamType(i);
            String name;
            if (obs instanceof IProgramMethod) {
                name = ((IProgramMethod) obs).getParameterDeclarationAt(i)
                        .getVariableSpecification().getName();
            } else {
                name = String.valueOf(paramType.getSort().name().toString().charAt(0));
            }
            final LocationVariable paramVar = locationVariable(name, paramType, makeNamesUnique);
            result = result.append(paramVar);
        }
        return result;
    }

    /**
     * Creates program variables for the parameters. Take care to register them in the namespaces!
     */
    public ImmutableList<LocationVariable> paramVars(String postfix, IObserverFunction obs,
            boolean makeNamesUnique) {
        final ImmutableList<LocationVariable> paramVars = paramVars(obs, makeNamesUnique);
        ImmutableList<LocationVariable> result = ImmutableSLList.nil();
        for (LocationVariable paramVar : paramVars) {
            ProgramElementName pen = new ProgramElementName(paramVar.name() + postfix);
            LocationVariable formalParamVar = new LocationVariable(pen, paramVar.getKeYJavaType());
            result = result.append(formalParamVar);
        }
        return result;
    }

    /**
     * Creates a program variable for the result. Take care to register it in the namespaces.
     */
    public LocationVariable resultVar(IProgramMethod pm, boolean makeNameUnique) {
        return resultVar("result", pm, makeNameUnique);
    }

    /**
     * Creates a program variable for the result with passed name. Take care to register it in the
     * namespaces.
     */
    public LocationVariable resultVar(String name, IProgramMethod pm, boolean makeNameUnique) {
        if (pm.isVoid() || pm.isConstructor()) {
            return null;
        } else {
            name += "_" + pm.getName();
            return locationVariable(name, pm.getReturnType(), makeNameUnique);
        }
    }

    /**
     * Creates a program variable for the thrown exception. Take care to register it in the
     * namespaces.
     */
    public LocationVariable excVar(IProgramMethod pm, boolean makeNameUnique) {
        return excVar("exc", pm, makeNameUnique);
    }

    /**
     * Creates a program variable for the thrown exception. Take care to register it in the
     * namespaces.
     */
    public LocationVariable excVar(String name, IProgramMethod pm, boolean makeNameUnique) {
        return locationVariable(name,
            services.getJavaInfo().getTypeByClassName(JAVA_LANG_THROWABLE), makeNameUnique);
    }

    /**
     * Creates a program variable for the atPre heap. Take care to register it in the namespaces.
     */
    public LocationVariable heapAtPreVar(String baseName, boolean makeNameUnique) {
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        return locationVariable(baseName, heapLDT.getHeap().sort(), makeNameUnique);
    }

    /**
     * Creates a location variable for prestate variables. Take care to register it in the
     * namespaces.
     *
     * @param baseName the base name to use
     * @param sort the sort of the variable
     * @param makeNameUnique whether to change the base name to be unique
     * @return a location variable for the given name and type
     */
    public LocationVariable atPreVar(String baseName, Sort sort, boolean makeNameUnique) {
        var kjt = services.getJavaInfo().getKeYJavaType(sort);
        if (kjt == null) {
            kjt = new KeYJavaType(sort);
        }
        return atPreVar(baseName, kjt, makeNameUnique);
    }

    /**
     * Creates a location variable for prestate variables. Take care to register it in the
     * namespaces.
     *
     * @param baseName the base name to use
     * @param kjt the type of the variable
     * @param makeNameUnique whether to change the base name to be unique
     * @return a location variable for the given name and type
     */
    public LocationVariable atPreVar(String baseName, KeYJavaType kjt, boolean makeNameUnique) {
        return locationVariable(baseName + "AtPre", kjt, makeNameUnique);
    }

    /**
     * Creates a location variable for example for prestate variables. Take care to register it in
     * the namespaces.
     *
     * @param baseName the base name to use
     * @param sort the sort of the variable
     * @param makeNameUnique whether to change the base name to be unique
     * @return a location variable for the given name and type
     */
    public LocationVariable locationVariable(String baseName, Sort sort, boolean makeNameUnique) {
        return locationVariable(baseName, new KeYJavaType(sort), makeNameUnique);
    }

    /**
     * Creates a location variable for example for prestate variables. Take care to register it in
     * the namespaces.
     *
     * @param baseName the base name to use
     * @param kjt the type of the variable
     * @param makeNameUnique whether to change the base name to be unique
     * @return a location variable for the given name and type
     */
    public LocationVariable locationVariable(String baseName, KeYJavaType kjt,
            boolean makeNameUnique) {
        if (makeNameUnique) {
            baseName = newName(baseName);
        }
        return new LocationVariable(new ProgramElementName(baseName), kjt);
    }

    // -------------------------------------------------------------------------
    // constructors for special classes of term operators
    // -------------------------------------------------------------------------

    public JTerm var(LogicVariable v) {
        return tf.createTerm(v);
    }

    public JTerm var(ProgramSV v) {
        return tf.createTerm(v);
    }

    public JTerm var(ProgramVariable v) {
        // if(v.isMember()) {
        // throw new TermCreationException(
        // "Cannot create term for \"member\" "
        // + "program variable \"" + v + "\". Use field symbols "
        // + "like your mother told you!");
        // }
        return tf.createTerm(v);
    }

    public ImmutableList<JTerm> var(ProgramVariable... vs) {
        ImmutableList<JTerm> result = ImmutableSLList.nil();
        for (ProgramVariable v : vs) {
            result = result.append(var(v));
        }
        return result;
    }

    public ImmutableList<JTerm> var(Iterable<? extends ProgramVariable> vs) {
        ImmutableList<JTerm> result = ImmutableSLList.nil();
        for (ProgramVariable v : vs) {
            result = result.append(var(v));
        }
        return result;
    }

    public JTerm var(JOperatorSV v) {
        return tf.createTerm(v);
    }

    public JTerm var(VariableSV v) {
        return tf.createTerm(v);
    }

    public JTerm var(Metavariable pMv) {
        return tf.createTerm(pMv);
    }

    // TODO: Inline?
    public JTerm varOfUpdateableOp(UpdateableOperator op) {
        if (op instanceof LocationVariable lv)
            return var(lv);
        return var((ProgramSV) op);
    }

    // TODO: Inline?
    public JTerm varOfQuantVar(QuantifiableVariable op) {
        if (op instanceof LogicVariable lv)
            return var(lv);
        return var((VariableSV) op);
    }

    public JTerm func(Function f) {
        return tf.createTerm(f);
    }

    public JTerm func(Function f, JTerm s) {
        return tf.createTerm(f, s);
    }

    public JTerm func(Function f, JTerm s1, JTerm s2) {
        return tf.createTerm(f, s1, s2);
    }

    public JTerm func(Function f, JTerm... s) {
        return tf.createTerm(f, s);
    }

    public JTerm func(IObserverFunction f, JTerm... s) {
        return tf.createTerm(f, s);
    }

    public JTerm func(Function f, JTerm[] s, ImmutableArray<QuantifiableVariable> boundVars) {
        return tf.createTerm(f, s, boundVars, null);
    }

    // public Term prog(Modality modality, Term t) {
    // return tf.createTerm(modality, new Term[] { t }, null, t.javaBlock());
    // }
    //
    // public Term prog(Modality modality, Term t, ImmutableArray<TermLabel> labels) {
    // return tf.createTerm(modality, new Term[] { t }, null, t.javaBlock(), labels);
    // }

    public JTerm prog(JModality.JavaModalityKind modKind, JavaBlock jb, JTerm t) {
        return tf.createTerm(JModality.getModality(modKind, jb), new JTerm[] { t }, null, null);
    }

    public JTerm prog(JModality.JavaModalityKind modKind, JavaBlock jb, JTerm t,
            ImmutableArray<TermLabel> labels) {
        return tf.createTerm(JModality.getModality(modKind, jb), new JTerm[] { t }, null, labels);
    }

    public JTerm box(JavaBlock jb, JTerm t) {
        return prog(JModality.JavaModalityKind.BOX, jb, t);
    }

    public JTerm dia(JavaBlock jb, JTerm t) {
        return prog(JModality.JavaModalityKind.DIA, jb, t);
    }

    public JTerm ife(JTerm cond, JTerm _then, JTerm _else) {
        return tf.createTerm(IfThenElse.IF_THEN_ELSE, cond, _then, _else);
    }

    /**
     * Construct a term with the \ifEx operator.
     */
    public JTerm ifEx(QuantifiableVariable qv, JTerm cond, JTerm _then, JTerm _else) {
        return tf.createTerm(IfExThenElse.IF_EX_THEN_ELSE,
            new ImmutableArray<>(cond, _then, _else),
            new ImmutableArray<>(qv), null);
    }

    /**
     * Construct a term with the \ifEx operator.
     */
    public JTerm ifEx(ImmutableList<QuantifiableVariable> qvs, JTerm cond, JTerm _then,
            JTerm _else) {
        if (qvs.isEmpty()) {
            throw new TermCreationException("no quantifiable variables in ifEx term");
        }
        if (qvs.size() == 1) {
            return ifEx(qvs.head(), cond, _then, _else);
        } else {
            return ifEx(qvs.head(), tt(), ifEx(qvs.tail(), cond, _then, _else), _else);
        }
    }

    public JTerm cast(Sort s, JTerm t) {
        return tf.createTerm(services.getJavaDLTheory().getCastSymbol(s, services), t);
    }

    public JTerm tt() {
        return tt;
    }

    public JTerm ff() {
        return ff;
    }

    public JTerm all(QuantifiableVariable qv, JTerm t) {
        return tf.createTerm(Quantifier.ALL, new ImmutableArray<>(t),
            new ImmutableArray<>(qv), null);
    }

    public JTerm all(Iterable<QuantifiableVariable> qvs, JTerm t) {
        JTerm result = t;
        for (QuantifiableVariable fv : qvs) {
            result = all(fv, result);
        }
        return result;
    }

    public JTerm allClose(JTerm t) {
        return all(t.freeVars(), t);
    }

    /**
     * Removes universal quantifiers from a formula.
     */
    public JTerm open(JTerm formula) {
        assert formula.sort() == JavaDLTheory.FORMULA;
        if (formula.op() == Quantifier.ALL) {
            return open(formula.sub(0));
        } else {
            return formula;
        }
    }

    public JTerm ex(QuantifiableVariable qv, JTerm t) {
        return tf.createTerm(Quantifier.EX, new ImmutableArray<>(t),
            new ImmutableArray<>(qv), null);
    }

    public JTerm ex(Iterable<QuantifiableVariable> qvs, JTerm t) {
        JTerm result = t;
        for (QuantifiableVariable fv : qvs) {
            result = ex(fv, result);
        }
        return result;
    }

    public JTerm bsum(QuantifiableVariable qv, JTerm a, JTerm b, JTerm t) {
        Function bsum = services.getTypeConverter().getIntegerLDT().getBsum();
        return func(bsum, new JTerm[] { a, b, t }, new ImmutableArray<>(qv));
    }

    /**
     * General (unbounded) sum
     */
    public JTerm sum(ImmutableList<LogicVariable> qvs, JTerm range, JTerm t) {
        final Function sum = services.getNamespaces().functions().lookup("sum");
        final Iterator<LogicVariable> it = qvs.iterator();
        JTerm res = func(sum, new JTerm[] { convertToBoolean(range), t },
            new ImmutableArray<>(it.next()));
        while (it.hasNext()) {
            res = func(sum, new JTerm[] { TRUE(), res }, new ImmutableArray<>(it.next()));
        }
        return res;
    }

    /**
     * Constructs a bounded product comprehension expression.
     */
    public JTerm bprod(QuantifiableVariable qv, JTerm a, JTerm b, JTerm t, Services services) {
        Function bprod = services.getTypeConverter().getIntegerLDT().getBprod();
        return func(bprod, new JTerm[] { a, b, t }, new ImmutableArray<>(qv));
    }

    /**
     * General (unbounded) product
     */
    public JTerm prod(ImmutableList<LogicVariable> qvs, JTerm range, JTerm t,
            TermServices services) {
        final Function prod = services.getNamespaces().functions().lookup("prod");
        final Iterator<LogicVariable> it = qvs.iterator();
        JTerm res = func(prod, new JTerm[] { convertToBoolean(range), t },
            new ImmutableArray<>(it.next()));
        while (it.hasNext()) {
            res = func(prod, new JTerm[] { TRUE(), res },
                new ImmutableArray<>(it.next()));
        }
        return res;
    }

    /**
     * minimum operator
     */
    public JTerm min(ImmutableList<? extends QuantifiableVariable> qvs, JTerm range, JTerm t,
            TermServices services) {
        final Function min = services.getNamespaces().functions().lookup("min");
        final Iterator<? extends QuantifiableVariable> it = qvs.iterator();
        JTerm res = func(min, new JTerm[] { convertToBoolean(range), t },
            new ImmutableArray<>(it.next()));
        while (it.hasNext()) {
            res = func(min, new JTerm[] { TRUE(), res },
                new ImmutableArray<>(it.next()));
        }
        return res;
    }

    /**
     * minimum operator
     */
    public JTerm max(ImmutableList<? extends QuantifiableVariable> qvs, JTerm range, JTerm t,
            TermServices services) {
        final Function max = services.getNamespaces().functions().lookup("max");
        final Iterator<? extends QuantifiableVariable> it = qvs.iterator();
        JTerm res = func(max, new JTerm[] { convertToBoolean(range), t },
            new ImmutableArray<>(it.next()));
        while (it.hasNext()) {
            res = func(max, new JTerm[] { TRUE(), res }, new ImmutableArray<>(it.next()));
        }
        return res;
    }

    public JTerm not(JTerm t) {
        if (t.op() == Junctor.TRUE) {
            return ff();
        } else if (t.op() == Junctor.FALSE) {
            return tt();
        } else if (t.op() == Junctor.NOT) {
            return t.sub(0);
        } else {
            return tf.createTerm(Junctor.NOT, t);
        }
    }

    public JTerm and(JTerm t1, JTerm t2) {
        if (t1.op() == Junctor.FALSE || t2.op() == Junctor.FALSE) {
            return ff();
        } else if (t1.op() == Junctor.TRUE) {
            return t2;
        } else if (t2.op() == Junctor.TRUE) {
            return t1;
        } else {
            return tf.createTerm(Junctor.AND, t1, t2);
        }
    }

    public JTerm andSC(JTerm t1, JTerm t2) {
        if (t1.op() == Junctor.TRUE || t1.op() == Junctor.FALSE || t2.op() == Junctor.FALSE
                || t2.op() == Junctor.TRUE) {
            return and(t1, t2);
        } else {
            return shortcut(and(t1, t2));
        }
    }

    public JTerm and(JTerm... subTerms) {
        JTerm result = tt();
        for (JTerm sub : subTerms) {
            result = and(result, sub);
        }
        return result;
    }

    public JTerm andSC(JTerm... subTerms) {
        JTerm result = tt();
        if (subTerms.length == 1) {
            return and(subTerms);
        }
        for (JTerm sub : subTerms) {
            result = andSC(result, sub);
        }
        return result;
    }

    public JTerm and(Iterable<JTerm> subTerms) {
        JTerm result = tt();
        for (JTerm sub : subTerms) {
            result = and(result, sub);
        }
        return result;
    }

    public JTerm andSC(Iterable<JTerm> subTerms) {
        JTerm result = tt();
        int i = 0;
        for (JTerm sub : subTerms) {
            result = andSC(result, sub);
            i++;
        }
        if (i == 1) {
            return and(subTerms);
        }
        return result;
    }

    public JTerm or(JTerm t1, JTerm t2) {
        if (t1.op() == Junctor.TRUE || t2.op() == Junctor.TRUE) {
            return tt();
        } else if (t1.op() == Junctor.FALSE) {
            return t2;
        } else if (t2.op() == Junctor.FALSE) {
            return t1;
        } else {
            return tf.createTerm(Junctor.OR, t1, t2);
        }
    }

    public JTerm orSC(JTerm t1, JTerm t2) {
        if (t1.op() == Junctor.TRUE || t1.op() == Junctor.FALSE || t2.op() == Junctor.FALSE
                || t2.op() == Junctor.TRUE) {
            return or(t1, t2);
        } else {
            return shortcut(or(t1, t2));
        }
    }

    public JTerm or(JTerm... subTerms) {
        JTerm result = ff();
        for (JTerm sub : subTerms) {
            result = or(result, sub);
        }
        return result;
    }

    public JTerm orSC(JTerm... subTerms) {
        JTerm result = ff();
        if (subTerms.length == 1) {
            return or(subTerms);
        }
        for (JTerm sub : subTerms) {
            result = orSC(result, sub);
        }
        return result;
    }

    public JTerm or(Iterable<JTerm> subTerms) {
        JTerm result = ff();
        for (JTerm sub : subTerms) {
            result = or(result, sub);
        }
        return result;
    }

    public JTerm orSC(Iterable<JTerm> subTerms) {
        JTerm result = ff();
        int i = 0;
        for (JTerm sub : subTerms) {
            result = orSC(result, sub);
            i++;
        }
        if (i == 1) {
            return or(subTerms);
        }
        return result;
    }

    public JTerm imp(JTerm t1, JTerm t2) {
        return imp(t1, t2, null);
    }

    public JTerm imp(JTerm t1, JTerm t2, ImmutableArray<TermLabel> labels) {
        if (t1.op() == Junctor.FALSE || t2.op() == Junctor.TRUE) {
            return tt();
        } else if (t1.op() == Junctor.TRUE) {
            return t2;
        } else if (t2.op() == Junctor.FALSE) {
            return not(t1);
        } else {
            return tf.createTerm(Junctor.IMP, t1, t2, labels);
        }
    }

    /**
     * Creates a term with the correct equality symbol for the sorts involved
     */
    public JTerm equals(JTerm t1, JTerm t2) {
        if (t1.sort() == JavaDLTheory.FORMULA) {
            if (t1.op() == Junctor.TRUE) {
                return t2;
            } else if (t2.op() == Junctor.TRUE) {
                return t1;
            } else if (t1.op() == Junctor.FALSE) {
                return not(t2);
            } else if (t2.op() == Junctor.FALSE) {
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
     *
     * @param substVar the QuantifiableVariable to be substituted
     * @param substTerm the Term that replaces substVar
     * @param origTerm the Term that is substituted
     */
    public JTerm subst(SubstOp op, QuantifiableVariable substVar, JTerm substTerm,
            JTerm origTerm) {
        return tf.createTerm(op, new ImmutableArray<>(substTerm, origTerm),
            new ImmutableArray<>(substVar), null);
    }

    public JTerm subst(QuantifiableVariable substVar, JTerm substTerm, JTerm origTerm) {
        return subst(WarySubstOp.SUBST, substVar, substTerm, origTerm);
    }

    public JTerm instance(Sort s, JTerm t) {
        return equals(func(services.getJavaDLTheory().getInstanceofSymbol(s, services), t), TRUE());
    }

    public JTerm exactInstance(Sort s, JTerm t) {
        return equals(func(services.getJavaDLTheory().getExactInstanceofSymbol(s, services), t),
            TRUE());
    }

    // Functions for wellfoundedness
    // ------------------------------

    public JTerm pair(JTerm first, JTerm second) {
        final Namespace<Function> funcNS = services.getNamespaces().functions();
        final Function f = funcNS.lookup(new Name("pair"));
        if (f == null) {
            throw new RuntimeException("LDT: Function pair not found.\n"
                + "It seems that there are definitions missing from the .key files.");
        }

        return func(f, first, second);

    }

    public JTerm prec(JTerm mby, JTerm mbyAtPre) {
        final Namespace<Function> funcNS = services.getNamespaces().functions();
        final Function f = funcNS.lookup(new Name("prec"));
        if (f == null) {
            throw new RuntimeException("LDT: Function prec not found.\n"
                + "It seems that there are definitions missing from the .key files.");
        }

        return func(f, mby, mbyAtPre);
    }

    public JTerm measuredByCheck(JTerm mby) {
        final Namespace<Function> funcNS = services.getNamespaces().functions();
        final Function f = funcNS.lookup(new Name("measuredByCheck"));
        if (f == null) {
            throw new RuntimeException("LDT: Function measuredByCheck not found.\n"
                + "It seems that there are definitions missing from the .key files.");
        }
        return func(f, mby);
    }

    public JTerm measuredBy(JTerm mby) {
        final Namespace<Function> funcNS = services.getNamespaces().functions();
        final Function f = funcNS.lookup(new Name("measuredBy"));
        if (f == null) {
            throw new RuntimeException("LDT: Function measuredBy not found.\n"
                + "It seems that there are definitions missing from the .key files.");
        }
        return func(f, mby);
    }

    public Function getMeasuredByEmpty() {
        final Namespace<Function> funcNS = services.getNamespaces().functions();
        final Function f = funcNS.lookup(new Name("measuredByEmpty"));
        if (f == null) {
            throw new RuntimeException("LDT: Function measuredByEmpty not found.\n"
                + "It seems that there are definitions missing from the .key files.");
        }
        return f;
    }

    public JTerm measuredByEmpty() {
        return func(getMeasuredByEmpty());
    }

    /**
     * If a is a boolean literal, the method returns the literal as a Formula.
     */
    public JTerm convertToFormula(JTerm a) {
        BooleanLDT booleanLDT = services.getTypeConverter().getBooleanLDT();
        if (booleanLDT == null) {
            throw new IllegalStateException("boolean ldt is not set in services");
        }
        if (a == null) {
            throw new NullPointerException();
        }
        if (a.sort() == JavaDLTheory.FORMULA) {
            return a;
        } else if (a.sort() == booleanLDT.targetSort()) {
            // special case where a is the result of convertToBoolean
            if (a.op() == IfThenElse.IF_THEN_ELSE) {
                assert a.arity() == 3;
                assert a.sub(0).sort() == JavaDLTheory.FORMULA;
                if (a.sub(1).op() == booleanLDT.getTrueConst()
                        && a.sub(2).op() == booleanLDT.getFalseConst()) {
                    return a.sub(0);
                } else if (a.sub(1).op() == booleanLDT.getFalseConst()
                        && a.sub(2).op() == booleanLDT.getTrueConst()) {
                    return not(a.sub(0));
                }
            }
            return equals(a, TRUE());
        } else {
            throw new TermCreationException(
                "Term " + a + " cannot be converted" + " into a formula.");
        }
    }

    /**
     * For a formula a, convert it to a boolean expression.
     */
    public JTerm convertToBoolean(JTerm a) {
        BooleanLDT booleanLDT = services.getTypeConverter().getBooleanLDT();
        if (a.sort() == booleanLDT.targetSort()) {
            return a;
        } else if (a.sort() == JavaDLTheory.FORMULA) {
            // special case where a is the result of convertToFormula
            if (a.op() == Equality.EQUALS && a.sub(1).op() == booleanLDT.getTrueConst()) {
                return a.sub(0);
            }
            return ife(a, TRUE(), FALSE());
        } else {
            throw new TermCreationException(
                "Term " + a + " cannot be converted" + " into a boolean.");
        }
    }

    // -------------------------------------------------------------------------
    // updates
    // -------------------------------------------------------------------------

    public JTerm elementary(UpdateableOperator lhs, JTerm rhs) {
        ElementaryUpdate eu = ElementaryUpdate.getInstance(lhs);
        return tf.createTerm(eu, rhs);
    }

    public JTerm elementary(JTerm lhs, JTerm rhs) {
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        if (lhs.op() instanceof UpdateableOperator updateableOperator) {
            assert lhs.arity() == 0 : "uh oh: " + lhs;
            return elementary(updateableOperator, rhs);
        } else if (heapLDT.getSortOfSelect(lhs.op()) != null
                && lhs.sub(0).op().equals(heapLDT.getHeap())) {
            final JTerm heapTerm = lhs.sub(0);
            final JTerm objectTerm = lhs.sub(1);
            final JTerm fieldTerm = lhs.sub(2);

            final JTerm fullRhs = store(heapTerm, objectTerm, fieldTerm, rhs);
            return elementary(heapLDT.getHeap(), fullRhs);
        } else if (lhs.op() == UpdateApplication.UPDATE_APPLICATION) {
            // #1536 A nested updates like
            // { {a:=1} b :=a}
            // should be parsed as (see KeY-Book, Sec. 3.4.1, Def. 3.8)
            // { {a:=1} (b :=a)}
            // but is parsed as:
            // { ({a:=1} b) :=a}
            // The latter is (currently) not supported, hence the exception.
            throw new TermCreationException("lhs cannot have a nested update. "
                + "If you have a nested update like '{{a:=1} b:=a}', "
                + "replace it with the bracketed version '{{a:=1} (b:=a)}'.");
        } else {
            throw new TermCreationException("Not a legal lhs: " + lhs);
        }
    }

    private JTerm elementary(JTerm heapTerm) {
        return elementary(getBaseHeap(), heapTerm);
    }

    public JTerm skip() {
        return tf.createTerm(UpdateJunctor.SKIP);
    }

    public JTerm parallel(JTerm u1, JTerm u2) {
        if (u1.sort() != JavaDLTheory.UPDATE) {
            throw new TermCreationException("Not an update: " + u1);
        } else if (u2.sort() != JavaDLTheory.UPDATE) {
            throw new TermCreationException("Not an update: " + u2);
        }
        if (u1.op() == UpdateJunctor.SKIP) {
            return u2;
        } else if (u2.op() == UpdateJunctor.SKIP) {
            return u1;
        }
        return tf.createTerm(UpdateJunctor.PARALLEL_UPDATE, u1, u2);
    }

    public JTerm parallel(JTerm... updates) {
        JTerm result = skip();
        for (JTerm update : updates) {
            result = parallel(result, update);
        }
        return result;
    }

    public JTerm parallel(ImmutableList<JTerm> updates) {
        return parallel(updates.toArray(new JTerm[updates.size()]));
    }

    public JTerm parallel(JTerm[] lhss, JTerm[] values) {
        if (lhss.length != values.length) {
            throw new TermCreationException("Tried to create parallel update with " + lhss.length
                + " locs and " + values.length + " values");
        }
        JTerm[] updates = new JTerm[lhss.length];
        for (int i = 0; i < updates.length; i++) {
            updates[i] = elementary(lhss[i], values[i]);
        }
        return parallel(updates);
    }

    public JTerm parallel(Iterable<JTerm> lhss, Iterable<JTerm> values) {
        ImmutableList<JTerm> updates = ImmutableSLList.nil();
        Iterator<JTerm> lhssIt = lhss.iterator();
        Iterator<JTerm> rhssIt = values.iterator();
        while (lhssIt.hasNext()) {
            assert rhssIt.hasNext();
            updates = updates.append(elementary(lhssIt.next(), rhssIt.next()));
        }
        return parallel(updates);
    }

    public JTerm sequential(JTerm u1, JTerm u2) {
        return parallel(u1, apply(u1, u2, null));
    }

    public JTerm sequential(JTerm[] updates) {
        if (updates.length == 0) {
            return skip();
        } else {
            JTerm result = updates[updates.length - 1];
            for (int i = updates.length - 2; i >= 0; i--) {
                result = sequential(updates[i], result);
            }
            return result;
        }
    }

    public JTerm sequential(ImmutableList<JTerm> updates) {
        if (updates.isEmpty()) {
            return skip();
        } else if (updates.size() == 1) {
            return updates.head();
        } else {
            return sequential(updates.head(), sequential(updates.tail()));
        }
    }

    public JTerm apply(JTerm update, JTerm target) {
        return apply(update, target, null);
    }

    public ImmutableList<JTerm> apply(JTerm update, ImmutableList<JTerm> targets) {
        ImmutableList<JTerm> result = ImmutableSLList.nil();
        for (JTerm target : targets) {
            result = result.append(apply(update, target));
        }
        return result;
    }

    public JTerm apply(JTerm update, JTerm target, ImmutableArray<TermLabel> labels) {
        if (update.sort() != JavaDLTheory.UPDATE) {
            throw new TermCreationException("Not an update: " + update);
        } else if (update.op() == UpdateJunctor.SKIP) {
            return target;
        } else if (target.equals(tt())) {
            return tt();
        } else {
            return tf.createTerm(UpdateApplication.UPDATE_APPLICATION, update, target, labels);
        }
    }

    public JTerm applyElementary(JTerm loc, JTerm value, JTerm target) {
        return apply(elementary(loc, value), target, null);
    }

    public JTerm applyElementary(JTerm heap, JTerm target) {
        return apply(elementary(heap), target, null);
    }

    public ImmutableList<JTerm> applyElementary(JTerm heap, Iterable<JTerm> targets) {
        ImmutableList<JTerm> result = ImmutableSLList.nil();
        for (JTerm target : targets) {
            result = result.append(apply(elementary(heap), target, null));
        }
        return result;
    }

    public JTerm applyParallel(JTerm[] updates, JTerm target) {
        return apply(parallel(updates), target, null);
    }

    public JTerm applyParallel(ImmutableList<JTerm> updates, JTerm target) {
        return apply(parallel(updates), target, null);
    }

    public JTerm applyParallel(ImmutableList<JTerm> updates, JTerm target,
            ImmutableArray<TermLabel> labels) {
        return apply(parallel(updates), target, labels);
    }

    public JTerm applyParallel(JTerm[] lhss, JTerm[] values, JTerm target) {
        return apply(parallel(lhss, values), target, null);
    }

    public JTerm applySequential(JTerm[] updates, JTerm target) {
        if (updates.length == 0) {
            return target;
        } else {
            ImmutableList<JTerm> updateList = ImmutableSLList.<JTerm>nil().append(updates).tail();
            return apply(updates[0], applySequential(updateList, target), null);
        }
    }

    public JTerm applySequential(ImmutableList<JTerm> updates, JTerm target) {
        if (updates.isEmpty()) {
            return target;
        } else {
            return apply(updates.head(), applySequential(updates.tail(), target), null);
        }
    }

    public JTerm applyUpdatePairsSequential(ImmutableList<UpdateLabelPair> updates, JTerm target) {
        if (updates.isEmpty()) {
            return target;
        } else {
            return apply(updates.head().update(),
                applyUpdatePairsSequential(updates.tail(), target),
                updates.head().updateApplicationlabels());
        }
    }

    // -------------------------------------------------------------------------
    // boolean operators
    // -------------------------------------------------------------------------

    public JTerm TRUE() {
        return services.getTypeConverter().getBooleanLDT().getTrueTerm();
    }

    public JTerm FALSE() {
        return services.getTypeConverter().getBooleanLDT().getFalseTerm();
    }

    // -------------------------------------------------------------------------
    // integer operators
    // -------------------------------------------------------------------------

    public JTerm geq(JTerm t1, JTerm t2) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return func(integerLDT.getGreaterOrEquals(), t1, t2);
    }

    public JTerm gt(JTerm t1, JTerm t2) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return func(integerLDT.getGreaterThan(), t1, t2);
    }

    public JTerm lt(JTerm t1, JTerm t2) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return func(integerLDT.getLessThan(), t1, t2);
    }

    public JTerm leq(JTerm t1, JTerm t2) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return func(integerLDT.getLessOrEquals(), t1, t2);
    }

    public JTerm zero() {
        return services.getTypeConverter().getIntegerLDT().zero();
    }

    public JTerm one() {
        return services.getTypeConverter().getIntegerLDT().one();
    }

    /**
     * Creates terms to be used in Z/C/FP/DFP/R notations. The result does not have such a
     * constructor applied yet.
     *
     * @param numberString a string containing the number in a decimal representation
     * @return Term in "number" notation representing the given number
     * @throws NumberFormatException if <code>numberString</code> is not a number
     */
    private JTerm numberTerm(String numberString) {
        if (numberString == null || numberString.isEmpty()) {
            throw new NumberFormatException(numberString + " is not a number.");
        }

        JTerm numberLiteralTerm;
        boolean negate = false;
        int j = 0;

        final IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();

        if (numberString.charAt(0) == '-') {
            negate = true;
            j = 1;
        }
        numberLiteralTerm = func(intLDT.getNumberTerminator());

        int digit;
        for (int i = j, sz = numberString.length(); i < sz; i++) {
            char c = numberString.charAt(i);
            if ('0' <= c && c <= '9') {
                digit = c - '0';
            } else {
                throw new NumberFormatException(numberString + " is not a number.");
            }
            numberLiteralTerm = func(intLDT.getNumberLiteralFor(digit), numberLiteralTerm);
        }
        if (negate) {
            numberLiteralTerm = func(intLDT.getNegativeNumberSign(), numberLiteralTerm);
        }

        // return the raw number literal term ('C', 'Z' or 'R' must still be added)
        return numberLiteralTerm;
    }

    /**
     * Get term for an integer literal.
     *
     * @param numberString String representing an integer with radix 10, may be negative
     * @return Term in Z-Notation representing the given number
     * @throws NumberFormatException if <code>numberString</code> is not a number
     */
    public JTerm zTerm(String numberString) {
        return func(services.getTypeConverter().getIntegerLDT().getNumberSymbol(),
            numberTerm(numberString));
    }

    /**
     * Get term for an integer literal.
     *
     * @param number an integer
     * @return Term in Z-Notation representing the given number
     */
    public JTerm zTerm(long number) {
        return zTerm(Long.toString(number));
    }

    /**
     * @param numberString String containing the value of the char as a decimal number
     * @return Term in C-Notation representing the given char
     * @throws NumberFormatException if <code>numberString</code> is not a number
     */
    public JTerm cTerm(String numberString) {
        return func(services.getTypeConverter().getIntegerLDT().getCharSymbol(),
            numberTerm(numberString));
    }

    /**
     * Create a floating point literal value from a float value.
     *
     * @param value any float value (even NaN)
     * @return a term representing the value
     */
    public JTerm fpTerm(float value) {
        int bitPattern = Float.floatToIntBits(value);
        String patternStr = Integer.toUnsignedString(bitPattern);
        JTerm numberTerm = numberTerm(patternStr);
        return func(services.getTypeConverter().getFloatLDT().getFloatSymbol(), numberTerm);
    }

    /**
     * Create a double floating point literal value from a double value.
     *
     * @param value any double value (even NaN)
     * @return a term representing the value
     */
    public JTerm dfpTerm(double value) {
        long bitPattern = Double.doubleToLongBits(value);
        String patternStr = Long.toUnsignedString(bitPattern);
        JTerm numberTerm = numberTerm(patternStr);
        return func(services.getTypeConverter().getDoubleLDT().getDoubleSymbol(), numberTerm);
    }

    public JTerm add(JTerm t1, JTerm t2) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        final JTerm zero = integerLDT.zero();
        if (t1.equals(zero)) {
            return t2;
        } else if (t2.equals(zero)) {
            return t1;
        } else {
            return func(integerLDT.getAdd(), t1, t2);
        }
    }

    public JTerm inByte(JTerm var) {
        Function f = services.getNamespaces().functions().lookup(new Name("inByte"));
        return func(f, var);
    }

    public JTerm inShort(JTerm var) {
        Function f = services.getNamespaces().functions().lookup(new Name("inShort"));
        return func(f, var);
    }

    public JTerm inChar(JTerm var) {
        Function f = services.getNamespaces().functions().lookup(new Name("inChar"));
        return func(f, var);
    }

    public JTerm inInt(JTerm var) {
        Function f = services.getNamespaces().functions().lookup(new Name("inInt"));
        return func(f, var);
    }

    public JTerm inLong(JTerm var) {
        Function f = services.getNamespaces().functions().lookup(new Name("inLong"));
        return func(f, var);
    }

    public JTerm index() {
        return func(services.getTypeConverter().getIntegerLDT().getIndex());
    }

    // -------------------------------------------------------------------------
    // location set operators
    // -------------------------------------------------------------------------

    /**
     * This value is only used as a marker for "\strictly_nothing" in JML. It may return any term.
     * Preferably of type LocSet, but this is not necessary.
     *
     * @return an arbitrary but fixed term.
     */
    public JTerm strictlyNothing() {
        return ff();
    }

    public JTerm empty() {
        return func(services.getTypeConverter().getLocSetLDT().getEmpty());
    }

    public JTerm allLocs() {
        return func(services.getTypeConverter().getLocSetLDT().getAllLocs());
    }

    public JTerm singleton(JTerm o, JTerm f) {
        return func(services.getTypeConverter().getLocSetLDT().getSingleton(), o, f);
    }

    public JTerm union(JTerm s1, JTerm s2) {
        final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
        if (s1.op() == ldt.getEmpty()) {
            return s2;
        } else if (s2.op() == ldt.getEmpty()) {
            return s1;
        } else {
            return func(ldt.getUnion(), s1, s2);
        }
    }

    public JTerm union(JTerm... subTerms) {
        JTerm result = empty();
        for (JTerm sub : subTerms) {
            result = union(result, sub);
        }
        return result;
    }

    public JTerm union(Iterable<JTerm> subTerms) {
        JTerm result = empty();
        for (JTerm sub : subTerms) {
            result = union(result, sub);
        }
        return result;
    }

    public JTerm intersect(JTerm s1, JTerm s2) {
        final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
        if (s1.op() == ldt.getEmpty() || s2.op() == ldt.getEmpty()) {
            return empty();
        } else if (s1.op() == ldt.getAllLocs()) {
            return s2;
        } else if (s2.op() == ldt.getAllLocs()) {
            return s1;
        } else {
            return func(ldt.getIntersect(), s1, s2);
        }
    }

    public JTerm intersect(JTerm... subTerms) {
        JTerm result = allLocs();
        for (JTerm sub : subTerms) {
            result = intersect(result, sub);
        }
        return result;
    }

    public JTerm intersect(Iterable<JTerm> subTerms) {
        JTerm result = allLocs();
        for (JTerm sub : subTerms) {
            result = intersect(result, sub);
        }
        return result;
    }

    public JTerm setMinus(JTerm s1, JTerm s2) {
        final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
        if (s1.op() == ldt.getEmpty() || s2.op() == ldt.getEmpty()) {
            return s1;
        } else {
            return func(ldt.getSetMinus(), s1, s2);
        }
    }

    public JTerm infiniteUnion(QuantifiableVariable[] qvs, JTerm s) {
        final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
        return tf.createTerm(ldt.getInfiniteUnion(), new JTerm[] { s },
            new ImmutableArray<>(qvs), null);
    }

    public JTerm infiniteUnion(QuantifiableVariable[] qvs, JTerm guard, JTerm s) {
        return infiniteUnion(qvs, ife(guard, s, empty()));
    }

    public JTerm setComprehension(QuantifiableVariable[] qvs, JTerm o, JTerm f) {
        return infiniteUnion(qvs, singleton(o, f));
    }

    public JTerm setComprehension(QuantifiableVariable[] qvs, JTerm guard, JTerm o, JTerm f) {
        return infiniteUnion(qvs, guard, singleton(o, f));
    }

    public JTerm allFields(JTerm o) {
        return func(services.getTypeConverter().getLocSetLDT().getAllFields(), o);
    }

    public JTerm allObjects(JTerm f) {
        return func(services.getTypeConverter().getLocSetLDT().getAllObjects(), f);
    }

    public JTerm arrayRange(JTerm o, JTerm lower, JTerm upper) {
        return func(services.getTypeConverter().getLocSetLDT().getArrayRange(), o, lower, upper);
    }

    public JTerm freshLocs(JTerm h) {
        return func(services.getTypeConverter().getLocSetLDT().getFreshLocs(), h);
    }

    public JTerm elementOf(JTerm o, JTerm f, JTerm s) {
        final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
        if (s.op() == ldt.getEmpty()) {
            return ff();
        } else {
            return func(ldt.getElementOf(), o, f, s);
        }
    }

    public JTerm subset(JTerm s1, JTerm s2) {
        final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
        if (s1.op() == ldt.getEmpty()) {
            return tt();
        } else {
            return func(ldt.getSubset(), s1, s2);
        }
    }

    public JTerm disjoint(JTerm s1, JTerm s2) {
        final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
        if (s1.op() == ldt.getEmpty() || s2.op() == ldt.getEmpty()) {
            return tt();
        } else {
            return func(ldt.getDisjoint(), s1, s2);
        }
    }

    public JTerm createdInHeap(JTerm s, JTerm h) {
        final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
        if (s.op() == ldt.getEmpty()) {
            return tt();
        } else {
            return func(ldt.getCreatedInHeap(), s, h);
        }
    }

    public JTerm createdLocs() {
        return setMinus(allLocs(), freshLocs(getBaseHeap()));
    }

    // The template of the well-definedness transformer for terms.
    public static final Transformer WD_ANY = new Transformer(new Name("wd"), JavaDLTheory.ANY);

    // The template of the well-definedness transformer for formulas.
    public static final Transformer WD_FORMULA =
        new Transformer(new Name("WD"), JavaDLTheory.FORMULA);

    public JTerm wd(JTerm t) {
        if (t.op() == Junctor.FALSE || t.op() == Junctor.TRUE) {
            return tt();
        } else if (t.sort().equals(JavaDLTheory.FORMULA)) {
            return func(Transformer.getTransformer(WD_FORMULA, services), t);
        } else {
            return func(Transformer.getTransformer(WD_ANY, services), t);
        }
    }

    public ImmutableList<JTerm> wd(Iterable<JTerm> l) {
        ImmutableList<JTerm> res = ImmutableSLList.nil();
        for (JTerm t : l) {
            res = res.append(wd(t));
        }
        return res;
    }

    public JTerm[] wd(JTerm[] l) {
        JTerm[] res = new JTerm[l.length];
        for (int i = 0; i < l.length; i++) {
            res[i] = wd(l[i]);
        }
        return res;
    }

    // -------------------------------------------------------------------------
    // heap operators
    // -------------------------------------------------------------------------

    public JTerm NULL() {
        return func(services.getTypeConverter().getHeapLDT().getNull());
    }

    /**
     * The "deep non null" predicate arising from JML non_null types. Deep non null means that it is
     * recursively defined for arrays. See bug #1392.
     */
    public JTerm deepNonNull(JTerm o, JTerm d) {
        final Function nonNull = services.getNamespaces().functions().lookup("nonNull");
        final JTerm heap = getBaseHeap();
        return func(nonNull, heap, o, d);
    }

    public JTerm wellFormed(JTerm heap) {
        return func(services.getTypeConverter().getHeapLDT().getWellFormed(), heap);
    }

    public JTerm wellFormed(LocationVariable heap) {
        return wellFormed(var(heap));
    }

    public JTerm permissionsFor(JTerm permHeap, JTerm regularHeap) {
        return func(services.getTypeConverter().getPermissionLDT().getPermissionsFor(), permHeap,
            regularHeap);
    }

    public JTerm permissionsFor(LocationVariable permHeap, LocationVariable regularHeap) {
        return permissionsFor(var(permHeap), var(regularHeap));
    }

    public JTerm inv(JTerm[] h, JTerm o) {
        JTerm[] p = new JTerm[h.length + 1];
        System.arraycopy(h, 0, p, 0, h.length);
        p[h.length] = o;
        return func(services.getJavaInfo().getInv(), p);
    }

    public JTerm inv(JTerm o) {
        List<LocationVariable> heaps = HeapContext.getModifiableHeaps(services, false);
        JTerm[] hs = new JTerm[heaps.size()];
        int i = 0;
        for (LocationVariable heap : heaps) {
            hs[i++] = var(heap);
        }
        return inv(hs, o);
    }

    public JTerm staticInv(JTerm[] h, KeYJavaType t) {
        return func(services.getJavaInfo().getStaticInv(t), h);
    }

    public JTerm staticInv(KeYJavaType t) {
        List<LocationVariable> heaps = HeapContext.getModifiableHeaps(services, false);
        JTerm[] hs = new JTerm[heaps.size()];
        int i = 0;
        for (LocationVariable heap : heaps) {
            hs[i++] = var(heap);
        }
        return func(services.getJavaInfo().getStaticInv(t), hs);
    }

    public JTerm invFree(JTerm[] h, JTerm o) {
        JTerm[] p = new JTerm[h.length + 1];
        System.arraycopy(h, 0, p, 0, h.length);
        p[h.length] = o;
        return func(services.getJavaInfo().getInvFree(), p);
    }

    public JTerm invFree(JTerm o) {
        List<LocationVariable> heaps = HeapContext.getModifiableHeaps(services, false);
        JTerm[] hs = new JTerm[heaps.size()];
        int i = 0;
        for (LocationVariable heap : heaps) {
            hs[i++] = var(heap);
        }
        return invFree(hs, o);
    }

    public JTerm staticInvFree(JTerm[] h, KeYJavaType t) {
        return func(services.getJavaInfo().getStaticInvFree(t), h);
    }

    public JTerm staticInvFree(KeYJavaType t) {
        List<LocationVariable> heaps = HeapContext.getModifiableHeaps(services, false);
        JTerm[] hs = new JTerm[heaps.size()];
        int i = 0;
        for (LocationVariable heap : heaps) {
            hs[i++] = var(heap);
        }
        return func(services.getJavaInfo().getStaticInvFree(t), hs);
    }

    public JTerm select(Sort asSort, JTerm h, JTerm o, JTerm f) {
        return func(services.getTypeConverter().getHeapLDT().getSelect(asSort, services), h, o, f);
    }

    /**
     * Get the select expression for a location variabe representing the field.
     */
    public JTerm select(Sort asSort, JTerm h, JTerm o, LocationVariable field) {
        final Function f =
            services.getTypeConverter().getHeapLDT().getFieldSymbolForPV(field, services);
        return select(asSort, h, o, func(f));
    }

    public JTerm dot(Sort asSort, JTerm o, JTerm f) {
        return select(asSort, getBaseHeap(), o, f);
    }

    public JTerm getBaseHeap() {
        return var((LocationVariable) services.getNamespaces().programVariables()
                .lookup(HeapLDT.BASE_HEAP_NAME));
        // return var(services.getTypeConverter().getHeapLDT().getHeap());
    }

    public JTerm dot(Sort asSort, JTerm o, Function f) {
        final Sort fieldSort = services.getTypeConverter().getHeapLDT().getFieldSort();
        return f.sort() == fieldSort ? dot(asSort, o, func(f)) : func(f, getBaseHeap(), o);
    }

    public JTerm dot(Sort asSort, JTerm o, LocationVariable field) {
        final Function f =
            services.getTypeConverter().getHeapLDT().getFieldSymbolForPV(field, services);
        return dot(asSort, o, f);
    }

    public JTerm staticDot(Sort asSort, JTerm f) {
        return dot(asSort, NULL(), f);
    }

    public JTerm staticDot(Sort asSort, Function f) {
        final Sort fieldSort = services.getTypeConverter().getHeapLDT().getFieldSort();
        return f.sort() == fieldSort ? staticDot(asSort, func(f)) : func(f, getBaseHeap());
    }

    /**
     * Get a term for accessing a final field.
     * This can be used for ordinary fields and model fields.
     * The results are quite different!
     *
     * @param sort the sort of the result.
     * @param o the object to access
     * @param f the field to access
     * @return the term representing the access "o.f"
     * @see #finalDot(Sort, JTerm, JTerm) for accessing final Java or ghost fields
     * @see #dot(Sort, JTerm, Function) for accessing final model fields
     */
    public JTerm finalDot(Sort sort, JTerm o, Function f) {
        final Sort fieldSort = services.getTypeConverter().getHeapLDT().getFieldSort();
        return f.sort() == fieldSort ? finalDot(sort, o, func(f))
                : func(f, getBaseHeap(), o);
    }

    /**
     * Get a term for accessing a static final field.
     * This can be used for ordinary fields.
     *
     * @param sort the sort of the result.
     * @param f the field to access
     * @return the term representing the static access "C.f"
     * @see #finalDot(Sort, JTerm, JTerm) for accessing final Java or ghost fields
     * @see #dot(Sort, JTerm, Function) for accessing final model fields
     */
    public JTerm staticFinalDot(Sort sort, Function f) {
        final Sort fieldSort = services.getTypeConverter().getHeapLDT().getFieldSort();
        return f.sort() == fieldSort ? finalDot(sort, NULL(), func(f))
                : func(f, getBaseHeap(), NULL());
    }

    /**
     * Final fields can be treated differently outside the heap.
     * This methods creates a heap-independent read access to final field.
     *
     * @param asSort the sort of the result.
     * @param o the object to access
     * @param f the field to access
     * @return the term representing the access "o.f"
     */
    public JTerm finalDot(Sort asSort, JTerm o, JTerm f) {
        return func(services.getTypeConverter().getHeapLDT().getFinal(asSort, services),
            o, f);
    }

    public JTerm arr(JTerm idx) {
        return func(services.getNamespaces().functions().lookup("arr"), idx);
        // return func(services.getTypeConverter().getHeapLDT().getArr(), idx);
    }

    /**
     * Applies the labels to the term and almost every (direct or indirect) sub-term recursively.
     *
     * <p>
     * The labels are not added to heap variables.
     * </p>
     *
     * @param term term to label.
     * @param labels the labels to apply.
     * @return a labeled term.
     */
    public JTerm addLabelToAllSubs(JTerm term, ImmutableArray<TermLabel> labels) {
        if (labels == null || labels.isEmpty() || (!OriginTermLabel.canAddLabel(term, services)
                && labels.stream().anyMatch(l -> l instanceof OriginTermLabel))) {
            return term;
        }

        ImmutableArray<JTerm> oldSubs = term.subs();
        JTerm[] newSubs = new JTerm[oldSubs.size()];

        for (int i = 0; i < newSubs.length; ++i) {
            newSubs[i] = addLabelToAllSubs(oldSubs.get(i), labels);
        }


        JTerm result =
            tf.createTerm(term.op(), newSubs, term.boundVars(), term.getLabels());
        result = addLabel(result, labels);
        return result;
    }

    /**
     * Applies the label to the term and almost every (direct or indirect) sub-term recursively.
     *
     * <p>
     * The label is not added to heap variables.
     * </p>
     *
     * @param term term to label.
     * @param label the label to apply.
     * @return a labeled term.
     */
    public JTerm addLabelToAllSubs(JTerm term, TermLabel label) {
        return addLabelToAllSubs(term, new ImmutableArray<>(label));
    }

    /**
     * Adds labels to a term, removing any existing labels of the same type.
     *
     * @param term the term.
     * @param labels the labels to add.
     * @return the term with the labels added.
     */
    public JTerm addLabel(JTerm term, ImmutableArray<TermLabel> labels) {
        if ((labels == null || labels.isEmpty()) && !term.hasLabels()) {
            return term;
        } else if (!term.hasLabels()) {
            return tf.createTerm(term.op(), term.subs(), term.boundVars(),
                labels);
        } else {
            List<TermLabel> newLabelList = term.getLabels().toList();

            if (labels != null && !labels.isEmpty()) {
                for (TermLabel newLabel : labels) {
                    for (TermLabel oldLabel : term.getLabels()) {
                        if (oldLabel.equals(newLabel) || (oldLabel.getClass() == newLabel.getClass()
                                && oldLabel instanceof OriginTermLabel)) {
                            newLabelList.remove(oldLabel);
                            break;
                        }
                    }
                    newLabelList.add(newLabel);
                }
            }

            return tf.createTerm(term.op(), term.subs(), term.boundVars(),
                new ImmutableArray<>(newLabelList));
        }
    }

    /**
     * Adds a label to a term, removing any existing labels of the same type.
     *
     * @param term the term.
     * @param label the label to add.
     * @return the term with the label added.
     */
    public JTerm addLabel(JTerm term, TermLabel label) {
        if (label == null && !term.hasLabels()) {
            return term;
        } else {
            return addLabel(term, new ImmutableArray<>(label));
        }
    }

    /**
     * Applies labels to a term, removing any existing labels.
     *
     * @param term the term.
     * @param labels the labels to apply.
     * @return the modified term.
     */
    public JTerm label(JTerm term, ImmutableArray<TermLabel> labels) {
        if ((labels == null || labels.isEmpty())) {
            return term;
        } else {
            return tf.createTerm(term.op(), term.subs(), term.boundVars(),
                labels);
        }
    }

    /**
     * Applies a label to a term, removing any existing labels.
     *
     * @param term the term.
     * @param label the label to apply.
     * @return the modified term.
     */
    public JTerm label(JTerm term, TermLabel label) {
        if (label == null) {
            return term;
        } else {
            return label(term, new ImmutableArray<>(label));
        }
    }

    public JTerm shortcut(JTerm term) {
        return addLabel(term, ParameterlessTermLabel.SHORTCUT_EVALUATION_LABEL);
    }

    public JTerm unlabel(JTerm term) {
        return tf.createTerm(term.op(), term.subs(), term.boundVars());
    }

    public JTerm unlabelRecursive(JTerm term) {
        JTerm[] subs = new JTerm[term.arity()];
        for (int i = 0; i < subs.length; i++) {
            subs[i] = unlabelRecursive(term.sub(i));
        }
        return tf.createTerm(term.op(), subs, term.boundVars(), null);
    }

    public JTerm dotArr(JTerm ref, JTerm idx) {
        if (ref == null || idx == null) {
            throw new TermCreationException(
                "Tried to build an array access " + "term without providing an "
                    + (ref == null ? "array reference." : "index.") + "(" + ref + "[" + idx + "])");
        }

        final Sort elementSort;
        if (ref.sort() instanceof ArraySort) {
            elementSort = ((ArraySort) ref.sort()).elementSort();
        } else {
            throw new TermCreationException(String.format(
                "Tried to build an array access on an inacceptable sort: "
                    + "Sort: %s : %s with %s[%s] ",
                ref.sort(), ref.sort().getClass().getSimpleName(), ref, idx));
        }

        return select(elementSort, getBaseHeap(), ref, arr(idx));
    }

    public JTerm dotLength(JTerm a) {
        final TypeConverter tc = services.getTypeConverter();
        return func(tc.getHeapLDT().getLength(), a);
    }

    public JTerm created(JTerm h, JTerm o) {
        final TypeConverter tc = services.getTypeConverter();
        return equals(
            select(tc.getBooleanLDT().targetSort(), h, o, func(tc.getHeapLDT().getCreated())),
            TRUE());
    }

    public JTerm created(JTerm o) {
        return created(getBaseHeap(), o);
    }

    public JTerm initialized(JTerm o) {
        final TypeConverter tc = services.getTypeConverter();
        return equals(dot(tc.getBooleanLDT().targetSort(), o, tc.getHeapLDT().getInitialized()),
            TRUE());
    }

    public JTerm classPrepared(Sort classSort) {
        final TypeConverter tc = services.getTypeConverter();
        return equals(staticDot(tc.getBooleanLDT().targetSort(),
            tc.getHeapLDT().getClassPrepared(classSort, services)), TRUE());
    }

    public JTerm classInitialized(Sort classSort) {
        final TypeConverter tc = services.getTypeConverter();
        return equals(staticDot(tc.getBooleanLDT().targetSort(),
            tc.getHeapLDT().getClassInitialized(classSort, services)), TRUE());
    }

    public JTerm classInitializationInProgress(Sort classSort) {
        final TypeConverter tc = services.getTypeConverter();
        return equals(staticDot(tc.getBooleanLDT().targetSort(),
            tc.getHeapLDT().getClassInitializationInProgress(classSort, services)), TRUE());
    }

    public JTerm classErroneous(Sort classSort) {
        final TypeConverter tc = services.getTypeConverter();
        return equals(staticDot(tc.getBooleanLDT().targetSort(),
            tc.getHeapLDT().getClassErroneous(classSort, services)), TRUE());
    }

    public JTerm store(JTerm h, JTerm o, JTerm f, JTerm v) {
        return func(services.getTypeConverter().getHeapLDT().getStore(), h, o, f, v);
    }

    public JTerm create(JTerm h, JTerm o) {
        return func(services.getTypeConverter().getHeapLDT().getCreate(), new JTerm[] { h, o });
    }

    public JTerm anon(JTerm h1, JTerm s, JTerm h2) {
        return func(services.getTypeConverter().getHeapLDT().getAnon(), h1, s, h2);
    }

    public JTerm fieldStore(TermServices services, JTerm o, Function f, JTerm v) {
        return store(getBaseHeap(), o, func(f), v);
    }

    public JTerm staticFieldStore(Function f, JTerm v) {
        return fieldStore(services, NULL(), f, v);
    }

    public JTerm arrayStore(JTerm o, JTerm i, JTerm v) {
        return store(getBaseHeap(), o, func(services.getTypeConverter().getHeapLDT().getArr(), i),
            v);
    }

    public JTerm reachableValue(JTerm h, JTerm t, KeYJavaType kjt) {
        assert t.sort().extendsTrans(kjt.getSort()) || t.sort() instanceof ProgramSVSort;
        final Sort s = t.sort() instanceof ProgramSVSort ? kjt.getSort() : t.sort();
        final IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();
        final LocSetLDT setLDT = services.getTypeConverter().getLocSetLDT();
        if (s.extendsTrans(services.getJavaInfo().objectSort())) {
            return orSC(equals(t, NULL()), created(h, t));
        } else if (s.equals(setLDT.targetSort())) {
            return createdInHeap(t, h);
        } else if (s.equals(intLDT.targetSort())
                && kjt.getJavaType() != PrimitiveType.JAVA_BIGINT) {
            return func(intLDT.getInBounds(kjt.getJavaType()), t);
        } else {
            return tt();
        }
    }

    public JTerm reachableValue(JTerm t, KeYJavaType kjt) {
        return reachableValue(getBaseHeap(), t, kjt);
    }

    public JTerm reachableValue(LocationVariable pv) {
        return reachableValue(var(pv), pv.getKeYJavaType());
    }

    public JTerm frame(JTerm heapTerm, Map<JTerm, JTerm> normalToAtPre, JTerm modifiable) {
        final Sort objectSort = services.getJavaInfo().objectSort();
        final Sort fieldSort = services.getTypeConverter().getHeapLDT().getFieldSort();

        final Name objVarName = new Name(newName("o"));
        final Name fieldVarName = new Name(newName("f"));
        final LogicVariable objVar = new LogicVariable(objVarName, objectSort);
        final LogicVariable fieldVar = new LogicVariable(fieldVarName, fieldSort);
        final JTerm objVarTerm = var(objVar);
        final JTerm fieldVarTerm = var(fieldVar);

        final OpReplacer or = new OpReplacer(normalToAtPre, tf);
        final JTerm modifiableAtPre = or.replace(modifiable);
        final JTerm createdAtPre = or.replace(created(heapTerm, objVarTerm));

        ImmutableList<QuantifiableVariable> quantVars = ImmutableSLList.nil();
        quantVars = quantVars.append(objVar);
        quantVars = quantVars.append(fieldVar);
        // selects on permission heaps have to be explicitly typed as field type
        // narrowing
        // does not follow Java typing for the permission heap
        boolean permissionHeap =
            heapTerm.op() == services.getTypeConverter().getHeapLDT().getPermissionHeap();
        return all(quantVars, or(elementOf(objVarTerm, fieldVarTerm, modifiableAtPre),
            and(not(equals(objVarTerm, NULL())), not(createdAtPre)),
            equals(
                select(permissionHeap ? services.getTypeConverter().getPermissionLDT().targetSort()
                        : JavaDLTheory.ANY,
                    heapTerm, objVarTerm, fieldVarTerm),
                select(permissionHeap ? services.getTypeConverter().getPermissionLDT().targetSort()
                        : JavaDLTheory.ANY,
                    or.replace(heapTerm), objVarTerm, fieldVarTerm))));
    }

    /**
     * Returns the framing condition that the resulting heap is identical (i.e. has the same value
     * in all locations) to the before-heap.
     *
     * @see #frame(JTerm, Map, JTerm)
     */
    public JTerm frameStrictlyEmpty(JTerm heapTerm, Map<JTerm, JTerm> normalToAtPre) {
        final Sort objectSort = services.getJavaInfo().objectSort();
        final Sort fieldSort = services.getTypeConverter().getHeapLDT().getFieldSort();

        final Name objVarName = new Name(newName("o"));
        final Name fieldVarName = new Name(newName("f"));
        final LogicVariable objVar = new LogicVariable(objVarName, objectSort);
        final LogicVariable fieldVar = new LogicVariable(fieldVarName, fieldSort);
        final JTerm objVarTerm = var(objVar);
        final JTerm fieldVarTerm = var(fieldVar);

        final OpReplacer or = new OpReplacer(normalToAtPre, tf);

        ImmutableList<QuantifiableVariable> quantVars = ImmutableSLList.nil();
        quantVars = quantVars.append(objVar);
        quantVars = quantVars.append(fieldVar);

        // see above
        boolean permissionHeap =
            heapTerm.op() == services.getTypeConverter().getHeapLDT().getPermissionHeap();

        return all(quantVars,
            equals(
                select(permissionHeap ? services.getTypeConverter().getPermissionLDT().targetSort()
                        : JavaDLTheory.ANY,
                    heapTerm, objVarTerm, fieldVarTerm),
                select(permissionHeap ? services.getTypeConverter().getPermissionLDT().targetSort()
                        : JavaDLTheory.ANY,
                    or.replace(heapTerm), objVarTerm, fieldVarTerm)));
    }

    public JTerm anonUpd(LocationVariable heap, JTerm modifiable, JTerm anonHeap) {
        return elementary(heap, anon(var(heap), modifiable, anonHeap));
    }

    public JTerm forallHeaps(Services services, JTerm t) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final LogicVariable heapLV = new LogicVariable(new Name("h"), heapLDT.targetSort());
        final Map<LocationVariable, LogicVariable> map = new LinkedHashMap<>();
        map.put(heapLDT.getHeap(), heapLV);
        final OpReplacer or = new OpReplacer(map, tf);
        t = or.replace(t);
        return all(heapLV, t);
    }

    // -------------------------------------------------------------------------
    // reachability operators
    // -------------------------------------------------------------------------

    public JTerm acc(JTerm h, JTerm s, JTerm o1, JTerm o2) {
        return func(services.getTypeConverter().getHeapLDT().getAcc(), h, s, o1, o2);
    }

    public JTerm reach(JTerm h, JTerm s, JTerm o1, JTerm o2, JTerm n) {
        return func(services.getTypeConverter().getHeapLDT().getReach(), h, s, o1, o2, n);
    }

    // -------------------------------------------------------------------------
    // sequence operators
    // -------------------------------------------------------------------------

    public JTerm seqGet(Sort asSort, JTerm s, JTerm idx) {
        return func(services.getTypeConverter().getSeqLDT().getSeqGet(asSort, services), s, idx);
    }

    public JTerm seqLen(JTerm s) {
        return func(services.getTypeConverter().getSeqLDT().getSeqLen(), s);
    }

    /**
     * Function representing the least index of an element x in a sequence s (or underspecified)
     */
    public JTerm indexOf(JTerm s, JTerm x) {
        return func(services.getTypeConverter().getSeqLDT().getSeqIndexOf(), s, x);
    }

    public JTerm seqEmpty() {
        return func(services.getTypeConverter().getSeqLDT().getSeqEmpty());
    }

    public JTerm seqSingleton(JTerm x) {
        return func(services.getTypeConverter().getSeqLDT().getSeqSingleton(), x);
    }

    public JTerm seqConcat(JTerm s, JTerm s2) {
        if (s == seqEmpty()) {
            return s2;
        } else if (s2 == seqEmpty()) {
            return s;
        } else {
            return func(services.getTypeConverter().getSeqLDT().getSeqConcat(), s, s2);
        }
    }

    public JTerm seq(JTerm... terms) {
        JTerm result = seqEmpty();
        for (JTerm term : terms) {
            result = seqConcat(result, seqSingleton(term));
        }
        return result;
    }

    public JTerm seq(ImmutableList<JTerm> terms) {
        JTerm result = seqEmpty();
        for (JTerm term : terms) {
            result = seqConcat(result, seqSingleton(term));
        }
        return result;
    }

    public JTerm seqSub(JTerm s, JTerm from, JTerm to) {
        return func(services.getTypeConverter().getSeqLDT().getSeqSub(), s, from, to);
    }

    public JTerm seqUpd(JTerm seq, JTerm idx, JTerm value) {
        return func(services.getTypeConverter().getSeqLDT().getSeqUpd(), seq, idx, value);
    }


    public JTerm seqReverse(JTerm s) {
        return func(services.getTypeConverter().getSeqLDT().getSeqReverse(), s);
    }

    // -------------------------------------------------------------------------
    // misc (moved from key.util.MiscTools)
    // -------------------------------------------------------------------------

    /**
     * Replaces a child term by another one.
     *
     * @param term the term in which to perform the replacement.
     * @param pos the position at which to perform the replacement.
     * @param replacement the replacement term.
     * @return {@code term}, with the child at {@code pos} replaced by {@code replacement}.
     */
    public JTerm replace(JTerm term, PosInTerm pos, JTerm replacement) {
        return replace(term, pos, replacement, 0);
    }

    private JTerm replace(JTerm term, PosInTerm pos, JTerm replacement, int depth) {
        if (depth == pos.depth()) {
            return replacement;
        }

        ImmutableArray<JTerm> oldSubs = term.subs();
        JTerm[] newSubs = new JTerm[oldSubs.size()];

        for (int i = 0; i < newSubs.length; ++i) {
            if (pos.getIndexAt(depth) == i) {
                newSubs[i] = replace(oldSubs.get(i), pos, replacement, depth + 1);
            } else {
                newSubs[i] = oldSubs.get(i);
            }
        }

        return tf.createTerm(term.op(), newSubs, term.boundVars(),
            term.getLabels());
    }

    public ImmutableSet<JTerm> unionToSet(JTerm s) {
        final LocSetLDT setLDT = services.getTypeConverter().getLocSetLDT();
        assert s.sort().equals(setLDT.targetSort());
        final Function union = setLDT.getUnion();
        ImmutableSet<JTerm> result = DefaultImmutableSet.nil();
        ImmutableList<JTerm> workingList = ImmutableSLList.<JTerm>nil().prepend(s);
        while (!workingList.isEmpty()) {
            JTerm f = workingList.head();
            workingList = workingList.tail();
            if (f.op() == union) {
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
    public static JTerm goBelowUpdates(JTerm term) {
        while (term.op() instanceof UpdateApplication) {
            term = UpdateApplication.getTarget(term);
        }
        return term;
    }

    /**
     * Removes leading updates from the passed term.
     */
    public static Pair<ImmutableList<JTerm>, JTerm> goBelowUpdates2(JTerm term) {
        ImmutableList<JTerm> updates = ImmutableSLList.nil();
        while (term.op() instanceof UpdateApplication) {
            updates = updates.append(UpdateApplication.getUpdate(term));
            term = UpdateApplication.getTarget(term);
        }
        return new Pair<>(updates, term);
    }

    public JTerm seqDef(QuantifiableVariable qv, JTerm a, JTerm b, JTerm t) {
        return func(services.getTypeConverter().getSeqLDT().getSeqDef(), new JTerm[] { a, b, t },
            new ImmutableArray<>(qv));
    }

    public JTerm values() {
        return func(services.getTypeConverter().getSeqLDT().getValues());
    }

    /**
     * Returns the {@link Sort}s of the given {@link JTerm}s.
     *
     * @param terms The given {@link JTerm}s.
     * @return The {@link JTerm} {@link Sort}s.
     */
    public ImmutableList<Sort> getSorts(Iterable<JTerm> terms) {
        ImmutableList<Sort> result = ImmutableSLList.nil();
        for (JTerm t : terms) {
            result = result.append(t.sort());
        }
        return result;
    }

    /**
     * Similar behavior as {@link #imp(JTerm, JTerm)} but simplifications are not performed if
     * {@link TermLabel}s would be lost.
     *
     * @param t1 The left side.
     * @param t2 The right side.
     * @return The created {@link JTerm}.
     */
    public JTerm impPreserveLabels(JTerm t1, JTerm t2) {
        if ((t1.op() == Junctor.FALSE || t2.op() == Junctor.TRUE)
                && (!t1.hasLabels() && !t2.hasLabels())) {
            return tt();
        } else if (t1.op() == Junctor.TRUE && !t1.hasLabels()) {
            return t2;
        } else if (t2.op() == Junctor.FALSE && !t2.hasLabels()) {
            return notPreserveLabels(t1);
        } else {
            return tf.createTerm(Junctor.IMP, t1, t2);
        }
    }

    /**
     * Similar behavior as {@link #not(JTerm)} but simplifications are not performed if
     * {@link TermLabel}s would be lost.
     *
     * @param t The child {@link JTerm}.
     * @return The created {@link JTerm}.
     */
    public JTerm notPreserveLabels(JTerm t) {
        if (t.op() == Junctor.TRUE && !t.hasLabels()) {
            return ff();
        } else if (t.op() == Junctor.FALSE && !t.hasLabels()) {
            return tt();
        } else if (t.op() == Junctor.NOT && !t.hasLabels()) {
            return t.sub(0);
        } else {
            return tf.createTerm(Junctor.NOT, t);
        }
    }

    /**
     * Similar behavior as {@link #and(Iterable)} but simplifications are not performed if
     * {@link TermLabel}s would be lost.
     *
     * @param subTerms The sub {@link JTerm}s.
     * @return The created {@link JTerm}.
     */
    public JTerm andPreserveLabels(Iterable<JTerm> subTerms) {
        JTerm result = tt();
        for (JTerm sub : subTerms) {
            result = andPreserveLabels(result, sub);
        }
        return result;
    }

    /**
     * Similar behavior as {@link #and(JTerm, JTerm)} but simplifications are not performed if
     * {@link TermLabel}s would be lost.
     *
     * @param t1 The left side.
     * @param t2 The right side.
     * @return The created {@link JTerm}.
     */
    public JTerm andPreserveLabels(JTerm t1, JTerm t2) {
        if ((t1.op() == Junctor.FALSE || t2.op() == Junctor.FALSE)
                && (!t1.hasLabels() && !t2.hasLabels())) {
            return ff();
        } else if (t1.op() == Junctor.TRUE && !t1.hasLabels()) {
            return t2;
        } else if (t2.op() == Junctor.TRUE && !t2.hasLabels()) {
            return t1;
        } else {
            return tf.createTerm(Junctor.AND, t1, t2);
        }
    }

    /**
     * Similar behavior as {@link #or(Iterable)} but simplifications are not performed if
     * {@link TermLabel}s would be lost.
     *
     * @param subTerms The sub {@link JTerm}s.
     * @return The created {@link JTerm}.
     */
    public JTerm orPreserveLabels(Iterable<JTerm> subTerms) {
        JTerm result = ff();
        for (JTerm sub : subTerms) {
            result = orPreserveLabels(result, sub);
        }
        return result;
    }

    /**
     * Similar behavior as {@link #or(JTerm, JTerm)} but simplifications are not performed if
     * {@link TermLabel}s would be lost.
     *
     * @param t1 The left side.
     * @param t2 The right side.
     * @return The created {@link JTerm}.
     */
    public JTerm orPreserveLabels(JTerm t1, JTerm t2) {
        if ((t1.op() == Junctor.TRUE || t2.op() == Junctor.TRUE)
                && (!t1.hasLabels() && !t2.hasLabels())) {
            return tt();
        } else if (t1.op() == Junctor.FALSE && !t1.hasLabels()) {
            return t2;
        } else if (t2.op() == Junctor.FALSE && !t2.hasLabels()) {
            return t1;
        } else {
            return tf.createTerm(Junctor.OR, t1, t2);
        }
    }

    /**
     * Floating-point aware equality for floats and double
     */
    public JTerm fpEq(JTerm t1, JTerm t2) {
        FloatLDT floatLDT = services.getTypeConverter().getFloatLDT();
        if (t1.sort() == floatLDT.targetSort()) {
            return func(floatLDT.getEquals(), t1, t2);
        } else {
            // If it is not float, assume double. It will fail if wrong args
            DoubleLDT doubleLDT = services.getTypeConverter().getDoubleLDT();
            return func(doubleLDT.getEquals(), t1, t2);
        }
    }


    // Origin label addition

    /**
     * add origin information to the term and all its sub terms
     * nothing will be done if no origin term label factory is present
     *
     * @param term the term where to start to add the origin information
     * @param origin the Origin information
     * @return the labeled term or the same term, if no origin term label factory is present
     */
    public JTerm addLabelToAllSubs(JTerm term, OriginTermLabel.Origin origin) {
        final OriginTermLabelFactory originFactory = services.getOriginFactory();
        if (originFactory != null) {
            return addLabelToAllSubs(term, originFactory.createOriginTermLabel(origin));
        }
        return term;
    }

    /**
     * add origin information to the term
     * nothing will be done if no origin term label factory is present
     *
     * @param term the term where to add the origin information
     * @param origin the Origin information
     * @return the labeled term or the same term, if no origin term label factory is present
     */
    public JTerm addLabel(JTerm term, OriginTermLabel.Origin origin) {
        final OriginTermLabelFactory originFactory = services.getOriginFactory();
        if (originFactory != null) {
            return addLabel(term, originFactory.createOriginTermLabel(origin));
        }
        return term;
    }

    /**
     * returns the origin term label factory
     *
     * @return the OriginTermLabelFactory
     */
    public OriginTermLabelFactory getOriginFactory() {
        return services.getOriginFactory();
    }
}
