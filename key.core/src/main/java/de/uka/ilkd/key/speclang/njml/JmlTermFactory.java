/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.util.*;
import java.util.function.BiFunction;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.ldt.BooleanLDT;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.JMLSpecExtractor;
import de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator;
import de.uka.ilkd.key.speclang.translation.SLExceptionFactory;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.antlr.runtime.Token;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static java.text.MessageFormat.format;

/**
 * Old legacy factory methods for constructing KeY terms for JML constructs.
 */
public final class JmlTermFactory {
    public static final Logger LOGGER = LoggerFactory.getLogger(JmlTermFactory.class);

    public Services services;
    public final TermBuilder tb;
    public final SLExceptionFactory exc;
    // public final JMLArithmeticHelper arithmeticHelper;
    public final List<PositionedString> warnings = new ArrayList<>();
    public static final Map<String, String> jml2jdl;

    static {
        Map<String, String> tmp = new TreeMap<>();
        tmp.put("\\map_get", "mapGet");
        tmp.put("\\map_empty", "mapEmpty");
        tmp.put("\\map_singleton", "mapSingleton");
        tmp.put("\\map_override", "mapOverride");
        tmp.put("\\seq_2_map", "seq2map");
        tmp.put("\\map_update", "mapUpdate");
        tmp.put("\\map_remove", "mapRemove");
        tmp.put("\\in_domain", "inDomain");
        tmp.put("\\domain_implies_created", "inDomainImpliesCreated");
        tmp.put("\\is_finite", "isFinite");
        tmp.put("\\map_size", "mapSize");
        jml2jdl = Collections.unmodifiableMap(tmp);
    }

    private final OverloadedOperatorHandler overloadedFunctionHandler;


    public JmlTermFactory(SLExceptionFactory exc, Services services, SpecMathMode specMathMode) {

        this.exc = exc;
        this.services = services;
        this.tb = services.getTermBuilder();
        overloadedFunctionHandler = new OverloadedOperatorHandler(services, specMathMode);
    }

    public SpecMathMode replaceSpecMathMode(SpecMathMode specMathMode) {
        return overloadedFunctionHandler.replaceSpecMathMode(specMathMode);
    }

    // region reach
    public SLExpression reach(Term t, SLExpression e1, SLExpression e2, SLExpression e3) {
        final LogicVariable stepsLV = e3 == null
                ? new LogicVariable(new Name("n"),
                    services.getTypeConverter().getIntegerLDT().targetSort())
                : null;
        final Term h = tb.getBaseHeap();
        final Term s = getFields(t);
        final Term o = e1.getTerm();
        final Term o2 = e2.getTerm();
        final Term n = e3 == null ? tb.var(stepsLV) : e3.getTerm();
        Term reach = tb.reach(h, s, o, o2, n);
        if (e3 == null) {
            reach = tb.ex(stepsLV, reach);
        }
        return new SLExpression(reach);
    }

    public SLExpression reachLocs(Term t, SLExpression e1, SLExpression e2, SLExpression e3) {
        final LogicVariable objLV =
            new LogicVariable(new Name("o"), services.getJavaInfo().objectSort());
        final LogicVariable stepsLV = e3 == null
                ? new LogicVariable(new Name("n"),
                    services.getTypeConverter().getIntegerLDT().targetSort())
                : null;
        final Term h = tb.getBaseHeap();
        final Term s = getFields(t);
        final Term o = e1.getTerm();
        final Term o2 = tb.var(objLV);
        final Term n = e3 == null ? tb.var(stepsLV) : e3.getTerm();
        Term reach = tb.reach(h, s, o, o2, n);
        if (e3 == null) {
            reach = tb.ex(stepsLV, reach);
        }

        final LogicVariable fieldLV = new LogicVariable(new Name("f"),
            services.getTypeConverter().getHeapLDT().getFieldSort());
        final Term locSet =
            tb.setComprehension(new LogicVariable[] { objLV, fieldLV }, reach, o2, tb.var(fieldLV));

        return createIntersect(locSet, services.getJavaInfo());
    }


    /**
     * Creates an "all-objects" term from a store-ref term.
     *
     * @param t store-ref term, needs to be a union of singletons
     * @return allObjects term (see <code>LocSetADT</code>) @ in case <code>t</code> is not a
     *         store-ref term cosisting of unions of singletons
     */
    private Term getFields(Term t) {
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        if (t.op().equals(locSetLDT.getUnion())) {
            final Term sub0 = getFields(t.sub(0));
            final Term sub1 = getFields(t.sub(1));
            return tb.union(sub0, sub1);
        } else if (t.op().equals(locSetLDT.getSingleton())) {
            return tb.allObjects(t.sub(1));
        } else {
            throw exc.createException0("Inacceptable field expression: " + t);
        }
    }
    // endregion


    // region quantification
    private Term typerestrictMinAndMax(KeYJavaType kjt, final boolean nullable,
            Iterable<? extends QuantifiableVariable> qvs) {
        final Type type = kjt.getJavaType();
        final int arrayDepth = JMLSpecExtractor.arrayDepth(type, services);
        Term res = tb.tt();
        for (QuantifiableVariable qv : qvs) {
            if (type instanceof PrimitiveType) {
                if (type == PrimitiveType.JAVA_BYTE) {
                    res = tb.and(res, tb.inByte(tb.var(qv)));
                }
                if (type == PrimitiveType.JAVA_SHORT) {
                    res = tb.and(res, tb.inShort(tb.var(qv)));
                }
                if (type == PrimitiveType.JAVA_CHAR) {
                    res = tb.and(res, tb.inChar(tb.var(qv)));
                }
                if (type == PrimitiveType.JAVA_INT) {
                    res = tb.and(res, tb.inInt(tb.var(qv)));
                }
                if (type == PrimitiveType.JAVA_LONG) {
                    res = tb.and(res, tb.inLong(tb.var(qv)));
                }
            } else {
                // assume reference type
                if (nullable) {
                    res = tb.and(res, tb.created(tb.var(qv)));
                } else {
                    final Term nonNull =
                        arrayDepth > 0 ? tb.deepNonNull(tb.var(qv), tb.zTerm(arrayDepth))
                                : tb.not(tb.equals(tb.var(qv), tb.NULL()));
                    res = tb.and(res, tb.and(tb.created(tb.var(qv)), nonNull));
                }
            }
        }
        return res;
    }

    public SLExpression quantifiedMin(Term _guard, Term body, KeYJavaType declsType,
            boolean nullable, ImmutableList<LogicVariable> qvs) {
        Term guard = tb.convertToFormula(_guard);
        assert guard.sort() == Sort.FORMULA;
        final Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();
        if (body.sort() != intSort) {
            throw exc.createException0("body of \\min expression must be integer type");
        }
        final Term tr = typerestrictMinAndMax(declsType, nullable, qvs);
        final Term min = tb.min(qvs, tb.andSC(tr, guard), body, services);
        final KeYJavaType type =
            services.getTypeConverter().getKeYJavaType(PrimitiveType.JAVA_BIGINT);
        return new SLExpression(min, type);
    }

    public SLExpression quantifiedMax(Term _guard, Term body, KeYJavaType declsType,
            boolean nullable, ImmutableList<LogicVariable> qvs) {
        Term guard = tb.convertToFormula(_guard);
        final Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();
        if (body.sort() != intSort) {
            throw exc.createException0("body of \\max expression must be integer type");
        }
        final Term tr = typerestrictMinAndMax(declsType, nullable, qvs);
        final Term max = tb.max(qvs, tb.andSC(tr, guard), body, services);
        final KeYJavaType type =
            services.getTypeConverter().getKeYJavaType(PrimitiveType.JAVA_BIGINT);

        return new SLExpression(max, type);
    }

    public @Nonnull SLExpression quantifiedNumOf(@Nullable Term t1, Term t2, KeYJavaType declsType,
            boolean nullable, Iterable<LogicVariable> qvs, KeYJavaType resultType) {
        BoundedNumericalQuantifier bounded = (qv, lo, hi, body) -> {
            final Term cond = tb.ife(tb.convertToFormula(body), tb.one(), tb.zero());
            return tb.bsum(qv, lo, hi, cond);
        };
        UnboundedNumericalQuantifier unbounded = (javaType, n, vars, range, body) -> {
            final Term tr = typerestrict(javaType, n, vars);
            final Term cond = tb.ife(tb.convertToFormula(body), tb.one(), tb.zero());
            return tb.sum(vars, tb.andSC(tr, range), cond);
        };
        return numeralQuantifier(declsType, nullable, qvs, t1, t2, resultType, unbounded, bounded);
    }

    public @Nonnull SLExpression quantifiedProduct(KeYJavaType declsType, boolean nullable,
            Iterable<LogicVariable> qvs, @Nullable Term t1, Term t2, KeYJavaType resultType) {
        BoundedNumericalQuantifier bounded =
            (qv, lo, hi, body) -> tb.bprod(qv, lo, hi, body, services);

        UnboundedNumericalQuantifier unbounded = (javaType, n, q, range, body) -> {
            final Term tr = typerestrict(javaType, n, q);
            return tb.prod(q, tb.andSC(tr, range), body, services);
        };
        return numeralQuantifier(declsType, nullable, qvs, t1, t2, resultType, unbounded, bounded);
    }

    public @Nonnull SLExpression quantifiedSum(KeYJavaType javaType, boolean nullable,
            Iterable<LogicVariable> qvs, @Nullable Term t1, Term t2, KeYJavaType resultType) {
        BoundedNumericalQuantifier bounded = tb::bsum;
        UnboundedNumericalQuantifier unbounded = (declsType, n, vars, range, body) -> {
            final Term tr = typerestrict(declsType, n, vars);
            return tb.sum(vars, tb.andSC(tr, range), body);
        };
        return numeralQuantifier(javaType, nullable, qvs, t1, t2, resultType, unbounded, bounded);
    }

    public SLExpression forall(Term preTerm, Term bodyTerm, KeYJavaType declsType,
            ImmutableList<LogicVariable> declVars, boolean nullable, KeYJavaType resultType) {
        BiFunction<QuantifiableVariable, Term, Term> quantify = tb::all;
        BiFunction<Term, Term, Term> combineGuard = tb::imp;
        return simpleQuantifier(preTerm, bodyTerm, declsType, declVars, nullable, resultType,
            quantify, combineGuard);
    }

    public SLExpression exists(Term preTerm, Term bodyTerm, KeYJavaType declsType,
            ImmutableList<LogicVariable> declVars, boolean nullable, KeYJavaType resultType) {
        boolean isGeneralized = false;
        BiFunction<QuantifiableVariable, Term, Term> quantify = tb::ex;
        BiFunction<Term, Term, Term> combineGuard = tb::andSC;
        return simpleQuantifier(preTerm, bodyTerm, declsType, declVars, nullable, resultType,
            quantify, combineGuard);
    }

    private SLExpression simpleQuantifier(Term preTerm, Term bodyTerm, KeYJavaType declsType,
            ImmutableList<LogicVariable> declVars, boolean nullable, KeYJavaType resultType,
            BiFunction<QuantifiableVariable, Term, Term> combine,
            BiFunction<Term, Term, Term> combineQuantifiedTerms) {
        final Type type = declsType.getJavaType();
        final int arrayDepth = JMLSpecExtractor.arrayDepth(type, services);

        if (resultType == null) {
            // quick fix. may happen with \num_of
            resultType = services.getTypeConverter().getKeYJavaType(PrimitiveType.JAVA_BIGINT);
        }

        for (LogicVariable lv : declVars) {
            preTerm = tb.and(preTerm, tb.reachableValue(tb.var(lv), declsType));
            if (lv.sort().extendsTrans(services.getJavaInfo().objectSort()) && !nullable) {
                final Term nonNull =
                    arrayDepth > 0 ? tb.deepNonNull(tb.var(lv), tb.zTerm(arrayDepth))
                            : tb.not(tb.equals(tb.var(lv), tb.NULL()));
                preTerm = tb.and(preTerm, nonNull);
            }
        }
        Term t1 = preTerm;
        Term t2 = tb.convertToFormula(bodyTerm);
        Term result = combineQuantifiedTerms.apply(t1, t2);
        for (LogicVariable qv : declVars) {
            result = combine.apply(qv, result);
        }
        return new SLExpression(result);
    }


    /*
     * public SLExpression translateGeneralizedQuantifiers(KeYJavaType declsType, boolean nullable,
     * Iterable<LogicVariable> qvs, Term t1, Term t2, KeYJavaType resultType) {
     * Iterator<LogicVariable> it = qvs.iterator(); LogicVariable qv = it.next(); assert resultType
     * != null; if (it.hasNext()) { throw new
     * SLTranslationException("Only one quantified variable is allowed in this context."); } Term
     * cond = tb.convertToBoolean(tb.and(t1, t2)); return new SLExpression(translateQuantifier(qv,
     * cond), resultType); }
     */

    private boolean isBoundedNumerical(Term a, LogicVariable lv) {
        return lowerBound(a, lv) != null && upperBound(a, lv) != null;
    }


    /**
     * Extracts lower bound from <code>a</code> if it matches the pattern.
     *
     * @param a guard to be disected
     * @param lv variable bound by quantifier
     * @return lower bound term (or null)
     */
    private Term lowerBound(Term a, LogicVariable lv) {
        if (a.arity() == 2 && a.op() == Junctor.AND && a.sub(0).arity() == 2
                && a.sub(0).sub(1).op() == lv && a.sub(0).op()
                        .equals(services.getTypeConverter().getIntegerLDT().getLessOrEquals())) {
            return a.sub(0).sub(0);
        }
        return null;
    }

    /**
     * Extracts upper bound from <code>a</code> if it matches the pattern.
     *
     * @param a guard to be disected
     * @param lv variable bound by quantifier
     * @return upper bound term (or null)
     */
    public Term upperBound(Term a, LogicVariable lv) {
        if (a.arity() == 2 && a.op() == Junctor.AND && a.sub(1).arity() == 2
                && a.sub(1).sub(0).op() == lv && a.sub(1).op()
                        .equals(services.getTypeConverter().getIntegerLDT().getLessThan())) {
            return a.sub(1).sub(1);
        }
        return null;
    }

    private @Nonnull SLExpression numeralQuantifier(KeYJavaType declsType, boolean nullable,
            Iterable<LogicVariable> qvs, Term t1, Term t2, @Nullable KeYJavaType resultType,
            UnboundedNumericalQuantifier unbounded, BoundedNumericalQuantifier bounded) {
        Iterator<LogicVariable> it = qvs.iterator();
        LogicVariable lv = it.next();
        Term t;
        if (it.hasNext() || !isBoundedNumerical(t1, lv)) {
            // not interval range, create unbounded comprehension term
            ImmutableList<QuantifiableVariable> _qvs =
                ImmutableSLList.<QuantifiableVariable>nil().prepend(lv);
            while (it.hasNext()) {
                _qvs = _qvs.prepend(it.next());
            }
            t = unbounded.apply(declsType, nullable, _qvs, t1, t2);
        } else {
            t = bounded.apply(lv, lowerBound(t1, lv), upperBound(t1, lv), t2);
        }

        if (resultType == null) {
            resultType = services.getTypeConverter().getKeYJavaType(t2);
        }

        // cast to specific JML type (fixes bug #1347)
        return buildBigintTruncationExpression(resultType, t);
    }

    public ImmutableList<Term> infflowspeclist(ImmutableList<Term> result) {
        return result;
    }

    public Term notModified(Term term, SLExpression t) {
        return null;
    }

    @Nonnull
    public SLExpression binary(OverloadedOperatorHandler.JMLOperator jmlOperator, SLExpression left,
            SLExpression right) {
        try {
            SLExpression result = overloadedFunctionHandler.build(jmlOperator, left, right);
            if (result == null) {
                throw exc.createException0(
                    String.format("Cannot resolve JML operation %s %s %s (types %s %s %s).",
                        left.getTerm(), jmlOperator.getImage(), right.getTerm(), left.getType(),
                        jmlOperator.getImage(), right.getType()));
            }
            return result;
        } catch (SLTranslationException e) {
            throw exc.createException0("Error while converting a binary expression", e);
        }
    }

    public SLExpression unary(JMLOperator unaryOp, SLExpression arg) {
        try {
            SLExpression result = overloadedFunctionHandler.build(unaryOp, arg, null);
            if (result == null) {
                throw exc.createException0(
                    String.format("Cannot resolve JML operation %s %s (types %s).",
                        unaryOp.getImage(), arg.getTerm(), arg.getType()));
            }
            return result;
        } catch (SLTranslationException e) {
            throw exc.createException0("Error while converting a unary expression", e);
        }
    }


    private interface UnboundedNumericalQuantifier {
        Term apply(KeYJavaType declsType, boolean nullable, ImmutableList<QuantifiableVariable> qvs,
                Term range, Term body);
    }

    private interface BoundedNumericalQuantifier {
        Term apply(QuantifiableVariable qv, Term lo, Term hi, Term body);
    }
    // endregion


    @Nonnull
    public SLExpression arrayRef(SLExpression receiver, String fullyQualifiedName,
            SLExpression rangeFrom, SLExpression rangeTo) {
        SLExpression result;
        try {
            if (receiver == null) {
                throw exc.createException0(format("Array \"{0}\" not found.", fullyQualifiedName));
            } else if (receiver.isType()) {
                throw exc.createException0(
                    format("Error in array expression: \"{0}\" is a type.", fullyQualifiedName));
            } else if (!(receiver.getType().getJavaType() instanceof ArrayType
                    || receiver.getType().getJavaType().equals(PrimitiveType.JAVA_SEQ))) {
                throw exc.createException0(
                    format("Cannot access {0} as an array.", receiver.getTerm()));
            }

            // arrays
            if (receiver.getType().getJavaType() instanceof ArrayType) {
                result = translateArrayReference(receiver, rangeFrom, rangeTo);

                // sequences
            } else {
                result = translateSequenceReference(receiver, rangeFrom, rangeTo);
            }
            return result;
        } catch (TermCreationException tce) {
            throw exc.createException0(tce.getMessage());
        }
    }

    public SLExpression translateArrayReference(SLExpression receiver, SLExpression rangeFrom,
            SLExpression rangeTo) {
        SLExpression result;
        if (rangeFrom == null) {
            // We have a star. A star includes all components of an array even
            // those out of bounds. This makes proving easier.
            Term t = tb.allFields(receiver.getTerm());
            result = new SLExpression(t);
        } else if (rangeTo != null) {
            // We have "rangeFrom .. rangeTo"
            Term t = tb.arrayRange(receiver.getTerm(), rangeFrom.getTerm(), rangeTo.getTerm());
            result = new SLExpression(t);
        } else {
            // We have a regular array access
            Term t = tb.dotArr(receiver.getTerm(), rangeFrom.getTerm());
            ArrayType arrayType = (ArrayType) receiver.getType().getJavaType();
            KeYJavaType elementType = arrayType.getBaseType().getKeYJavaType();
            result = new SLExpression(t, elementType);
        }
        return result;
    }


    public SLExpression translateSequenceReference(SLExpression receiver, SLExpression rangeFrom,
            SLExpression rangeTo) {
        if (rangeFrom == null) {
            // a star
            return new SLExpression(tb.allFields(receiver.getTerm()));
        } else if (rangeTo != null) {
            Term t = tb.seqSub(receiver.getTerm(), rangeFrom.getTerm(), rangeTo.getTerm());
            return new SLExpression(t);
        } else {
            return seqGet(receiver.getTerm(), rangeFrom.getTerm());
        }
    }

    public SLExpression dlKeyword(String name, ImmutableList<SLExpression> list) {
        if (name.startsWith("\\dl_")) {
            name = name.substring(4);
        }
        return translateToJDLTerm(name, list);
    }

    public SLExpression commentary(String desc, ProgramVariable selfVar, ProgramVariable resultVar,
            ImmutableList<ProgramVariable> paramVars, Term heapAtPre) {
        // strip leading and trailing (* ... *)
        String text = desc;
        text = text.substring(2, text.length() - 2);

        // prepare namespaces
        NamespaceSet namespaces = services.getNamespaces().copy();
        Namespace<IProgramVariable> programVariables = namespaces.programVariables();

        if (heapAtPre != null && heapAtPre.op() instanceof ProgramVariable) {
            programVariables.add((ProgramVariable) heapAtPre.op());
        }

        if (selfVar != null) {
            programVariables.add(selfVar);
        }

        if (resultVar != null) {
            programVariables.add(resultVar);
        }

        if (paramVars != null) {
            for (ProgramVariable param : paramVars) {
                programVariables.add(param);
            }
        }

        SLExpression result;
        try {
            result = new SLExpression(services.getTermBuilder().parseTerm(text, namespaces));
            return result;
        } catch (ParserException ex) {
            throw exc.createException0("Cannot parse embedded JavaDL: " + text + desc, ex);
        }
    }

    public SLExpression ite(SLExpression result, SLExpression a, SLExpression b) {
        // handle cases where a and b are of sort FORMULA and boolean respectively (which are
        // incompatible, unfortunately)
        final KeYJavaType bool = services.getTypeConverter().getBooleanType();
        Term aTerm = a.getType() == bool ? tb.convertToFormula(a.getTerm()) : a.getTerm();
        Term bTerm = b.getType() == bool ? tb.convertToFormula(b.getTerm()) : b.getTerm();

        Term ife = tb.ife(tb.convertToFormula(result.getTerm()), aTerm, bTerm);
        if (a.getType() != null && b.getType() != null) {
            if (a.getType().equals(b.getType())) {
                // same type: obvious case
                result = new SLExpression(ife, a.getType());
            } else {
                KeYJavaType promotedType =
                    services.getTypeConverter().getPromotedType(a.getType(), b.getType());
                if (promotedType != null) {
                    // different, put compatible types: add a cast to make sure that
                    // an int is cast to a float e.g.
                    result = new SLExpression(tb.cast(promotedType.getSort(), ife), promotedType);
                } else {
                    // TODO this is an NPE in the making
                    result = new SLExpression(ife);
                }
            }
        } else {
            // TODO this is an NPE in the making
            result = new SLExpression(ife);
        }
        return result;
    }

    public SLExpression cast(KeYJavaType type, SLExpression result) {
        if (type != null) {
            if (result.isType()) {
                throw exc.createException0("Casting of type variables not (yet) supported.");
            }
            assert result.isTerm();
            Sort origSort = result.getTerm().sort();
            Sort targetSort = type.getSort();

            if (origSort == Sort.FORMULA) {
                // This case might occur since boolean expressions
                // get converted prematurely (see bug #1121).
                // Just check whether there is a cast to boolean.
                if (type != services.getTypeConverter().getBooleanType()) {
                    throw exc.createException0("Cannot cast from boolean to " + type + ".");
                }
            } else if (targetSort == services.getTypeConverter().getIntegerLDT().targetSort()) {
                Term target = result.getTerm();
                if (origSort != services.getTypeConverter().getIntegerLDT().targetSort()) {
                    // first cast to int and then refine ...
                    target = tb.cast(targetSort, target);
                }
                return buildIntCastExpression(type, target);
            } else {
                return new SLExpression(tb.cast(type.getSort(), result.getTerm()), type);
            }
        } else {
            throw exc.createException0("Please provide a type to cast to.");
        }
        return result;
    }

    // region equalities
    public SLExpression equivalence(SLExpression left, SLExpression right) {
        checkSLExpressions(left, right, "<==>");
        return buildEqualityTerm(left, right);
    }

    public SLExpression antivalence(SLExpression left, SLExpression right) {
        checkSLExpressions(left, right, "<=!=>");
        SLExpression eq = buildEqualityTerm(left, right);
        return new SLExpression(tb.not(eq.getTerm()));
    }

    public SLExpression eq(SLExpression left, SLExpression right) {
        checkSLExpressions(left, right, "==");
        return buildEqualityTerm(left, right);
    }

    public SLExpression fpEq(SLExpression left, SLExpression right) {
        return new SLExpression(tb.fpEq(left.getTerm(), right.getTerm()));
    }

    public SLExpression fpNeq(SLExpression left, SLExpression right) {
        return new SLExpression(tb.not(tb.fpEq(left.getTerm(), right.getTerm())));
    }


    public SLExpression neq(SLExpression left, SLExpression right) {
        checkSLExpressions(left, right, "!=");
        SLExpression eq = buildEqualityTerm(left, right);
        if (eq.getType() != null) {
            return new SLExpression(tb.not(eq.getTerm()), eq.getType());
        } else {
            return new SLExpression(tb.not(eq.getTerm()));
        }
    }

    private void checkSLExpressions(SLExpression left, SLExpression right, String eqSymb) {
        if (left.isType() != right.isType()) {
            throw exc.createException0("Cannot build equality expression (" + eqSymb
                + ") between term and type.\n" + "The expression was: " + left + eqSymb + right);
        }
    }

    private SLExpression buildEqualityTerm(SLExpression a, SLExpression b) {
        if (a.isTerm() && b.isTerm()) {
            return new SLExpression(buildEqualityTerm(a.getTerm(), b.getTerm()));
        }
        if (a.isType() && b.isType()) {
            SLExpression typeofExpr;
            SLExpression typeExpr;
            if (a.getTerm() != null) {
                typeofExpr = a;
                typeExpr = b;
            } else {
                if (b.getTerm() == null) {
                    throw exc.createException0("Type equality only supported for expressions "
                        + " of shape \"\\typeof(term) == \\type(Typename)\"");
                }
                typeofExpr = b;
                typeExpr = a;
            }

            Sort os = typeExpr.getType().getSort();

            Function ioFunc = os.getExactInstanceofSymbol(services);
            Term instanceOf = tb.equals(tb.func(ioFunc, typeofExpr.getTerm()), tb.TRUE());
            IntegerLDT ldt = services.getTypeConverter().getIntegerLDT();
            if (os == ldt.targetSort()) {
                Term casted = tb.cast(ldt.targetSort(), typeofExpr.getTerm());
                Term inType =
                    tb.func(ldt.getSpecInBounds(typeExpr.getType().getJavaType()), casted);
                return new SLExpression(tb.and(instanceOf, inType));
            } else {
                return new SLExpression(instanceOf);
            }
        }
        // this should not be reached
        throw exc.createException0(
            "Equality must be between two terms or " + "two formulas, not term and formula.");
    }

    private Term buildEqualityTerm(Term a, Term b) {
        Term result;
        try {
            if (a.sort() != Sort.FORMULA && b.sort() != Sort.FORMULA) {
                result = tb.equals(a, b);
                // Special case so that model methods are handled better
            } else if (a.sort() == services.getTypeConverter().getBooleanLDT().targetSort()
                    && b.sort() == Sort.FORMULA) {
                result = tb.equals(a, tb.ife(b, tb.TRUE(), tb.FALSE()));
            } else {
                result = tb.equals(tb.convertToFormula(a), tb.convertToFormula(b));
            }
            return result;
        } catch (IllegalArgumentException e) {
            throw exc.createException0("Illegal Arguments in equality expression.");
        } catch (TermCreationException e) {
            throw exc.createException0(
                "Error in equality-expression\n" + a + " == " + b.toString() + ".");
        }
    }
    // endregion

    public SLExpression bsum(SLExpression a, SLExpression b, SLExpression t, KeYJavaType declsType,
            ImmutableList<LogicVariable> declVars) {
        KeYJavaType promo = t.getType();
        // services.getTypeConverter().getPromotedType(declsType, t.getType());

        if (!(declsType.getJavaType().equals(PrimitiveType.JAVA_INT)
                || declsType.getJavaType().equals(PrimitiveType.JAVA_BIGINT))) {
            throw exc.createException0("bounded sum variable must be of type int or \\bigint");
        } else if (declVars.size() != 1) {
            throw exc.createException0("bounded sum must declare exactly one variable");
        }
        LogicVariable qv = declVars.head();
        Term resultTerm = tb.bsum(qv, a.getTerm(), b.getTerm(), t.getTerm());
        warnings.add(new PositionedString(
            "The keyword \\bsum is deprecated and will be removed in the future.\n"
                + "Please use the standard \\sum syntax."));
        // cast to specific JML type (fixes bug #1347)
        return buildBigintTruncationExpression(promo, resultTerm);
    }

    /**
     * Truncates a bigint term to resultType depending on the spec math mode
     *
     * @param resultType the desired result type
     * @param term the term
     * @return the maybe truncated expression
     */
    private SLExpression buildBigintTruncationExpression(KeYJavaType resultType, Term term) {
        assert term.sort() == services.getTypeConverter().getIntegerLDT().targetSort();

        SpecMathMode mode = this.overloadedFunctionHandler.getSpecMathMode();
        if (mode == SpecMathMode.JAVA) {
            return buildIntCastExpression(resultType, term);
        } else {
            KeYJavaType bigint = services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BIGINT);
            return new SLExpression(term, bigint);
        }
    }

    private SLExpression buildIntCastExpression(KeYJavaType resultType, Term term) {
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        try {
            Function cast = integerLDT.getSpecCast(resultType.getJavaType());
            if (cast != null) {
                return new SLExpression(tb.func(cast, term), resultType);
            } else {
                // \bigint does not need a spec cast
                return new SLExpression(term, resultType);
            }
        } catch (RuntimeException e) {
            throw exc.createException0(
                "Error while casting expression " + term + " to " + resultType + ".", e);
        }
    }

    public SLExpression fresh(ImmutableList<SLExpression> list,
            Map<LocationVariable, Term> atPres) {
        final LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
        if (atPres == null || atPres.get(baseHeap) == null) {
            throw exc.createException0("\\fresh not allowed in this context");
        }

        Term t = tb.tt();
        final Sort objectSort = services.getJavaInfo().objectSort();
        final TypeConverter tc = services.getTypeConverter();
        for (SLExpression expr : list) {
            if (!expr.isTerm()) {
                throw exc.createException0("Expected a term, but found: " + expr);
            } else if (expr.getTerm().sort().extendsTrans(objectSort)) {
                t = tb.and(t,
                    tb.equals(tb.select(tc.getBooleanLDT().targetSort(), atPres.get(baseHeap),
                        expr.getTerm(), tb.func(tc.getHeapLDT().getCreated())), tb.FALSE()));
                // add non-nullness (bug #1364)
                t = tb.and(t, tb.not(tb.equals(expr.getTerm(), tb.NULL())));
            } else if (expr.getTerm().sort().extendsTrans(tc.getLocSetLDT().targetSort())) {
                t = tb.and(t, tb.subset(expr.getTerm(), tb.freshLocs(atPres.get(baseHeap))));
            } else {
                throw exc.createException0("Wrong type: " + expr);
            }
        }
        return new SLExpression(t);
    }

    public SLExpression invFor(SLExpression param) {
        Term obj = param.getTerm();
        return new SLExpression(tb.inv(obj));
    }

    public SLExpression staticInfFor(KeYJavaType kjt) {
        final Term term = tb.staticInv(kjt);
        return new SLExpression(term);
    }

    public SLExpression invFreeFor(SLExpression param) {
        Term obj = param.getTerm();
        return new SLExpression(tb.invFree(obj));
    }

    public SLExpression staticInfFreeFor(KeYJavaType kjt) {
        final Term term = tb.staticInvFree(kjt);
        return new SLExpression(term);
    }


    public SLExpression empty(JavaInfo javaInfo) {
        return createIntersect(tb.empty(), javaInfo);
    }

    public SLExpression index() {
        final KeYJavaType t = services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_INT);
        return new SLExpression(tb.index(), t);
    }

    public SLExpression values(KeYJavaType t) {
        return new SLExpression(tb.values(), t);
    }

    /**
     * Need to handle this one differently from INV_FOR since here static invariants may occur too.
     * For a static invariant, take the passed type as receiver.
     */
    @Nonnull
    public SLExpression createInv(Term selfVar, KeYJavaType targetType) {
        final boolean isStatic = selfVar == null;
        assert targetType != null || !isStatic;
        final Term result = isStatic ? tb.staticInv(targetType) : tb.inv(selfVar);
        return new SLExpression(result);
    }

    /**
     * Need to handle this one differently from INV_FREE_FOR since here static invariants may occur
     * too. For a static invariant, take the passed type as receiver.
     */
    @Nonnull
    public SLExpression createInvFree(Term selfVar, KeYJavaType targetType) {
        final boolean isStatic = selfVar == null;
        assert targetType != null || !isStatic;
        final Term result = isStatic ? tb.staticInvFree(targetType) : tb.invFree(selfVar);
        return new SLExpression(result);
    }

    public SLExpression createSeqDef(SLExpression a, SLExpression b, SLExpression t,
            KeYJavaType declsType, ImmutableList<? extends QuantifiableVariable> declVars) {
        if (!(declsType.getJavaType().equals(PrimitiveType.JAVA_INT)
                || declsType.getJavaType().equals(PrimitiveType.JAVA_BIGINT))) {
            throw exc.createException0(
                "sequence definition variable must be of type int or \\bigint");
        } else if (declVars.size() != 1) {
            throw exc.createException0("sequence definition must declare exactly one variable");
        }
        QuantifiableVariable qv = declVars.head();
        Term tt = t.getTerm();
        if (tt.sort() == Sort.FORMULA) {
            // bugfix (CS): t.getTerm() delivers a formula instead of a
            // boolean term; obviously the original boolean terms are
            // converted to formulas somewhere else; however, we need
            // boolean terms instead of formulas here
            tt = tb.convertToBoolean(t.getTerm());
        }
        Term resultTerm = tb.seqDef(qv, a.getTerm(), b.getTerm(), tt);
        final KeYJavaType seqtype = services.getJavaInfo().getPrimitiveKeYJavaType("\\seq");
        return new SLExpression(resultTerm, seqtype);
    }

    public SLExpression createUnionF(boolean nullable,
            Pair<KeYJavaType, ImmutableList<LogicVariable>> declVars, Term expr, Term guard) {
        final JavaInfo javaInfo = services.getJavaInfo();
        final Term restr =
            JmlTermFactory.this.typerestrict(declVars.first, nullable, declVars.second);
        guard = guard == null ? restr : tb.and(restr, guard);
        return createIntersect(tb.infiniteUnion(
            declVars.second.toArray(new QuantifiableVariable[declVars.second.size()]), guard, expr),
            javaInfo);
    }

    public SLExpression createUnion(JavaInfo javaInfo, Term t) {
        return new SLExpression(t, javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
    }

    public SLExpression createIntersect(Term t, JavaInfo javaInfo) {
        return new SLExpression(t, javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
    }

    public Term createStoreRef(SLExpression expr) {
        if (expr.isTerm()) {
            Term t = expr.getTerm();
            LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
            if (t.sort().equals(locSetLDT.targetSort())
                    || t.op().equals(locSetLDT.getSingleton())) {
                return t;
            } else {
                ImmutableList<SLExpression> exprList = ImmutableSLList.nil();
                exprList = exprList.append(expr);
                return createLocSet(exprList);
            }
        }
        throw exc.createException0("Not a term: " + expr);
    }

    public Term createLocSet(ImmutableList<SLExpression> exprList) {
        ImmutableList<Term> singletons = ImmutableSLList.nil();
        for (SLExpression expr : exprList) {
            if (expr.isTerm()) {
                Term t = expr.getTerm();
                LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
                if (!t.op().equals(locSetLDT.getSingleton())) {
                    HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
                    if (heapLDT.getSortOfSelect(t.op()) != null) {
                        final Term objTerm = t.sub(1);
                        final Term fieldTerm = t.sub(2);
                        t = tb.singleton(objTerm, fieldTerm);
                        singletons = singletons.append(t);
                    } else if (t.op() instanceof ProgramVariable) {
                        // this case may happen with local variables
                        exc.addIgnoreWarning("local variable in assignable clause");
                        LOGGER.debug("Can't create a locset from local variable " + t + ".\n"
                            + "In this version of KeY, you do not need to put them in assignable clauses.");
                    } else {
                        throw exc.createException0("Can't create a locset from " + t + ".");
                    }
                } else {
                    throw exc.createException0("Can't create a locset of a singleton: " + expr);
                }
            } else {
                throw exc.createException0("Not a term: " + expr);
            }
        }
        return tb.union(singletons);
    }

    public SLExpression createPairwiseDisjoint(ImmutableList<Term> list) {
        ImmutableList<Term> disTerms = ImmutableSLList.nil();
        while (!list.isEmpty()) {
            Term t1 = list.head();
            list = list.tail();
            for (Term t2 : list) {
                Term dis = tb.disjoint(t1, t2);
                disTerms = disTerms.append(dis);
            }
        }
        return new SLExpression(tb.and(disTerms));
    }

    public SLExpression seqConcat(Term seq1, Term seq2) {
        final KeYJavaType seqtype = services.getJavaInfo().getPrimitiveKeYJavaType("\\seq");
        return new SLExpression(tb.seqConcat(seq1, seq2), seqtype);
    }

    @Nonnull
    public SLExpression seqGet(Term seq, Term idx) {
        return new SLExpression(tb.seqGet(Sort.ANY, seq, idx));
    }

    public SLExpression seqConst(ImmutableList<SLExpression> exprList) {
        ImmutableList<Term> terms = ImmutableSLList.nil();
        for (SLExpression expr : exprList) {
            if (expr.isTerm()) {
                Term t = expr.getTerm();
                terms = terms.append(t);
            } else {
                throw exc.createException0("Not a term: " + expr);
            }
        }
        final KeYJavaType seqtype = services.getJavaInfo().getPrimitiveKeYJavaType("\\seq");
        return new SLExpression(tb.seq(terms), seqtype);
    }

    public SLExpression createIndexOf(Term seq, Term elem) {
        final KeYJavaType inttype =
            services.getJavaInfo().getPrimitiveKeYJavaType(PrimitiveType.JAVA_BIGINT);
        return new SLExpression(tb.indexOf(seq, elem), inttype);
    }

    public @Nonnull Term createReturns(@Nullable Term term) {
        return term == null ? tb.tt() : tb.convertToFormula(term);
    }

    public @Nonnull Pair<Label, Term> createContinues(Term term, String label) {
        return createBreaks(term, label);
    }

    @Nonnull
    public Pair<Label, Term> createBreaks(Term term, String label) {
        Term formula = term == null ? tb.tt() : tb.convertToFormula(term);
        return new Pair<>(label == null ? null : new ProgramElementName(label), formula);
    }


    // region clauses
    public Term signalsOnly(ImmutableList<KeYJavaType> signalsonly, ProgramVariable excVar) {
        Term result = tb.ff();
        for (KeYJavaType kjt : signalsonly) {
            Function instance = kjt.getSort().getInstanceofSymbol(services);
            result = tb.or(result, tb.equals(tb.func(instance, tb.var(excVar)), tb.TRUE()));
        }

        return result;
    }

    public Term signals(Term result, LogicVariable eVar, ProgramVariable excVar,
            KeYJavaType excType) {
        if (result == null) {
            result = tb.tt();
        } else {
            Map /* Operator -> Operator */<LogicVariable, ProgramVariable> replaceMap =
                new LinkedHashMap<>();
            replaceMap.put(eVar, excVar);
            OpReplacer excVarReplacer = new OpReplacer(replaceMap, services.getTermFactory());

            Sort os = excType.getSort();
            Function instance = os.getInstanceofSymbol(services);

            result = tb.imp(tb.equals(tb.func(instance, tb.var(excVar)), tb.TRUE()),
                tb.convertToFormula(excVarReplacer.replace(result)));
        }
        return result;
    }

    public Pair<IObserverFunction, Term> represents(SLExpression lhs, Term t) {
        return new Pair<>((IObserverFunction) lhs.getTerm().op(), t);
    }

    public Triple<IObserverFunction, Term, Term> depends(SLExpression lhs, Term rhs,
            SLExpression mby) {
        LocationVariable heap = services.getTypeConverter().getHeapLDT().getHeap();

        if (!lhs.isTerm()) {
            throw exc.createException0(
                "Left hand side of depends clause should be a term, given:" + lhs);
        }

        if (!(lhs.getTerm().op() instanceof IObserverFunction)) {
            throw exc.createException0(
                "Left hand side of depends clause should be of type IObserverFunction, given:"
                    + lhs.getTerm().op().getClass());
        }

        if (lhs.getTerm().sub(0).op() != heap) {
            throw exc.createException0("Depends clause should be heap dependent of heap " + heap
                + ", given" + lhs.getTerm().sub(0).op());
        }

        return new Triple<>((IObserverFunction) lhs.getTerm().op(), rhs,
            mby == null ? null : mby.getTerm());
    }


    public Term assignable(@Nonnull Term term) {
        return accessible(term);
    }

    public Term accessible(@Nonnull Term ensuresTerm) {
        BooleanLDT booleanLDT = services.getTypeConverter().getBooleanLDT();
        if (ensuresTerm.sort() == booleanLDT.targetSort()) {
            return tb.convertToFormula(ensuresTerm);
        } else {
            return ensuresTerm;
        }
    }
    // endregion

    /**
     * Create a skolem term (wrapped in SLExpression) for currently unsupported JML expressions of
     * type int.
     */
    SLExpression createSkolemExprInt(Token jmlKeyWord) {
        return skolemExprHelper(jmlKeyWord, PrimitiveType.JAVA_INT);
    }

    /**
     * Create a skolem term (wrapped in SLExpression) for currently unsupported JML expressions of
     * type long.
     */
    SLExpression createSkolemExprLong(Token jmlKeyWord) {
        return skolemExprHelper(jmlKeyWord, PrimitiveType.JAVA_LONG);
    }

    public SLExpression createSkolemExprLong(String text) {
        return skolemExprHelper(text, PrimitiveType.JAVA_LONG);
    }


    /**
     * Create a skolem term (wrapped in SLExpression) for currently unsupported JML expressions of
     * type \bigint.
     */
    SLExpression createSkolemExprBigint(Token jmlKeyWord) {
        return skolemExprHelper(jmlKeyWord, PrimitiveType.JAVA_BIGINT);
    }

    /**
     * Create a skolem term (wrapped in SLExpression) for currently unsupported JML expressions of
     * type Object.
     */
    SLExpression createSkolemExprObject(Token jmlKeyWord) {
        assert services != null;
        final KeYJavaType objType = services.getJavaInfo().getJavaLangObject();
        assert objType != null;
        return skolemExprHelper(jmlKeyWord, objType, services);
    }

    public SLExpression createSkolemExprObject(String jmlKeyWord) {
        assert services != null;
        final KeYJavaType objType = services.getJavaInfo().getJavaLangObject();
        assert objType != null;
        return skolemExprHelper(jmlKeyWord, objType, services);
    }

    /**
     * Create a nullary predicate (wrapped in SLExpression) for currently unsupported JML
     * expressions of type boolean.
     */
    public @Nonnull SLExpression createSkolemExprBool(@Nonnull Token jmlKeyWord) {
        return createSkolemExprBool(jmlKeyWord.getText());
    }

    public @Nonnull SLExpression createSkolemExprBool(String jmlKeyWord) {
        exc.addUnderspecifiedWarning(jmlKeyWord);
        final Namespace<Function> fns = services.getNamespaces().functions();
        final String shortName = jmlKeyWord.replace("\\", "");
        int x = -1;
        Name name;
        do {
            name = new Name(shortName + "_" + ++x);
        } while (fns.lookup(name) != null);
        final Function sk = new Function(name, Sort.FORMULA);
        fns.add(sk);
        final Term t = tb.func(sk);
        return new SLExpression(t);
    }

    /**
     * Get non-critical warnings.
     */
    public @Nonnull List<PositionedString> getWarnings() {
        return new ArrayList<>(warnings);
    }

    /**
     * Get non-critical warnings.
     */
    public @Nonnull String getWarningsAsString() {
        var sb = new StringBuilder();
        for (PositionedString s : warnings) {
            sb.append(s.toString());
            sb.append("\n");
        }
        sb.deleteCharAt(sb.length() - 1);
        return sb.toString();
    }

    public SLExpression skolemExprHelper(Token jmlKeyWord, PrimitiveType type) {
        final KeYJavaType kjt = services.getJavaInfo().getPrimitiveKeYJavaType(type);
        return skolemExprHelper(jmlKeyWord, kjt, services);
    }

    public SLExpression skolemExprHelper(String jmlKeyWord, PrimitiveType type) {
        final KeYJavaType kjt = services.getJavaInfo().getPrimitiveKeYJavaType(type);
        return skolemExprHelper(kjt, services, jmlKeyWord);
    }

    public SLExpression skolemExprHelper(Token jmlKeyWord, KeYJavaType type,
            TermServices services) {
        exc.addUnderspecifiedWarning(jmlKeyWord.getText());
        final String shortName = jmlKeyWord.getText();
        return skolemExprHelper(type, services, shortName);
    }

    public SLExpression skolemExprHelper(String jmlKeyWord, KeYJavaType type,
            TermServices services) {
        exc.addUnderspecifiedWarning(jmlKeyWord);
        return skolemExprHelper(type, services, jmlKeyWord);
    }


    @Nonnull
    public SLExpression skolemExprHelper(@Nonnull KeYJavaType type, @Nonnull TermServices services,
            @Nonnull String shortName) {
        shortName = shortName.replace("\\", "");
        final Namespace<Function> fns = services.getNamespaces().functions();
        final Sort sort = type.getSort();
        int x = -1;
        Name name;
        do {
            name = new Name(shortName + "_" + ++x);
        } while (fns.lookup(name) != null);
        final Function sk = new Function(name, sort);
        fns.add(sk);
        final Term t = tb.func(sk);
        return new SLExpression(t, type);
    }
    // endregion


    public SLExpression translateToJDLTerm(final String functName,
            ImmutableList<SLExpression> list) {
        Namespace<Function> funcs = services.getNamespaces().functions();
        Named symbol = funcs.lookup(new Name(functName));

        // weigl 2021-07-20: Handling of typed parameter in functions,
        // e.g, \dl_seqGet is resolved to any::seqGet.
        if (symbol == null) {
            String typedFunName = "::" + functName;
            Optional<String> altFunc =
                funcs.allElements().stream()
                        .map(it -> it.name().toString())
                        .filter(it -> it.endsWith(typedFunName))
                        .findFirst();
            if (altFunc.isPresent()) {
                symbol = funcs.lookup(altFunc.get());
            }
        }

        if (symbol != null) {
            // Function or predicate symbol found

            assert symbol instanceof Function : "Expecting a function symbol in this namespace";
            Function function = (Function) symbol;

            Term[] args;
            if (list == null) {
                list = ImmutableSLList.nil();
            }

            Term heap = tb.getBaseHeap();

            // special casing "implicit heap" arguments:
            // omitting one argument means first argument is "heap"
            int i = 0;
            if (function.arity() == list.size() + 1 && function.argSort(0) == heap.sort()) {
                args = new Term[list.size() + 1];
                args[i++] = heap;
            } else {
                args = new Term[list.size()];
            }

            for (SLExpression expr : list) {
                if (!expr.isTerm()) {
                    throw exc.createException0("Expecting a term here, not: " + expr);
                }
                args[i++] = expr.getTerm();
            }

            try {
                Term resultTerm = tb.func(function, args, null);
                final KeYJavaType type =
                    services.getTypeConverter().getIntegerLDT().targetSort() == resultTerm.sort()
                            ? services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BIGINT)
                            : services.getJavaInfo().getKeYJavaType(resultTerm.sort());
                return type == null ? new SLExpression(resultTerm)
                        : new SLExpression(resultTerm, type);
            } catch (TermCreationException ex) {
                throw exc.createException0(String.format("Cannot create term %s(%s)",
                    function.name(), MiscTools.join(args, ", ")), ex);
            }

        }

        Namespace<IProgramVariable> progVars = services.getNamespaces().programVariables();
        symbol = progVars.lookup(new Name(functName));

        if (symbol == null) {
            throw exc.createException0("Unknown escaped symbol " + functName);
        }

        assert symbol instanceof ProgramVariable : "Expecting a program variable";
        ProgramVariable pv = (ProgramVariable) symbol;
        try {
            Term resultTerm = tb.var(pv);
            return new SLExpression(resultTerm);
        } catch (TermCreationException ex) {
            throw exc.createException0("Cannot create term " + pv.name(), ex);
        }
    }


    /*
     * Translate a term of type \map to JavaDL, if it occurs in a JML expression.
     */
    public SLExpression translateMapExpressionToJDL(Token t, ImmutableList<SLExpression> list,
            Services services) {
        return translateMapExpressionToJDL(t.getText(), list, services);
    }

    public SLExpression translateMapExpressionToJDL(String text, ImmutableList<SLExpression> list,
            Services services) {
        String functName = jml2jdl.get(text);
        if (functName == null) {
            throw exc.createException0("Unknown function: " + text);
        }
        return translateToJDLTerm(functName, list);
    }

    /**
     * Provide restriction terms for the declared KeYJavaType Note that these restrictions only
     * apply to the JML to DL translation. See also
     * {@link TermBuilder#reachableValue(Term, KeYJavaType)}.
     */
    @Nonnull
    private Term typerestrict(
            @Nonnull KeYJavaType kjt, final boolean nullable,
            Iterable<? extends QuantifiableVariable> qvs) {
        final Type type = kjt.getJavaType();
        final int arrayDepth = JMLSpecExtractor.arrayDepth(type, services);
        Term res = tb.tt();
        for (QuantifiableVariable qv : qvs) {
            if (type instanceof PrimitiveType) {
                if (type == PrimitiveType.JAVA_BYTE) {
                    res = tb.and(res, tb.inByte(tb.var(qv)));
                }
                if (type == PrimitiveType.JAVA_SHORT) {
                    res = tb.and(res, tb.inShort(tb.var(qv)));
                }
                if (type == PrimitiveType.JAVA_CHAR) {
                    res = tb.and(res, tb.inChar(tb.var(qv)));
                }
                if (type == PrimitiveType.JAVA_INT) {
                    res = tb.and(res, tb.inInt(tb.var(qv)));
                }
                if (type == PrimitiveType.JAVA_LONG) {
                    res = tb.and(res, tb.inLong(tb.var(qv)));
                }
                if (type == PrimitiveType.JAVA_LOCSET) {
                    res = tb.and(res, tb.disjoint(tb.var(qv), tb.freshLocs(tb.getBaseHeap())));
                }
            } else {
                // assume reference type
                if (nullable) {
                    res = tb.and(res,
                        tb.or(tb.created(tb.var(qv)), tb.equals(tb.var(qv), tb.NULL())));
                } else {
                    final Term nonNull =
                        arrayDepth > 0 ? tb.deepNonNull(tb.var(qv), tb.zTerm(arrayDepth))
                                : tb.not(tb.equals(tb.var(qv), tb.NULL()));
                    res = tb.and(res, tb.and(tb.created(tb.var(qv)), nonNull));
                }
            }
        }
        return res;
    }
}
