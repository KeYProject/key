/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.ldt.*;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.SpecNameLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.translation.JMLResolverManager;
import de.uka.ilkd.key.speclang.njml.JmlParser.PrimaryFloatingPointContext;
import de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator;
import de.uka.ilkd.key.speclang.translation.SLExceptionFactory;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.speclang.translation.SLParameters;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.mergerule.MergeParamsSpec;
import de.uka.ilkd.key.util.parsing.BuildingException;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.TerminalNode;

import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.*;
import static java.lang.String.format;
import static java.util.Objects.requireNonNull;

/**
 * This is the visitor which translates JML constructs into their KeY counterparts.
 * <p>
 * Note, that this translator does not construct any contracts. In particular, clauses are
 * translated into a corresponding {@link Term} and are attached in
 * {@link de.uka.ilkd.key.speclang.jml.JMLSpecExtractor} into the correct contract.
 *
 * @author Alexander Weigl
 * @version 1 (5/10/20)
 */
class Translator extends JmlParserBaseVisitor<Object> {

    private final Services services;
    private final TermBuilder tb;
    private final JavaInfo javaInfo;
    private final KeYJavaType containerType;
    private final HeapLDT heapLDT;
    private final LocSetLDT locSetLDT;
    private final BooleanLDT booleanLDT;
    private final SLExceptionFactory exc;
    private final JmlTermFactory termFactory;
    private final ProgramVariable selfVar;
    private final ImmutableList<ProgramVariable> paramVars;
    private final ProgramVariable resultVar;
    private final ProgramVariable excVar;
    private final Map<LocationVariable, Term> atPres;
    private final Map<LocationVariable, Term> atBefores;

    // Helper objects
    private final JMLResolverManager resolverManager;

    Translator(Services services, KeYJavaType specInClass, ProgramVariable self,
            SpecMathMode specMathMode, ImmutableList<ProgramVariable> paramVars,
            ProgramVariable result, ProgramVariable exc, Map<LocationVariable, Term> atPres,
            Map<LocationVariable, Term> atBefores) {
        assert self == null || specInClass != null;

        // save parameters
        this.services = services;
        this.tb = services.getTermBuilder();
        this.javaInfo = services.getJavaInfo();
        containerType = specInClass;
        this.heapLDT = services.getTypeConverter().getHeapLDT();
        this.locSetLDT = services.getTypeConverter().getLocSetLDT();
        this.booleanLDT = services.getTypeConverter().getBooleanLDT();
        this.exc = new SLExceptionFactory(null, 1, 0);

        this.selfVar = self;
        this.paramVars = paramVars;
        this.resultVar = result;
        this.excVar = exc;
        this.atPres = atPres;
        this.atBefores = atBefores;

        this.termFactory = new JmlTermFactory(this.exc, services, specMathMode);
        // initialize helper objects
        this.resolverManager =
            new JMLResolverManager(this.javaInfo, specInClass, selfVar, this.exc);

        // initialize namespaces
        resolverManager.pushLocalVariablesNamespace();
        if (paramVars != null) {
            resolverManager.putIntoTopLocalVariablesNamespace(paramVars);
        }
        if (resultVar != null) {
            resolverManager.putIntoTopLocalVariablesNamespace(resultVar);
        }
    }

    // region accept helpers
    @SuppressWarnings("unchecked")
    private <T> T accept(@Nullable ParserRuleContext ctx) {
        if (ctx == null) {
            return null;
        }
        return (T) ctx.accept(this);
    }

    @SuppressWarnings("unchecked")
    private <T> List<T> mapOf(List<? extends ParserRuleContext> contexts) {
        return contexts.stream().map(it -> (T) accept(it)).collect(Collectors.toList());
    }

    @SuppressWarnings("unchecked")
    private <T> ImmutableList<T> listOf(List<? extends ParserRuleContext> contexts) {
        ImmutableList<T> seq = ImmutableSLList.nil();
        for (ParserRuleContext context : contexts) {
            seq = seq.append((T) accept(context));
        }
        return seq;
    }

    private <T> T oneOf(ParserRuleContext... contexts) {
        for (ParserRuleContext context : requireNonNull(contexts)) {
            T t = accept(context);
            if (t != null) {
                return t;
            }
        }
        return null;
    }
    // endregion

    private LocationVariable getBaseHeap() {
        return services.getTypeConverter().getHeapLDT().getHeap();
    }

    private LocationVariable getSavedHeap() {
        return services.getTypeConverter().getHeapLDT().getSavedHeap();
    }

    private LocationVariable getPermissionHeap() {
        return services.getTypeConverter().getHeapLDT().getPermissionHeap();
    }

    /**
     * Converts a term so that all of its non-rigid operators refer to the pre-state of the current
     * method.
     */
    private Term convertToOld(final Term term) {
        assert atPres != null && atPres.get(getBaseHeap()) != null;
        Map<Term, Term> map = new LinkedHashMap<>();
        for (LocationVariable var : atPres.keySet()) {
            // caution: That may now also be other variables than only heaps.
            Term varAtPre = atPres.get(var);
            if (varAtPre != null) {
                map.put(tb.var(var), varAtPre);
            }
        }
        OpReplacer or = new OpReplacer(map, tb.tf());
        return or.replace(term);
    }

    /**
     * Converts a term so that all of its non-rigid operators refer to the pre-state of the current
     * block ().
     */
    private Term convertToBefore(final Term term) {
        assert atBefores != null && atBefores.get(getBaseHeap()) != null;
        Map<Term, Term> map = new LinkedHashMap<>();
        for (LocationVariable var : atBefores.keySet()) {
            // caution: That may now also be other variables than only heaps.
            Term varAtPre = atBefores.get(var);
            if (varAtPre != null) {
                map.put(tb.var(var), varAtPre);
            }
        }
        OpReplacer or = new OpReplacer(map, tb.tf());
        return or.replace(term);
    }

    private Term convertToBackup(Term term) {
        assert atPres != null && atPres.get(getSavedHeap()) != null;
        Map<Term, Term> map = new LinkedHashMap<>();
        map.put(tb.var(getBaseHeap()), tb.var(getSavedHeap()));
        if (atPres.get(getBaseHeap()) != null) {
            map.put(atPres.get(getBaseHeap()), atPres.get(getSavedHeap()));
        }
        OpReplacer or = new OpReplacer(map, tb.tf());
        return or.replace(term);
    }

    private Term convertToPermission(Term term, ParserRuleContext ctx) {
        LocationVariable permissionHeap = getPermissionHeap();
        if (permissionHeap == null) {
            raiseError("\\permission expression used in a non-permission"
                + " context and permissions not enabled.", ctx);
        }
        if (!term.op().name().toString().endsWith("::select")) {
            raiseError("\\permission expression used with non store-ref" + " expression.", ctx);
        }
        return tb.select(services.getTypeConverter().getPermissionLDT().targetSort(),
            tb.var(getPermissionHeap()), term.sub(1), term.sub(2));
    }

    private String createSignatureString(ImmutableList<SLExpression> signature) {
        if (signature == null || signature.isEmpty()) {
            return "";
        }
        StringBuilder sigString = new StringBuilder();

        for (SLExpression expr : signature) {
            final KeYJavaType t = expr.getType();
            sigString.append(t == null ? "<unknown type>" : t.getFullName()).append(", ");
        }

        return sigString.substring(0, sigString.length() - 2);
    }

    // region expression
    @Override
    public SLExpression visitPrimaryLbl(JmlParser.PrimaryLblContext ctx) {
        SLExpression expr = accept(ctx.expression());
        var label = ctx.ident().getText();
        var term = tb.label(expr.getTerm(), new SpecNameLabel(label));
        return new SLExpression(term);
    }

    @Override
    public KeYJavaType visitBuiltintype(JmlParser.BuiltintypeContext ctx) {
        if (ctx.BYTE() != null) {
            return javaInfo.getKeYJavaType(PrimitiveType.JAVA_BYTE);
        }
        if (ctx.SHORT() != null) {
            return javaInfo.getKeYJavaType(PrimitiveType.JAVA_SHORT);
        }
        if (ctx.INT() != null) {
            return javaInfo.getKeYJavaType(PrimitiveType.JAVA_INT);
        }
        if (ctx.LONG() != null) {
            return javaInfo.getKeYJavaType(PrimitiveType.JAVA_LONG);
        }
        if (ctx.BOOLEAN() != null) {
            return javaInfo.getKeYJavaType(PrimitiveType.JAVA_BOOLEAN);
        }
        if (ctx.VOID() != null) {
            return KeYJavaType.VOID_TYPE;
        }
        if (ctx.BIGINT() != null) {
            return javaInfo.getKeYJavaType(PrimitiveType.JAVA_BIGINT);
        }
        if (ctx.REAL() != null) {
            return javaInfo.getKeYJavaType(PrimitiveType.JAVA_REAL);
        }
        if (ctx.LOCSET() != null) {
            return javaInfo.getKeYJavaType(PrimitiveType.JAVA_LOCSET);
        }
        if (ctx.SEQ() != null) {
            return javaInfo.getKeYJavaType(PrimitiveType.JAVA_SEQ);
        }
        if (ctx.FREE() != null) {
            return javaInfo.getKeYJavaType(PrimitiveType.JAVA_FREE_ADT);
        }
        raiseError(ctx, "Unknown builtin type.");
        return null;
    }


    private <T> ImmutableList<T> append(ImmutableList<T> by, ParserRuleContext ctx) {
        return by.append((T) accept(ctx));
    }

    private ImmutableList<Term> append(ImmutableList<Term> target,
            List<JmlParser.InfflowspeclistContext> ctx) {
        for (ParserRuleContext c : ctx) {
            ImmutableList<Term> t = accept(c);
            target = target.append(t);
        }
        return target;
    }

    private @Nullable String accept(@Nullable TerminalNode ident) {
        if (ident == null) {
            return null;
        }
        return ident.getText();
    }

    @Override
    public Term visitTermexpression(JmlParser.TermexpressionContext ctx) {
        return ((SLExpression) requireNonNull(accept(ctx.expression()))).getTerm();
    }

    @Override
    public Object visitStoreRefUnion(JmlParser.StoreRefUnionContext ctx) {
        final ImmutableList<Term> seq = requireNonNull(accept(ctx.storeRefList()));
        if (seq.size() == 1) {
            return seq.head();
        } else {
            return tb.union(seq);
        }
    }


    @Override
    public ImmutableList<Term> visitStoreRefList(JmlParser.StoreRefListContext ctx) {
        ImmutableList<Term> result = ImmutableSLList.nil();
        for (JmlParser.StorerefContext context : ctx.storeref()) {
            result = result.append((Term) accept(context));
        }
        return result;
    }

    @Override
    public Object visitStoreRefIntersect(JmlParser.StoreRefIntersectContext ctx) {
        return tb.intersect((Iterable<Term>) requireNonNull(accept(ctx.storeRefList())));
    }

    @Override
    public Object visitStoreref(JmlParser.StorerefContext ctx) {
        if (null != ctx.NOTHING()) {
            return tb.empty();
        }
        if (null != ctx.EVERYTHING()) {
            return tb.createdLocs();
        }
        if (null != ctx.NOT_SPECIFIED()) {
            return tb.createdLocs();
        }
        if (null != ctx.STRICTLY_NOTHING()) {
            return tb.strictlyNothing();
        } else {
            return accept(ctx.storeRefExpr());
        }
    }

    @Override
    public Object visitCreateLocset(JmlParser.CreateLocsetContext ctx) {
        return termFactory.createLocSet(requireNonNull(accept(ctx.exprList())));
    }


    @Override
    public ImmutableList<SLExpression> visitExprList(JmlParser.ExprListContext ctx) {
        ImmutableList<SLExpression> result = ImmutableSLList.nil();
        for (JmlParser.ExpressionContext context : ctx.expression()) {
            result = result.append((SLExpression) accept(context));
        }
        return result;
    }

    @Override
    public Term visitStoreRefExpr(JmlParser.StoreRefExprContext ctx) {
        return termFactory.createStoreRef(requireNonNull(accept(ctx.expression())));
    }


    @Override
    public SLExpression visitPredornot(JmlParser.PredornotContext ctx) {
        if (ctx.predicate() != null) {
            return accept(ctx.predicate());
        }
        if (ctx.NOT_SPECIFIED() != null) {
            return new SLExpression(
                termFactory.createSkolemExprBool(ctx.NOT_SPECIFIED().getText()).getTerm());
        }
        if (ctx.SAME() != null) {
            raiseError("'\\same' is currently not supported", ctx);
            return null;
        }
        raiseError(ctx, "Unknown syntax case.");
        return null;
    }

    @Override
    public Object visitPredicate(JmlParser.PredicateContext ctx) {
        SLExpression expr = accept(ctx.expression());
        assert expr != null;
        if (!expr.isTerm() && expr.getTerm().sort() == Sort.FORMULA) {
            raiseError("Expected a formula: " + expr, ctx);
        }
        return expr;
    }

    @Override
    public SLExpression visitExpression(JmlParser.ExpressionContext ctx) {
        SLExpression result = accept(ctx.conditionalexpr());
        assert result != null;
        if (!result.isTerm()) {
            raiseError("Expected a term: " + result, ctx);
        }
        return result;
    }

    @Override
    public SLExpression visitConditionalexpr(JmlParser.ConditionalexprContext ctx) {
        SLExpression cond = accept(ctx.equivalenceexpr());
        if (ctx.conditionalexpr().isEmpty()) {
            return cond;
        }
        SLExpression then = accept(ctx.conditionalexpr(0));
        SLExpression else_ = accept(ctx.conditionalexpr(1));
        assert else_ != null;
        assert then != null;
        assert cond != null;
        return termFactory.ite(cond, then, else_);
    }

    @Override
    public Object visitEquivalenceexpr(JmlParser.EquivalenceexprContext ctx) {
        List<SLExpression> e = mapOf(ctx.impliesexpr());
        SLExpression result = e.get(0);
        for (int i = 1; i < e.size(); i++) {
            String op = ctx.EQV_ANTIV(i - 1).getText();
            SLExpression expr = e.get(i);
            if (op.equals("<==>")) {
                result = termFactory.equivalence(result, expr);
            } else {
                result = termFactory.antivalence(result, expr);
            }
        }
        return result;
    }

    /*
     * Note: According to JML Manual 12.6.3 forward implication has to be parsed right-associatively
     * and backward implication left-associatively.
     */
    @Override
    public Object visitImpliesexpr(JmlParser.ImpliesexprContext ctx) {
        SLExpression result = accept(ctx.a);
        if (ctx.IMPLIES() != null) {
            SLExpression expr = accept(ctx.b);
            assert expr != null;
            assert result != null;
            result = new SLExpression(
                tb.imp(tb.convertToFormula(result.getTerm()), tb.convertToFormula(expr.getTerm())));
        }
        if (!ctx.IMPLIESBACKWARD().isEmpty()) {
            List<SLExpression> exprs = mapOf(ctx.c);
            for (SLExpression expr : exprs) {
                assert result != null;
                result = new SLExpression(tb.imp(tb.convertToFormula(expr.getTerm()),
                    tb.convertToFormula(result.getTerm())));
            }
        }
        assert result != null;
        return result;
    }

    @Override
    public SLExpression visitImpliesforwardexpr(JmlParser.ImpliesforwardexprContext ctx) {
        SLExpression result = accept(ctx.a);
        if (ctx.b != null) {
            SLExpression expr = accept(ctx.b);
            assert expr != null;
            assert result != null;
            return new SLExpression(
                tb.imp(tb.convertToFormula(result.getTerm()), tb.convertToFormula(expr.getTerm())));
        }
        return result;
    }

    @Override
    public SLExpression visitLogicalorexpr(JmlParser.LogicalorexprContext ctx) {
        if (ctx.logicalandexpr().size() == 1) {
            return accept(ctx.logicalandexpr(0));
        }

        List<SLExpression> seq = mapOf(ctx.logicalandexpr());
        return seq.stream()
                .reduce((a, b) -> new SLExpression(
                    tb.orSC(tb.convertToFormula(a.getTerm()), tb.convertToFormula(b.getTerm()))))
                .orElse(null);
    }

    @Override
    public Object visitRelationalexpr(JmlParser.RelationalexprContext ctx) {
        return oneOf(ctx.shiftexpr(), ctx.instance_of(), ctx.relational_chain(),
            ctx.relational_lockset(), ctx.st_expr());
    }

    @Override
    public Object visitLogicalandexpr(JmlParser.LogicalandexprContext ctx) {
        if (ctx.inclusiveorexpr().size() == 1) {
            return accept(ctx.inclusiveorexpr(0));
        }

        List<SLExpression> seq = mapOf(ctx.inclusiveorexpr());
        return seq.stream()
                .reduce((a, b) -> new SLExpression(
                    tb.andSC(tb.convertToFormula(a.getTerm()), tb.convertToFormula(b.getTerm()))))
                .orElse(null);
    }

    @Override
    public Object visitInclusiveorexpr(JmlParser.InclusiveorexprContext ctx) {
        if (ctx.exclusiveorexpr().size() == 1) {
            return accept(ctx.exclusiveorexpr(0));
        }

        List<SLExpression> seq = mapOf(ctx.exclusiveorexpr());
        SLExpression result = seq.get(0);
        for (int i = 1; i < seq.size(); i++) {
            SLExpression expr = seq.get(i);
            result = termFactory.binary(BITWISE_OR, result, expr);
        }
        return result;
    }

    @Override
    public Object visitExclusiveorexpr(JmlParser.ExclusiveorexprContext ctx) {
        if (ctx.andexpr().size() == 1) {
            return accept(ctx.andexpr(0));
        }

        List<SLExpression> exprs = mapOf(ctx.andexpr());
        SLExpression result = exprs.get(0);
        for (int i = 1; i < exprs.size(); i++) {
            SLExpression expr = exprs.get(i);
            result = termFactory.binary(BITWISE_XOR, result, expr);
        }
        return result;
    }

    @Override
    public Object visitAndexpr(JmlParser.AndexprContext ctx) {
        if (ctx.equalityexpr().size() == 1) {
            return accept(ctx.equalityexpr(0));
        }

        List<SLExpression> exprs = mapOf(ctx.equalityexpr());
        SLExpression result = exprs.get(0);
        for (int i = 1; i < exprs.size(); i++) {
            SLExpression expr = exprs.get(i);
            try {
                result = termFactory.binary(BITWISE_AND, result, expr);
            } catch (RuntimeException ex) {
                raiseError(ctx, ex);
            }
        }
        return result;
    }

    @Override
    public SLExpression visitEqualityexpr(JmlParser.EqualityexprContext ctx) {
        List<SLExpression> expr = mapOf(ctx.relationalexpr());
        SLExpression result = expr.get(0);

        // Does this chaining make sense at all? eq results in a formula?!
        for (int i = 1; i < expr.size(); i++) {
            TerminalNode tok = ctx.EQ_NEQ(i - 1);
            // floats require special casing for == and !=
            SLExpression floatResult = floatEqualityExpr(tok.getText(), result, expr.get(i));
            if (floatResult != null) {
                return floatResult;
            }
            if (tok.getText().equals("==")) {
                result = termFactory.eq(result, expr.get(i));
            } else {
                result = termFactory.neq(result, expr.get(i));
            }
        }
        return result;
    }

    private SLExpression floatEqualityExpr(String img, SLExpression lhs, SLExpression rhs) {
        if (lhs.getType() == null || rhs.getType() == null) {
            return null;
        }
        Type lhsTy = lhs.getType().getJavaType();
        Type rhsTy = lhs.getType().getJavaType();
        if (rhsTy != PrimitiveType.JAVA_DOUBLE && rhsTy != PrimitiveType.JAVA_FLOAT
                && lhsTy != PrimitiveType.JAVA_DOUBLE && lhsTy != PrimitiveType.JAVA_FLOAT) {
            return null;
        }
        KeYJavaType promotedType =
            services.getTypeConverter().getPromotedType(lhs.getType(), rhs.getType());

        if (lhs.getType() != promotedType) {
            lhs = termFactory.cast(promotedType, lhs);
        }
        if (rhs.getType() != promotedType) {
            rhs = termFactory.cast(promotedType, rhs);
        }

        if (img.equals("==")) {
            return termFactory.fpEq(lhs, rhs);
        } else {
            return termFactory.fpNeq(lhs, rhs);
        }
    }

    @Override
    public SLExpression visitInstance_of(JmlParser.Instance_ofContext ctx) {
        SLExpression result = accept(ctx.shiftexpr());
        KeYJavaType rtype = accept(ctx.typespec());
        assert rtype != null;
        SortDependingFunction f = rtype.getSort().getInstanceofSymbol(services);
        // instanceof-expression
        assert result != null;
        return new SLExpression(tb.and(tb.not(tb.equals(result.getTerm(), tb.NULL())),
            tb.equals(tb.func(f, result.getTerm()), tb.TRUE())));
    }

    @Override
    public Object visitSt_expr(JmlParser.St_exprContext ctx) {
        SLExpression result = accept(ctx.shiftexpr(0));
        SLExpression right = accept(ctx.shiftexpr(1));
        assert result != null && right != null;

        if (result.isTerm() || right.isTerm()) {
            raiseError("Cannot build subtype expression from terms.", ctx);
        }
        assert result.isType();
        assert right.isType();
        if (result.getTerm() == null) {
            exc.addIgnoreWarning("subtype expression <: only supported for"
                + " \\typeof() arguments on the left side.", ctx.ST().getSymbol());
            final Namespace<Function> fns = services.getNamespaces().functions();
            int x = -1;
            Name name;
            do {
                name = new Name("subtype_" + ++x);
            } while (fns.lookup(name) != null);
            final Function z = new Function(name, Sort.FORMULA);
            fns.add(z);
            result = new SLExpression(tb.func(z));
        } else {
            Sort os = right.getType().getSort();
            Function ioFunc = os.getInstanceofSymbol(services);
            result = new SLExpression(tb.equals(tb.func(ioFunc, result.getTerm()), tb.TRUE()));
        }
        return result;
    }


    @Override
    public Object visitRelational_lockset(JmlParser.Relational_locksetContext ctx) {
        Function f = null;
        SLExpression left = accept(ctx.shiftexpr());
        SLExpression right = accept(ctx.postfixexpr());

        if (ctx.LOCKSET_LEQ() != null) {
            exc.addIgnoreWarning("Lockset ordering is not supported",
                ctx.LOCKSET_LEQ().getSymbol());
            final Sort objSort = services.getJavaInfo().getJavaLangObject().getSort();
            f = new Function(new Name("lockset_leq"), Sort.FORMULA, objSort, objSort);
        }
        if (ctx.LOCKSET_LT() != null) {
            exc.addIgnoreWarning("Lockset ordering is not supported", ctx.LOCKSET_LT().getSymbol());
            final Sort objSort = services.getJavaInfo().getJavaLangObject().getSort();
            f = new Function(new Name("lockset_lt"), Sort.FORMULA, objSort, objSort);
        }
        assert f != null;
        assert right != null;
        assert left != null;
        return new SLExpression(tb.func(f, left.getTerm(), right.getTerm()));
    }

    @Override
    public SLExpression visitRelational_chain(JmlParser.Relational_chainContext ctx) {
        List<SLExpression> expressions = mapOf(ctx.shiftexpr());
        SLExpression result = null;
        for (int i = 1; i < expressions.size(); i++) {
            Token opToken = ctx.op.get(i - 1);
            JMLOperator jop = JMLOperator.get(opToken.getText());
            SLExpression left = expressions.get(i - 1);
            SLExpression right = expressions.get(i);
            try {
                SLExpression rel = termFactory.binary(jop, left, right);
                if (result != null) {
                    result = new SLExpression(tb.and(result.getTerm(), rel.getTerm()));
                } else {
                    result = rel;
                }
            } catch (RuntimeException ex) {
                raiseError(ctx, ex);
            }
        }
        assert result != null;
        return result;
    }


    @Override
    public Object visitShiftexpr(JmlParser.ShiftexprContext ctx) {
        List<SLExpression> e = mapOf(ctx.additiveexpr());
        SLExpression result = e.get(0);
        for (int i = 1; i < e.size(); i++) {
            String opToken = ctx.op.get(i - 1).getText();
            SLExpression expr = e.get(i);
            JMLOperator op = JMLOperator.get(opToken);
            try {
                result = termFactory.binary(op, result, expr);
            } catch (RuntimeException ex) {
                raiseError(ctx, ex);
            }
        }
        return result;
    }

    @Override
    public Object visitAdditiveexpr(JmlParser.AdditiveexprContext ctx) {
        List<SLExpression> exprs = mapOf(ctx.multexpr());
        SLExpression result = exprs.get(0);
        for (int i = 1; i < exprs.size(); i++) {
            SLExpression expr = exprs.get(i);
            String opToken = ctx.op.get(i - 1).getText();
            JMLOperator op = JMLOperator.get(opToken);
            try {
                result = termFactory.binary(op, result, expr);
            } catch (RuntimeException ex) {
                raiseError(ctx, ex);
            }
        }
        return result;
    }

    @Override
    public Object visitMultexpr(JmlParser.MultexprContext ctx) {
        List<SLExpression> exprs = mapOf(ctx.unaryexpr());
        SLExpression result = exprs.get(0);
        for (int i = 1; i < exprs.size(); i++) {
            Token op = ctx.op.get(i - 1);
            SLExpression e = exprs.get(i);
            if (result.isType()) {
                raiseError("Cannot build multiplicative expression from type "
                    + result.getType().getName() + ".", ctx);
            }
            if (e.isType()) {
                raiseError("Cannot multiply by type " + e.getType().getName() + ".", ctx);
            }
            JMLOperator jop = get(op.getText());
            try {
                result = termFactory.binary(jop, result, e);
            } catch (RuntimeException ex) {
                raiseError(ctx, ex);
            }
        }
        return result;
    }

    @Override
    public SLExpression visitUnaryexpr(JmlParser.UnaryexprContext ctx) {
        if (ctx.PLUS() != null) {
            // This allows also "+null" to be parsed as "null". But that is not
            // so terrible perhaps.
            SLExpression result = accept(ctx.unaryexpr());
            assert result != null;
            if (result.isType()) {
                raiseError("Cannot build  +" + result.getType().getName() + ".", ctx);
            }
            assert result.isTerm();
            return result;
        }
        if (ctx.DECLITERAL() != null) {
            String text = ctx.getText();
            boolean isLong = text.endsWith("l") || text.endsWith("L");
            try {
                Literal literal = isLong ? new LongLiteral(text) : new IntLiteral(text);
                Term intLit =
                    services.getTypeConverter().getIntegerLDT().translateLiteral(literal, services);

                PrimitiveType literalType =
                    isLong ? PrimitiveType.JAVA_LONG : PrimitiveType.JAVA_INT;
                return new SLExpression(intLit, javaInfo.getPrimitiveKeYJavaType(literalType));
            } catch (NumberFormatException e) {
                raiseError(ctx, e);
            }
        }
        if (ctx.MINUS() != null) {
            SLExpression result = accept(ctx.unaryexpr());
            assert result != null;
            if (result.isType()) {
                raiseError("Cannot build  -" + result.getType().getName() + ".", ctx);
            }
            assert result.isTerm();
            try {
                return termFactory.unary(UNARY_MINUS, result);
            } catch (RuntimeException e) {
                raiseError(ctx, e);
            }
        }
        return oneOf(ctx.castexpr(), ctx.unaryexprnotplusminus());
    }

    @Override
    public SLExpression visitCastexpr(JmlParser.CastexprContext ctx) {
        KeYJavaType rtype = accept(ctx.typespec());
        SLExpression result = accept(ctx.unaryexpr());
        return termFactory.cast(rtype, result);
    }

    @Override
    public Object visitUnaryexprnotplusminus(JmlParser.UnaryexprnotplusminusContext ctx) {
        if (ctx.NOT() != null) {
            SLExpression e = accept(ctx.unaryexpr());
            assert e != null;
            if (e.isType()) {
                raiseError("Cannot negate type " + e.getType().getName() + ".", ctx);
            }
            Term t = e.getTerm();
            if (t.sort() == Sort.FORMULA) {
                return new SLExpression(tb.not(t));
            } else if (t.sort() == booleanLDT.targetSort()) {
                return new SLExpression(tb.not(tb.equals(t, tb.TRUE())));
            } else {
                raiseError("Wrong type in not-expression: " + t, ctx);
            }
        }

        if (ctx.BITWISENOT() != null) {
            SLExpression e = accept(ctx.unaryexpr());
            assert e != null;
            if (e.isType()) {
                raiseError("Cannot negate type " + e.getType().getName() + ".", ctx);
            }
            try {
                return termFactory.unary(BITWISE_NEGATE, e);
            } catch (RuntimeException ex) {
                raiseError(ctx, ex);
            }
        }
        return accept(ctx.postfixexpr());
    }

    @Override
    public SLExpression visitTransactionUpdated(JmlParser.TransactionUpdatedContext ctx) {
        String fieldName = "<transactionConditionallyUpdated>";
        return lookupIdentifier(fieldName, accept(ctx.expression()), null, ctx);
    }


    @Override
    public SLExpression visitPostfixexpr(JmlParser.PostfixexprContext ctx) {
        String oldFqName = fullyQualifiedName;
        fullyQualifiedName = "";
        SLExpression expr = accept(ctx.primaryexpr());

        for (JmlParser.PrimarysuffixContext c : ctx.primarysuffix()) {
            receiver = expr;
            expr = accept(c);
        }

        if (expr == null) {
            raiseError(
                format("The fully qualified name '%s' could not be resolved.", fullyQualifiedName),
                ctx);
        }
        fullyQualifiedName = oldFqName;
        return expr;
    }

    @Override
    public Object visitIdent(JmlParser.IdentContext ctx) {
        if (ctx.THIS() != null) {
            if (selfVar == null) {
                raiseError("Cannot access \"this\" in a static context", ctx);
            }
            return getThisReceiver();
        }
        if (ctx.SUPER() != null) {
            raiseError("\"super\" is currently not supported", ctx);
        }
        appendToFullyQualifiedName(ctx.getText());
        return lookupIdentifier(ctx.getText(), null, null, ctx);
    }

    @Override
    public Object visitInv(JmlParser.InvContext ctx) {
        return termFactory.createInv(selfVar == null ? null : tb.var(selfVar), containerType);
    }

    @Override
    public Object visitInv_free(JmlParser.Inv_freeContext ctx) {
        return termFactory.createInvFree(selfVar == null ? null : tb.var(selfVar), containerType);
    }


    @Override
    public Object visitTrue_(JmlParser.True_Context ctx) {
        return new SLExpression(tb.tt());
    }

    @Override
    public Object visitFalse_(JmlParser.False_Context ctx) {
        return new SLExpression(tb.ff());
    }

    @Override
    public Object visitNull_(JmlParser.Null_Context ctx) {
        return new SLExpression(tb.NULL());
    }

    @Override
    public Object visitThis_(JmlParser.This_Context ctx) {
        if (selfVar == null) {
            raiseError("Cannot access \"this\" in a static context!", ctx);
        }
        return getThisReceiver();
    }

    @Nonnull
    private SLExpression getThisReceiver() {
        return new SLExpression(tb.var(selfVar), selfVar.getKeYJavaType());
    }

    private SLExpression lookupIdentifier(String lookupName, SLExpression receiver,
            SLParameters params, ParserRuleContext ctx) {
        exc.updatePosition(ctx.start);

        SLExpression result = null;
        try {
            result = resolverManager.resolve(receiver, lookupName, params);
        } catch (SLTranslationException | ClassCastException ignored) {
            // no type name found maybe package?
        }

        if (result != null) {
            return result;
        }

        // no identifier found, maybe it was just a package prefix.
        // but package prefixes don't have a receiver!
        // Let primarysuffix handle faulty method call.
        if (receiver != null && params == null) {
            raiseError(format("Identifier %s not found: %s", lookupName, lookupName), ctx);
        }
        return null;
    }

    // region suffix

    // receiver value of attribute access, functions calls or array access
    private SLExpression receiver;
    private String fullyQualifiedName;

    @Override
    public SLExpression visitPrimarySuffixAccess(JmlParser.PrimarySuffixAccessContext ctx) {
        SLExpression receiver = this.receiver;
        String lookupName;
        boolean methodCall = ctx.LPAREN() != null;

        SLParameters params = null;
        if (methodCall) {
            params = visitParameters(ctx.expressionlist());
        }

        if (ctx.IDENT() != null) {
            String id = ctx.IDENT().getText();
            if (receiver == null) {
                // Receiver was only a package/classname prefix
                lookupName = fullyQualifiedName + "." + id;
            } else {
                lookupName = id;
            }
            fullyQualifiedName = fullyQualifiedName + "." + id;
            try {
                return lookupIdentifier(lookupName, receiver, params, ctx);
            } catch (Exception e) {
                return lookupIdentifier(fullyQualifiedName, null, null, ctx);
            }
        }
        if (ctx.TRANSIENT() != null) {
            assert !methodCall;
            if (receiver == null) {
                raiseError("Unknown reference to " + fullyQualifiedName, ctx);
            }
            return lookupIdentifier("<transient>", receiver, null, ctx);
        }
        if (ctx.THIS() != null) {
            assert !methodCall;
            if (receiver == null) {
                raiseError("Unknown reference to " + fullyQualifiedName, ctx);
            }
            return new SLExpression(
                services.getTypeConverter().findThisForSort(receiver.getType().getSort(),
                    tb.var(selfVar), javaInfo.getKeYJavaType(selfVar.sort()), true),
                receiver.getType());
        }
        if (ctx.INV() != null) {
            assert !methodCall;
            if (receiver == null) {
                raiseError("Unknown reference to " + fullyQualifiedName, ctx);
            }
            return termFactory.createInv(receiver.getTerm(), receiver.getType());
        }
        if (ctx.INV_FREE() != null) {
            assert !methodCall;
            if (receiver == null) {
                raiseError("Unknown reference to " + fullyQualifiedName, ctx);
            }
            return termFactory.createInvFree(receiver.getTerm(), receiver.getType());
        }
        if (ctx.MULT() != null) {
            assert !methodCall;
            if (receiver == null) {
                raiseError("Unknown reference to " + fullyQualifiedName, ctx);
            }
            return new SLExpression(tb.allFields(receiver.getTerm()),
                javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
        }
        assert false;
        return null;
    }

    @Override
    public Object visitPrimarySuffixCall(JmlParser.PrimarySuffixCallContext ctx) {
        final SLExpression receiver = this.receiver;
        String lookupName = fullyQualifiedName;

        if (fullyQualifiedName.startsWith("\\dl_")) {
            try {
                return termFactory.dlKeyword(fullyQualifiedName, accept(ctx.expressionlist()));
            } catch (Exception e) {
                raiseError(ctx, e);
            }
        }
        SLParameters params = visitParameters(ctx.expressionlist());

        lookupName = lookupName.substring(lookupName.lastIndexOf('.') + 1);

        SLExpression result = lookupIdentifier(lookupName, receiver, params, ctx);
        if (result == null) {
            if (fullyQualifiedName.indexOf('.') < 0 && selfVar != null) {
                // resolve by prefixing an `this.`
                result = lookupIdentifier(lookupName, getThisReceiver(), params, ctx);
            }
            if (result == null) {
                raiseError(format("Method %s(%s) not found!", lookupName,
                    createSignatureString(params.getParameters())), ctx);
            }
        }
        if (((IProgramMethod) result.getTerm().op()).getStateCount() > 1
                && (atPres == null || atPres.get(getBaseHeap()) == null)) {
            raiseError("Two-state model method " + lookupName + " not allowed in this context!",
                ctx);
        }
        return result;
    }

    private SLParameters visitParameters(JmlParser.Param_listContext ctx) {
        ImmutableList<SLExpression> params =
            ctx.param_decl().stream().map(it -> lookupIdentifier(it.p.getText(), null, null, it))
                    .collect(ImmutableSLList.toImmutableList());
        return getSlParametersWithHeap(params);
    }

    private SLParameters visitParameters(JmlParser.ExpressionlistContext ctx) {
        ImmutableList<SLExpression> params = accept(ctx);
        return getSlParametersWithHeap(params);
    }

    private SLParameters getSlParametersWithHeap(ImmutableList<SLExpression> params) {
        ImmutableList<SLExpression> preHeapParams = ImmutableSLList.nil();
        for (LocationVariable heap : HeapContext.getModHeaps(services, false)) {
            Term p;
            if (atPres == null || atPres.get(heap) == null) {
                p = tb.var(heap);
            } else {
                p = atPres.get(heap);
            }
            preHeapParams = preHeapParams.append(new SLExpression(p));
        }
        params = (params == null) ? preHeapParams : params.prepend(preHeapParams);
        return new SLParameters(params);
    }

    @Override
    public Object visitPrimarySuffixArray(JmlParser.PrimarySuffixArrayContext ctx) {
        SLExpression curReceiver = receiver;
        SLExpression rangeFrom = accept(ctx.from);
        SLExpression rangeTo = accept(ctx.to);
        return termFactory.arrayRef(curReceiver, fullyQualifiedName, rangeFrom, rangeTo);
    }
    // endregion

    @Override
    public Object visitNew_expr(JmlParser.New_exprContext ctx) {
        raiseError("Object creation with 'new' is not supported specifications.", ctx);
        return null;
    }

    @Override
    public Object visitArray_initializer(JmlParser.Array_initializerContext ctx) {
        raiseError("Array Initializer are currently not allowed in JML specifications.", ctx);
        return null;
    }

    @Override
    public ImmutableList<SLExpression> visitExpressionlist(JmlParser.ExpressionlistContext ctx) {
        return listOf(ctx.expression());
    }

    @Override
    public SLExpression visitStringliteral(JmlParser.StringliteralContext ctx) {
        Token l = ctx.STRING_LITERAL().getSymbol();
        Term charListTerm =
            services.getTypeConverter().convertToLogicElement(new StringLiteral(l.getText()));
        Function strPool = services.getNamespaces().functions().lookup(CharListLDT.STRINGPOOL_NAME);
        if (strPool == null) {
            raiseError("String literals used in specification, but string pool function not found",
                ctx);
        }
        Term stringTerm = tb.func(strPool, charListTerm);
        return new SLExpression(stringTerm, javaInfo.getKeYJavaType("java.lang.String"));
    }

    @Override
    public SLExpression visitCharliteral(JmlParser.CharliteralContext ctx) {
        Term charLit = services.getTypeConverter().getIntegerLDT()
                .translateLiteral(new CharLiteral(ctx.getText()), services);
        return new SLExpression(charLit, javaInfo.getKeYJavaType("char"));
    }


    @Override
    public SLExpression visitIntegerliteral(JmlParser.IntegerliteralContext ctx) {
        SLExpression result = null;
        String text = ctx.getText();
        boolean isLong = text.endsWith("l") || text.endsWith("L");
        try {
            Literal literal = isLong ? new LongLiteral(text) : new IntLiteral(text);
            Term intLit =
                services.getTypeConverter().getIntegerLDT().translateLiteral(literal, services);
            PrimitiveType literalType = isLong ? PrimitiveType.JAVA_LONG : PrimitiveType.JAVA_INT;
            result = new SLExpression(intLit, javaInfo.getPrimitiveKeYJavaType(literalType));
        } catch (NumberFormatException e) {
            raiseError(ctx, e);
        }
        return result;
    }

    @Override
    public SLExpression visitFractionalliteral(JmlParser.FractionalliteralContext ctx) {
        SLExpression result = null;
        String text = ctx.getText();
        try {
            if (ctx.FLOAT_LITERAL() != null) {
                Term floatLit = services.getTypeConverter().getFloatLDT()
                        .translateLiteral(new FloatLiteral(text), services);
                result = new SLExpression(floatLit,
                    javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_FLOAT));
            } else if (ctx.DOUBLE_LITERAL() != null) {
                Term doubleLit = services.getTypeConverter().getDoubleLDT()
                        .translateLiteral(new DoubleLiteral(text), services);
                result = new SLExpression(doubleLit,
                    javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_DOUBLE));
            } else if (ctx.REAL_LITERAL() != null) {
                throw new Error("not yet implemented; needed real ldt");
            } else {
                raiseError(ctx, "Unexpected literal %s", text);
            }
        } catch (NumberFormatException ex) {
            raiseError(ctx, ex);
        }

        return result;
    }

    @Override
    public Object visitPrimaryResult(JmlParser.PrimaryResultContext ctx) {
        if (resultVar == null) {
            raiseError("\\result used in wrong context", ctx);
        }
        appendToFullyQualifiedName("\\result");
        return new SLExpression(tb.var(resultVar), resultVar.getKeYJavaType());
    }

    private void appendToFullyQualifiedName(String suffix) {
        if (fullyQualifiedName.isEmpty()) {
            fullyQualifiedName = suffix;
        } else {
            fullyQualifiedName += "." + suffix;
        }
    }

    @Override
    public Object visitPrimaryException(JmlParser.PrimaryExceptionContext ctx) {
        if (excVar == null) {
            raiseError("\\exception may only appear in determines clauses", ctx);
        }
        return new SLExpression(tb.var(excVar), excVar.getKeYJavaType());
    }

    @Override
    public Object visitPrimaryBackup(JmlParser.PrimaryBackupContext ctx) {
        SLExpression result = accept(ctx.expression());
        if (atPres == null || atPres.get(getSavedHeap()) == null) {
            raiseError("JML construct \\backup not allowed in this context.", ctx);
        }
        assert result != null;
        Object typ = result.getType();
        if (typ != null) {
            result = new SLExpression(convertToBackup(result.getTerm()), result.getType());
        } else {
            result = new SLExpression(convertToBackup(result.getTerm()));
        }
        return result;
    }

    @Override
    public Object visitPrimaryPermission(JmlParser.PrimaryPermissionContext ctx) {
        return new SLExpression(convertToPermission(
            ((SLExpression) requireNonNull(accept(ctx.expression()))).getTerm(), ctx));
    }

    @Override
    public Object visitPrimaryNNE(JmlParser.PrimaryNNEContext ctx) {
        SLExpression result = accept(ctx.expression());
        assert result != null;
        Term t = result.getTerm();
        Term resTerm = tb.not(tb.equals(t, tb.NULL()));
        if (t.sort() instanceof ArraySort) {
            LogicVariable i = new LogicVariable(new Name("i"),
                javaInfo.getKeYJavaType(PrimitiveType.JAVA_INT).getSort());

            // See JML reference manual
            // http://www.cs.iastate.edu/~leavens/JML/jmlrefman/jmlrefman_11.html#SEC139
            Term range = tb.and(tb.leq(tb.zero(), tb.var(i)), tb.lt(tb.var(i), tb.dotLength(t)));
            Term body = tb.equals(tb.dotArr(t, tb.var(i)), tb.NULL());
            body = tb.not(body);
            body = tb.imp(range, body);

            result = new SLExpression(tb.and(resTerm, tb.all(i, body)));
        } else {
            raiseError("\\nonnullelements may only be applied to arrays", ctx);
        }
        return result;
    }

    @Override
    public SLExpression visitPrimaryInformalDesc(JmlParser.PrimaryInformalDescContext ctx) {
        return termFactory.commentary(ctx.INFORMAL_DESCRIPTION().getText(), selfVar, resultVar,
            paramVars, atPres == null ? null : atPres.get(getBaseHeap()));
    }

    @Override
    public Object visitPrimaryMapEmpty(JmlParser.PrimaryMapEmptyContext ctx) {
        return termFactory.translateMapExpressionToJDL(ctx.MAPEMPTY().getText(), null/* ? */,
            services);
    }

    @Override
    public SLExpression visitPrimaryMapExpr(JmlParser.PrimaryMapExprContext ctx) {
        ImmutableList<SLExpression> list = accept(ctx.expressionlist());
        Token tk = ctx.mapExpression().getStart();
        return termFactory.translateMapExpressionToJDL(tk.getText(), list, services);
    }

    @Override
    public SLExpression visitPrimarySeq2Map(JmlParser.PrimarySeq2MapContext ctx) {
        ImmutableList<SLExpression> list = accept(ctx.expressionlist());
        return termFactory.translateMapExpressionToJDL(ctx.SEQ2MAP().getText(), list, services);
    }

    @Override
    public Object visitPrimaryFloatingPoint(PrimaryFloatingPointContext ctx) {
        SLExpression argument = accept(ctx.expression());
        assert argument != null;
        LDT ldt = services.getTypeConverter().getLDTFor(argument.getTerm().sort());
        if (ldt == null) {
            raiseError(ctx, "LDT for %s cannot be found.", argument.getTerm().sort());
        }
        String opName = ctx.getStart().getText();
        assert opName.startsWith("\\fp_");
        Function op = ldt.getFunctionFor(opName.substring(4), services);
        if (op == null) {
            raiseError(ctx, "The operation %s has no function in %s.", opName, ldt.name());
        }

        return new SLExpression(tb.func(op, argument.getTerm()));
    }

    @Override
    public Object visitPrimaryNotMod(JmlParser.PrimaryNotModContext ctx) {
        SLExpression t = accept(ctx.storeRefUnion());
        final Term a =
            termFactory.notModified(atPres == null ? null : atPres.get(getBaseHeap()), t);
        assert a != null;
        return new SLExpression(a);
    }

    @Override
    public Object visitPrimaryNotAssigned(JmlParser.PrimaryNotAssignedContext ctx) {
        return termFactory.createSkolemExprBool(ctx.NOT_ASSIGNED().getText());
    }

    @Override
    public Object visitPrimaryFresh(JmlParser.PrimaryFreshContext ctx) {
        ImmutableList<SLExpression> list = accept(ctx.expressionlist());
        return termFactory.fresh(list, atPres);
    }

    @Override
    public SLExpression visitPrimaryReach(JmlParser.PrimaryReachContext ctx) {
        Term t = accept(ctx.storeref());
        SLExpression e1 = accept(ctx.expression(0));
        SLExpression e2 = accept(ctx.expression(1));
        SLExpression e3 = ctx.expression().size() == 3 ? accept(ctx.expression(2)) : null;
        assert e2 != null;
        assert e1 != null;
        return termFactory.reach(t, e1, e2, e3);
    }

    @Override
    public SLExpression visitPrimaryReachLocs(JmlParser.PrimaryReachLocsContext ctx) {
        Term t = accept(ctx.storeref());
        SLExpression e1 = accept(ctx.expression(0));
        SLExpression e2 = accept(ctx.expression(1));
        SLExpression e3 = ctx.expression().size() == 2 ? accept(ctx.expression(1)) : null;
        assert e1 != null;
        return termFactory.reachLocs(t, e1, e2, e3);
    }

    @Override
    public Object visitFieldarrayaccess(JmlParser.FieldarrayaccessContext ctx) {
        SLExpression base = oneOf(ctx.ident(), ctx.super_(), ctx.this_());
        String backupFullyQualifiedName = fullyQualifiedName;
        fullyQualifiedName = ctx.start.getText();
        for (JmlParser.Fieldarrayaccess_suffixContext suffx : ctx.fieldarrayaccess_suffix()) {
            base = visitFieldarrayaccess_suffix(base, suffx);
        }
        fullyQualifiedName = backupFullyQualifiedName;
        return base;
    }

    public SLExpression visitFieldarrayaccess_suffix(SLExpression base,
            JmlParser.Fieldarrayaccess_suffixContext ctx) {
        if (ctx.DOT() != null) {
            String lookupName;
            if (ctx.ident() != null) {
                String id = ctx.ident().getText();
                if (base == null) {
                    // Receiver was only a package/classname prefix
                    lookupName = fullyQualifiedName + "." + id;
                } else {
                    lookupName = id;
                }
                fullyQualifiedName = fullyQualifiedName + "." + id;
                try {
                    return lookupIdentifier(lookupName, base, null, ctx);
                } catch (Exception e) {
                    return lookupIdentifier(fullyQualifiedName, null, null, ctx);
                }
            }
            if (ctx.TRANSIENT() != null) {
                return lookupIdentifier("<transient>", base, null, ctx);
            }
            if (ctx.this_() != null) {
                return new SLExpression(
                    services.getTypeConverter().findThisForSort(base.getType().getSort(),
                        tb.var(selfVar), javaInfo.getKeYJavaType(selfVar.sort()), true),
                    base.getType());
            }
            if (ctx.INV() != null) {
                return termFactory.createInv(base.getTerm(), base.getType());
            }
        } else {
            // Array access
            SLExpression index = accept(ctx.expression());
            return termFactory.arrayRef(base, fullyQualifiedName, index, null);
        }
        assert false;
        return null;
    }

    @Override
    public SLExpression visitPrimaryCreateLocsetSingleton(
            JmlParser.PrimaryCreateLocsetSingletonContext ctx) {
        SLExpression e = accept(ctx.expression());
        assert e != null;
        try {
            Term t = e.getTerm();
            final Term objTerm = t.sub(1);
            final Term fieldTerm = t.sub(2);
            return new SLExpression(tb.singleton(objTerm, fieldTerm));
        } catch (IndexOutOfBoundsException e1) {
            raiseError(ctx, "The given expression %s is not a valid reference.", e);
        }
        return null;
    }

    @Override
    public SLExpression visitPrimaryCreateLocset(JmlParser.PrimaryCreateLocsetContext ctx) {
        List<SLExpression> aa = mapOf(ctx.fieldarrayaccess());
        List<Term> seq = aa.stream().map(termFactory::createStoreRef).collect(Collectors.toList());
        Term ret = null;
        if (seq.isEmpty()) {
            raiseError(ctx, "empty!");
        } else if (seq.size() == 1) {
            ret = seq.get(0);
        } else {
            ret = tb.union(seq);
        }
        return new SLExpression(ret, javaInfo.getKeYJavaType(PrimitiveType.JAVA_LOCSET));
    }

    @Override
    public Object visitPrimaryDuration(JmlParser.PrimaryDurationContext ctx) {
        raiseError("The \\duration function is not supported", ctx);
        return null;
    }

    @Override
    public Object visitPrimarySpace(JmlParser.PrimarySpaceContext ctx) {
        raiseError("The \\space function is not supported", ctx);
        return null;
    }

    @Override
    public Object visitPrimaryWorksingSpace(JmlParser.PrimaryWorksingSpaceContext ctx) {
        raiseError("The \\working_space function is not supported", ctx);
        return null;
    }

    @Override
    public Object visitPrimaryParen(JmlParser.PrimaryParenContext ctx) {
        return accept(ctx.expression());
    }

    @Override
    public Object visitPrimaryTypeOf(JmlParser.PrimaryTypeOfContext ctx) {
        SLExpression result = accept(ctx.expression());
        assert result != null;
        return new SLExpression(result.getTerm(), result.getType(), false);
    }

    @Override
    public Object visitPrimaryElemtype(JmlParser.PrimaryElemtypeContext ctx) {
        raiseError("The \\elemtype function is not supported", ctx);
        return null;
    }


    @Override
    public Object visitPrimayTypeSpec(JmlParser.PrimayTypeSpecContext ctx) {
        KeYJavaType typ = accept(ctx.typespec());
        assert typ != null;
        return new SLExpression(typ);
    }

    @Override
    public Object visitPrimaryLockset(JmlParser.PrimaryLocksetContext ctx) {
        return termFactory.createSkolemExprObject(ctx.LOCKSET().getText());
    }

    @Override
    public Object visitPrimaryIsInitialised(JmlParser.PrimaryIsInitialisedContext ctx) {
        KeYJavaType typ = accept(ctx.referencetype());
        assert typ != null;
        Term resTerm = tb.equals(
            tb.var(javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED, typ)),
            tb.TRUE());
        return new SLExpression(resTerm);
    }

    @Override
    public SLExpression visitPrimaryInvFor(JmlParser.PrimaryInvForContext ctx) {
        SLExpression result = accept(ctx.expression());
        assert result != null;
        return termFactory.invFor(result);
    }

    @Override
    public SLExpression visitPrimaryInvFreeFor(JmlParser.PrimaryInvFreeForContext ctx) {
        SLExpression result = accept(ctx.expression());
        assert result != null;
        return termFactory.invFreeFor(result);
    }

    @Override
    public SLExpression visitPrimaryStaticInv(JmlParser.PrimaryStaticInvContext ctx) {
        KeYJavaType typ = accept(ctx.referencetype());
        return termFactory.staticInfFor(typ);
    }

    @Override
    public SLExpression visitPrimaryStaticInvFree(JmlParser.PrimaryStaticInvFreeContext ctx) {
        KeYJavaType typ = accept(ctx.referencetype());
        return termFactory.staticInfFreeFor(typ);
    }

    @Override
    public Object visitPrimaryLblNeg(JmlParser.PrimaryLblNegContext ctx) {
        exc.addIgnoreWarning("\\lblneg", ctx.LBLNEG().getSymbol());
        return accept(ctx.expression());
    }

    @Override
    public Object visitPrimaryLblPos(JmlParser.PrimaryLblPosContext ctx) {
        exc.addIgnoreWarning("\\lblpos", ctx.LBLPOS().getSymbol());
        return accept(ctx.expression());
    }

    @Override
    public Object visitPrimaryIndex(JmlParser.PrimaryIndexContext ctx) {
        return termFactory.index();
    }

    @Override
    public Object visitPrimaryValues(JmlParser.PrimaryValuesContext ctx) {
        return termFactory.values(this.containerType);
    }

    @Override
    public Object visitPrimaryStringEq(JmlParser.PrimaryStringEqContext ctx) {
        SLExpression e1 = accept(ctx.expression(0));
        SLExpression e2 = accept(ctx.expression(1));
        Function strContent =
            services.getNamespaces().functions().lookup(CharListLDT.STRINGCONTENT_NAME);
        if (strContent == null) {
            raiseError("strings used in spec, but string content function not found", ctx);
        }
        assert e2 != null;
        assert e1 != null;
        return new SLExpression(
            tb.equals(tb.func(strContent, e1.getTerm()), tb.func(strContent, e2.getTerm())));
    }

    @Override
    public Object visitPrimaryEmptySet(JmlParser.PrimaryEmptySetContext ctx) {
        return termFactory.empty(javaInfo);
    }

    @Override
    public Object visitPrimaryStoreRef(JmlParser.PrimaryStoreRefContext ctx) {
        Term t = accept(ctx.storeRefUnion());
        assert t != null;
        return new SLExpression(t, javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
    }

    @Override
    public Object visitPrimaryUnion(JmlParser.PrimaryUnionContext ctx) {
        Term t = accept(ctx.storeRefUnion());
        return termFactory.createUnion(javaInfo, t);
    }

    @Override
    public Object visitPrimaryIntersect(JmlParser.PrimaryIntersectContext ctx) {
        Term t = accept(ctx.storeRefIntersect());
        return termFactory.createIntersect(t, javaInfo);
    }

    @Override
    public Object visitPrimarySetMinux(JmlParser.PrimarySetMinuxContext ctx) {
        Term t = accept(ctx.storeref(0));
        Term t2 = accept(ctx.storeref(1));
        assert t != null;
        return new SLExpression(tb.setMinus(t, t2),
            javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
    }

    @Override
    public Object visitPrimaryAllFields(JmlParser.PrimaryAllFieldsContext ctx) {
        SLExpression e1 = accept(ctx.expression());
        assert e1 != null;
        if (!e1.isTerm()
                || !e1.getTerm().sort().extendsTrans(services.getJavaInfo().objectSort())) {
            raiseError("Invalid argument to \\allFields: " + e1, ctx);
        }
        return new SLExpression(tb.allFields(e1.getTerm()),
            javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
    }

    @Override
    public Object visitPrimaryAllObj(JmlParser.PrimaryAllObjContext ctx) {
        Term t = accept(ctx.storeref());
        assert t != null;
        return new SLExpression(tb.allObjects(t.sub(1)),
            javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
    }

    @Override
    public Object visitPrimaryUnionInf(JmlParser.PrimaryUnionInfContext ctx) {
        addWarning(ctx,
            "!!! Deprecation Warnung: You used \\infinite_union "
                + "in the functional syntax \\infinite_union(...)."
                + "\n\tThis is deprecated and won't be valid in future versions of KeY."
                + "\n\tPlease use \\infinite_union as a binder instead: "
                + "(\\infinite_union var type; guard; store-ref-expr).");
        return createInfiniteUnion(ctx.boundvarmodifiers(), ctx.quantifiedvardecls(),
            ctx.predicate(), ctx.storeref());
    }

    @Nonnull
    private Object createInfiniteUnion(JmlParser.BoundvarmodifiersContext boundvarmodifiers,
            JmlParser.QuantifiedvardeclsContext quantifiedvardecls,
            JmlParser.PredicateContext predicate, JmlParser.StorerefContext storeref) {
        Boolean nullable = accept(boundvarmodifiers);
        Pair<KeYJavaType, ImmutableList<LogicVariable>> declVars = accept(quantifiedvardecls);
        if (declVars != null) {
            resolverManager.pushLocalVariablesNamespace();
            resolverManager.putIntoTopLocalVariablesNamespace(declVars.second, declVars.first);
        }
        SLExpression t2 = accept(predicate);
        Term t = accept(storeref);
        if (declVars != null) {
            resolverManager.popLocalVariablesNamespace();
        }
        assert declVars != null;
        return termFactory.createUnionF(Boolean.TRUE.equals(nullable), declVars, t,
            t2 == null ? tb.tt() : t2.getTerm());
    }

    @Override
    public SLExpression visitPrimaryDisjoint(JmlParser.PrimaryDisjointContext ctx) {
        ImmutableList<Term> tlist = accept(ctx.storeRefList());
        assert tlist != null;
        return termFactory.createPairwiseDisjoint(tlist);
    }

    @Override
    public SLExpression visitPrimarySubset(JmlParser.PrimarySubsetContext ctx) {
        Term t = accept(ctx.storeref(0));
        Term t2 = accept(ctx.storeref(1));
        assert t != null;
        return new SLExpression(tb.subset(t, t2));
    }

    @Override
    public SLExpression visitPrimaryNewElemsfrehs(JmlParser.PrimaryNewElemsfrehsContext ctx) {
        Term t = accept(ctx.storeref());
        assert t != null;
        return new SLExpression(tb.subset(t, tb.union(convertToOld(t),
            tb.freshLocs(atPres == null ? null : atPres.get(getBaseHeap())))));
    }

    @Override
    public SLExpression visitSequenceEmpty(JmlParser.SequenceEmptyContext ctx) {
        return new SLExpression(tb.seqEmpty());
    }

    @Override
    public SLExpression visitSequenceCreate(JmlParser.SequenceCreateContext ctx) {
        ImmutableList<SLExpression> list = accept(ctx.exprList());
        assert list != null;
        return termFactory.seqConst(list);
    }

    @Override
    public Object visitSequenceSub(JmlParser.SequenceSubContext ctx) {
        SLExpression e1 = accept(ctx.expression(0));
        SLExpression e2 = accept(ctx.expression(1));
        SLExpression e3 = accept(ctx.expression(2));
        assert e3 != null;
        assert e2 != null;
        assert e1 != null;
        return new SLExpression(tb.seqSub(e1.getTerm(), e2.getTerm(), e3.getTerm()));
    }

    @Override
    public Object visitSequenceReverse(JmlParser.SequenceReverseContext ctx) {
        SLExpression e1 = accept(ctx.expression());
        assert e1 != null;
        return new SLExpression(tb.seqReverse(e1.getTerm()));
    }

    @Override
    public Object visitSequenceReplace(JmlParser.SequenceReplaceContext ctx) {
        SLExpression e1 = accept(ctx.expression(0));
        SLExpression e2 = accept(ctx.expression(1));
        SLExpression e3 = accept(ctx.expression(2));
        // short for "e1[0..e2-1]+e3+e1[e2+1..e1.length-1]"
        final Term minusOne = tb.zTerm("-1");
        assert e2 != null;
        assert e1 != null;
        final Term ante = tb.seqSub(e1.getTerm(), tb.zero(), tb.add(e2.getTerm(), minusOne));
        assert e3 != null;
        final Term insert = tb.seqSingleton(e3.getTerm());
        final Term post = tb.seqSub(e1.getTerm(), tb.add(e2.getTerm(), tb.one()),
            tb.add(tb.seqLen(e1.getTerm()), minusOne));
        final Term put = tb.seqConcat(ante, tb.seqConcat(insert, post));
        return new SLExpression(put);
    }

    @Override
    public Object visitSequenceFuncs(JmlParser.SequenceFuncsContext ctx) {
        SLExpression e1 = accept(ctx.expression(0));
        SLExpression e2 = accept(ctx.expression(1));

        assert e1 != null;
        assert e2 != null;

        final Term t2 = e2.getTerm();
        final Term t1 = e1.getTerm();
        switch (ctx.op.getType()) {
        case JmlLexer.SEQCONCAT:
            return termFactory.seqConcat(t1, t2);
        case JmlLexer.SEQGET:
            return termFactory.seqGet(t1, t2);
        case JmlLexer.INDEXOF:
            return termFactory.createIndexOf(t1, t2);
        default:
            raiseError(ctx, "Unexpected syntax case.");
        }
        raiseError(ctx, "Unknown operator: %s", ctx.op);
        return null;
    }

    @Override
    public Object visitInfinite_union_expr(JmlParser.Infinite_union_exprContext ctx) {
        return createInfiniteUnion(ctx.boundvarmodifiers(), ctx.quantifiedvardecls(),
            ctx.predicate(0), ctx.storeref());
    }

    @Override
    public SLExpression visitSpecquantifiedexpression(
            JmlParser.SpecquantifiedexpressionContext ctx) {
        boolean nullable = Boolean.TRUE == accept(ctx.boundvarmodifiers());
        Pair<KeYJavaType, ImmutableList<LogicVariable>> declVars = accept(ctx.quantifiedvardecls());
        resolverManager.pushLocalVariablesNamespace();
        assert declVars != null;
        resolverManager.putIntoTopLocalVariablesNamespace(declVars.second, declVars.first);

        Term guard = tb.tt();
        if (ctx.expression().size() == 2) {
            SLExpression a = accept(ctx.expression(0));
            assert a != null;
            guard = a.getTerm();
        }
        SLExpression expr =
            ctx.expression().size() == 2 ? accept(ctx.expression(1)) : accept(ctx.expression(0));

        resolverManager.popLocalVariablesNamespace();
        assert guard != null;
        guard = tb.convertToFormula(guard);
        assert expr != null;
        final Term body = expr.getTerm();
        switch (ctx.quantifier().start.getType()) {
        case JmlLexer.FORALL:
            return termFactory.forall(guard, body, declVars.first, declVars.second, nullable,
                expr.getType());
        case JmlLexer.EXISTS:
            return termFactory.exists(guard, body, declVars.first, declVars.second, nullable,
                expr.getType());
        case JmlLexer.MAX:
            return termFactory.quantifiedMax(guard, body, declVars.first, nullable,
                declVars.second);
        case JmlLexer.MIN:
            return termFactory.quantifiedMin(guard, body, declVars.first, nullable,
                declVars.second);
        case JmlLexer.NUM_OF:
            KeYJavaType kjtInt =
                services.getTypeConverter().getKeYJavaType(PrimitiveType.JAVA_BIGINT);
            return termFactory.quantifiedNumOf(guard, body, declVars.first, nullable,
                declVars.second, kjtInt);
        case JmlLexer.SUM:
            return termFactory.quantifiedSum(declVars.first, nullable, declVars.second, guard, body,
                expr.getType());
        case JmlLexer.PRODUCT:
            return termFactory.quantifiedProduct(declVars.first, nullable, declVars.second, guard,
                body, expr.getType());
        default:
            raiseError(ctx, "Unexpected syntax case.");
        }
        raiseError(ctx, "Unexpected syntax case.");
        return null;
    }

    @Override
    public SLExpression visitOldexpression(JmlParser.OldexpressionContext ctx) {
        KeYJavaType typ;
        SLExpression result = accept(ctx.expression());
        @Nullable
        String id = accept(ctx.IDENT());

        if (atPres == null || atPres.get(getBaseHeap()) == null) {
            raiseError("JML construct " + "\\old not allowed in this context.", ctx);
        }

        if (id != null) {
            exc.addIgnoreWarning("\\old with label ", ctx.IDENT().getSymbol());
        }

        assert result != null;
        typ = result.getType();
        if (typ != null) {
            result = new SLExpression(convertToOld(result.getTerm()), result.getType());
        } else {
            result = new SLExpression(convertToOld(result.getTerm()));
        }
        return result;
    }

    private Object visitExpressionInSpecMathMode(JmlParser.ExpressionContext ctx,
            SpecMathMode mode) {
        var old = this.termFactory.replaceSpecMathMode(mode);
        var result = accept(ctx);
        var replaced = this.termFactory.replaceSpecMathMode(old);
        assert replaced == mode;
        return result;
    }

    @Override
    public Object visitJava_math_expression(JmlParser.Java_math_expressionContext ctx) {
        return visitExpressionInSpecMathMode(ctx.expression(), SpecMathMode.JAVA);
    }

    @Override
    public Object visitSafe_math_expression(JmlParser.Safe_math_expressionContext ctx) {
        return visitExpressionInSpecMathMode(ctx.expression(), SpecMathMode.SAFE);
    }

    @Override
    public Object visitBigint_math_expression(JmlParser.Bigint_math_expressionContext ctx) {
        return visitExpressionInSpecMathMode(ctx.expression(), SpecMathMode.BIGINT);
    }

    @Override
    public SLExpression visitBeforeexpression(JmlParser.BeforeexpressionContext ctx) {
        KeYJavaType typ;
        SLExpression result = accept(ctx.expression());
        if (atBefores == null || atBefores.get(getBaseHeap()) == null) {
            raiseError("JML construct " + "\\before not allowed in this context.", ctx);
        }

        assert result != null;
        typ = result.getType();
        if (typ != null) {
            result = new SLExpression(convertToBefore(result.getTerm()), result.getType());
        } else {
            result = new SLExpression(convertToBefore(result.getTerm()));
        }
        return result;
    }

    @Override
    public SLExpression visitBsumterm(JmlParser.BsumtermContext ctx) {
        @Nullable
        Pair<KeYJavaType, ImmutableList<LogicVariable>> decls = accept(ctx.quantifiedvardecls());
        resolverManager.pushLocalVariablesNamespace();
        assert decls != null;
        resolverManager.putIntoTopLocalVariablesNamespace(decls.second, decls.first);
        SLExpression a = accept(ctx.expression(0));
        SLExpression b = accept(ctx.expression(1));
        SLExpression t = accept(ctx.expression(2));
        assert t != null;
        SLExpression result = termFactory.bsum(a, b, t, decls.first, decls.second);
        resolverManager.popLocalVariablesNamespace();
        return result;
    }

    @Override
    public Object visitSeqdefterm(JmlParser.SeqdeftermContext ctx) {
        @Nullable
        Pair<KeYJavaType, ImmutableList<LogicVariable>> decls = accept(ctx.quantifiedvardecls());
        resolverManager.pushLocalVariablesNamespace();
        assert decls != null;
        resolverManager.putIntoTopLocalVariablesNamespace(decls.second, decls.first);
        SLExpression a = accept(ctx.expression(0));
        SLExpression b = accept(ctx.expression(1));
        SLExpression t = accept(ctx.expression(2));
        SLExpression result = termFactory.createSeqDef(a, b, t, decls.first, decls.second);
        resolverManager.popLocalVariablesNamespace();
        return result;
    }

    @Override
    public Pair<KeYJavaType, ImmutableList<LogicVariable>> visitQuantifiedvardecls(
            JmlParser.QuantifiedvardeclsContext ctx) {
        ImmutableList<LogicVariable> vars = ImmutableSLList.nil();
        KeYJavaType t = accept(ctx.typespec());
        for (JmlParser.QuantifiedvariabledeclaratorContext context : ctx
                .quantifiedvariabledeclarator()) {
            LogicVariable v = visitQuantifiedvariabledeclarator(context, t);
            vars = vars.append(v);
        }
        return new Pair<>(t, vars);
    }

    @Override
    public Boolean visitBoundvarmodifiers(JmlParser.BoundvarmodifiersContext ctx) {
        return ctx.NULLABLE() != null;
    }

    @Override
    public KeYJavaType visitTypespec(JmlParser.TypespecContext ctx) {
        KeYJavaType t = accept(ctx.type());
        assert t != null;
        String fullName = t.getFullName() + (ctx.dims() != null ? ctx.dims().getText() : "");
        t = javaInfo.getKeYJavaType(fullName);
        if (t == null && ctx.dims() != null) {
            // try to create missing array type
            try {
                javaInfo.readJavaBlock("{" + fullName + " k;}");
                t = javaInfo.getKeYJavaType(fullName);
            } catch (Exception e) {
                t = null;
            }
        }
        return t;
    }

    @Override
    public Object visitDims(JmlParser.DimsContext ctx) {
        return ctx.LBRACKET().size();
    }

    @Override
    public KeYJavaType visitType(JmlParser.TypeContext ctx) {
        if (ctx.TYPE() != null) {
            raiseError("Only the function \\TYPE is supported", ctx);
        }
        return oneOf(ctx.builtintype(), ctx.referencetype());
    }

    @Override
    public KeYJavaType visitReferencetype(JmlParser.ReferencetypeContext ctx) {
        String typename = accept(ctx.name());
        try {
            return resolverManager.resolve(null, typename, null).getType();
        } catch (NullPointerException e) {
            raiseError("Type " + typename + " not found.", ctx);
        } catch (SLTranslationException e) {
            raiseError(ctx, e);
        }
        return null;
    }

    @Override
    public String visitName(JmlParser.NameContext ctx) {
        return ctx.getText();
    }

    @Override
    public Object visitQuantifiedvariabledeclarator(
            JmlParser.QuantifiedvariabledeclaratorContext ctx) {
        raiseError(ctx, "call the other method");
        return null;
    }

    public LogicVariable visitQuantifiedvariabledeclarator(
            JmlParser.QuantifiedvariabledeclaratorContext ctx, KeYJavaType t) {
        KeYJavaType varType;
        final Integer d = accept(ctx.dims());
        int dim = d == null ? 0 : d;
        String id = ctx.IDENT().toString();
        if (dim > 0) {
            StringBuilder fullName = new StringBuilder();
            if (t.getJavaType() instanceof ArrayType) {
                fullName.append(((ArrayType) t.getJavaType()).getAlternativeNameRepresentation());
            } else {
                fullName.append(t.getFullName());
            }
            for (int i = 0; i < dim; i++) {
                fullName.append("[]");
            }
            varType = javaInfo.getKeYJavaType(fullName.toString());
        } else {
            varType = t;
        }
        return new LogicVariable(new Name(id), varType.getSort());
    }
    // endregion

    // region contract
    private ImmutableList<String> mods;
    private ContractClauses contractClauses = new ContractClauses();

    @Override
    public Object visitAccessible_clause(JmlParser.Accessible_clauseContext ctx) {
        if (ctx.COLON() != null || ctx.MEASURED_BY() != null) {// depends clause
            // depends clause
            SLExpression lhs = accept(ctx.lhs);
            Term rhs = accept(ctx.rhs);
            SLExpression mby = accept(ctx.mby);
            assert lhs != null;
            assert rhs != null;
            try {
                return termFactory.depends(lhs, rhs, mby);
            } catch (Exception e) {
                // weigl: seems strange maybe someone missed switched the values
                return termFactory.depends(new SLExpression(rhs), lhs.getTerm(), mby);
            }
        }
        final Term term = requireNonNull(accept(ctx.storeRefUnion()));
        Term t = termFactory.accessible(term);
        LocationVariable[] heaps = visitTargetHeap(ctx.targetHeap());
        for (LocationVariable heap : heaps) {
            contractClauses.add(ContractClauses.ACCESSIBLE, heap, t);
        }
        return new SLExpression(t);
    }

    @Override
    public SLExpression visitAssignable_clause(JmlParser.Assignable_clauseContext ctx) {
        Term t;
        LocationVariable[] heaps = visitTargetHeap(ctx.targetHeap());
        if (ctx.STRICTLY_NOTHING() != null) {
            t = tb.strictlyNothing();
        } else {
            final Term storeRef = accept(ctx.storeRefUnion());
            assert storeRef != null;
            t = termFactory.assignable(storeRef);
        }
        for (LocationVariable heap : heaps) {
            contractClauses.add(ContractClauses.ASSIGNABLE, heap, t);
        }
        return new SLExpression(t);
    }


    @Override
    public SLExpression visitSignals_only_clause(JmlParser.Signals_only_clauseContext ctx) {
        ImmutableList<KeYJavaType> typeList = ImmutableSLList.nil();
        for (JmlParser.ReferencetypeContext context : ctx.referencetype()) {
            typeList = typeList.append((KeYJavaType) accept(context));
        }
        Term t = termFactory.signalsOnly(typeList, this.excVar);
        contractClauses.signalsOnly = t;
        return new SLExpression(t);
    }


    @Override
    public Pair<Label, Term> visitBreaks_clause(JmlParser.Breaks_clauseContext ctx) {
        String label = ctx.lbl == null ? "" : ctx.lbl.getText();
        SLExpression pred = accept(ctx.predornot());
        assert pred != null;
        @Nonnull
        Pair<Label, Term> t = termFactory.createBreaks(pred.getTerm(), label);
        contractClauses.add(ContractClauses.BREAKS, t.first, t.second);
        return t;
    }

    @Override
    public Pair<Label, Term> visitContinues_clause(JmlParser.Continues_clauseContext ctx) {
        String label = ctx.lbl == null ? "" : ctx.lbl.getText();
        SLExpression pred = accept(ctx.predornot());
        assert pred != null;
        @Nonnull
        Pair<Label, Term> t = termFactory.createContinues(pred.getTerm(), label);
        contractClauses.add(ContractClauses.CONTINUES, t.first, t.second);
        return t;
    }

    @Override
    public SLExpression visitReturns_clause(JmlParser.Returns_clauseContext ctx) {
        @Nullable
        SLExpression pred = accept(ctx.predornot());
        assert pred != null;
        contractClauses.returns = termFactory.createReturns(pred.getTerm());
        return pred;
    }

    @Override
    public ImmutableList<String> visitModifiers(JmlParser.ModifiersContext ctx) {
        mods = ImmutableSLList.nil();
        return mods;
    }

    @Override
    public String visitModifier(JmlParser.ModifierContext ctx) {
        mods = mods.append(ctx.getText());
        return ctx.getText();
    }

    @Override
    public SLExpression visitClass_invariant(JmlParser.Class_invariantContext ctx) {
        return accept(ctx.expression());
    }

    @Override
    public ClassAxiom visitClass_axiom(JmlParser.Class_axiomContext ctx) {
        raiseError(ctx, "Class axioms are not handled by the %s", getClass().getName());
        return null;
    }

    @Override
    public Object visitInitially_clause(JmlParser.Initially_clauseContext ctx) {
        raiseError(ctx, "Initially clauses are not handled by the %s", getClass().getName());
        return null;
    }

    @Override
    public Object visitMethod_specification(JmlParser.Method_specificationContext ctx) {
        return listOf(ctx.spec_case());
    }


    @Override
    public de.uka.ilkd.key.speclang.Contract visitSpec_case(JmlParser.Spec_caseContext ctx) {
        this.mods = accept(ctx.modifiers());
        contractClauses = new ContractClauses();
        accept(ctx.spec_body());
        return null;
    }

    @Override
    public Object visitSpec_body(JmlParser.Spec_bodyContext ctx) {
        listOf(ctx.clause());
        listOf(ctx.spec_body());
        return null;
    }


    enum ClauseSubType {
        NONE, FREE, REDUNDANT
    }

    private ClauseSubType subType(String type) {
        if (type.endsWith("_free")) {
            return ClauseSubType.FREE;
        }
        if (type.endsWith("_redundantly")) {
            return ClauseSubType.FREE;
        }
        return ClauseSubType.NONE;
    }

    private void insertSimpleClause(String type, LocationVariable heap, Term t,
            ContractClauses.Clauses<LocationVariable, Term> none,
            ContractClauses.Clauses<LocationVariable, Term> free,
            ContractClauses.Clauses<LocationVariable, Term> redundantly) {
        switch (subType(type)) {
        case FREE:
            contractClauses.add(free, heap, t);
            break;
        case REDUNDANT:
            contractClauses.add(redundantly, heap, t);
            break;
        default:
            contractClauses.add(none, heap, t);
        }
    }

    @Override
    public Object visitEnsures_clause(JmlParser.Ensures_clauseContext ctx) {
        String type = ctx.ENSURES().getText();
        SLExpression t = accept(ctx.predornot());
        LocationVariable[] heaps = visitTargetHeap(ctx.targetHeap());
        for (LocationVariable heap : heaps) {
            assert t != null;
            insertSimpleClause(type, heap, t.getTerm(), ContractClauses.ENSURES,
                ContractClauses.ENSURES_FREE, ContractClauses.ENSURES);
        }
        return t;
    }


    @Override
    public Object visitRequires_clause(JmlParser.Requires_clauseContext ctx) {
        String type = ctx.REQUIRES().getText();
        SLExpression t = accept(ctx.predornot());
        LocationVariable[] heaps = visitTargetHeap(ctx.targetHeap());
        for (LocationVariable heap : heaps) {
            assert t != null;
            insertSimpleClause(type, heap, t.getTerm(), ContractClauses.REQUIRES,
                ContractClauses.REQUIRES_FREE, ContractClauses.REQUIRES);
        }
        return t;
    }

    @Override
    public Object visitMeasured_by_clause(JmlParser.Measured_by_clauseContext ctx) {
        final List<SLExpression> seq = ctx.predornot().stream().map(it -> (SLExpression) accept(it))
                .collect(Collectors.toList());
        Optional<SLExpression> t =
            seq.stream().reduce((a, b) -> new SLExpression(tb.pair(a.getTerm(), b.getTerm())));
        Term result = t.orElse(seq.get(0)).getTerm();
        contractClauses.measuredBy = result;
        return new SLExpression(result);
    }


    @Override
    public Object visitCaptures_clause(JmlParser.Captures_clauseContext ctx) {
        return this.<SLExpression>accept(ctx.predornot());
    }

    @Override
    public Object visitDiverges_clause(JmlParser.Diverges_clauseContext ctx) {
        SLExpression t = accept(ctx.predornot());
        assert t != null;
        contractClauses.diverges = t.getTerm();
        return t;
    }

    @Override
    public Object visitWorking_space_clause(JmlParser.Working_space_clauseContext ctx) {
        addWarning(ctx, "Working space clause is not supported. Ignored!");
        return this.<SLExpression>accept(ctx.predornot());
    }

    @Override
    public Object visitDuration_clause(JmlParser.Duration_clauseContext ctx) {
        addWarning(ctx, "Duration clause is not supported. Ignored!");
        return null;
    }

    @Override
    public Object visitWhen_clause(JmlParser.When_clauseContext ctx) {
        addWarning(ctx, "When clause is not supported. Ignored!");
        return null;
    }


    @Override
    public Pair<IObserverFunction, Term> visitRepresents_clause(
            JmlParser.Represents_clauseContext ctx) {
        SLExpression lhs = accept(ctx.lhs);
        SLExpression rhs = accept(ctx.rhs);
        Term storeRef = accept(ctx.t);

        assert lhs != null;
        boolean representsClauseLhsIsLocSet = lhs.getTerm().sort().equals(locSetLDT.targetSort());
        if (!lhs.isTerm() || !(lhs.getTerm().op() instanceof ObserverFunction)
                || lhs.getTerm().sub(0).op() != heapLDT.getHeap()) {
            raiseError("Represents clause with unexpected lhs: " + lhs, ctx);
        } else if (selfVar != null && ((ObserverFunction) lhs.getTerm().op()).isStatic()) {
            raiseError("Represents clauses for static model fields must be static.", ctx);
        }

        Term t;
        if (ctx.SUCH_THAT() != null) {
            final SLExpression expr = accept(ctx.predicate());
            assert expr != null;
            t = expr.getTerm();
        } else if (!representsClauseLhsIsLocSet) {
            assert rhs != null;
            if (!rhs.isTerm()) {
                raiseError("Represents clause with unexpected rhs: " + rhs, ctx);
            }
            Term rhsTerm = rhs.getTerm();
            if (rhsTerm.sort() == Sort.FORMULA) {
                rhsTerm = tb.ife(rhsTerm, tb.TRUE(), tb.FALSE());
            }
            t = tb.equals(lhs.getTerm(), rhsTerm);
        } else {
            t = rhs != null ? rhs.getTerm() : storeRef;
            assert t != null;
            t = tb.equals(lhs.getTerm(), t);
        }
        return termFactory.represents(lhs, t);
    }

    // region inf flow

    @Override
    public InfFlowSpec visitSeparates_clause(JmlParser.Separates_clauseContext ctx) {
        ImmutableList<Term> decl = ImmutableSLList.nil();
        ImmutableList<Term> erases = ImmutableSLList.nil();
        ImmutableList<Term> newObs = ImmutableSLList.nil();

        ImmutableList<Term> sep = accept(ctx.sep);

        decl = append(decl, ctx.decl);
        erases = append(erases, ctx.erase);
        newObs = append(newObs, ctx.newobj);
        assert sep != null;
        decl = sep.append(decl);
        erases = sep.append(erases);
        return new InfFlowSpec(decl, erases, newObs);
    }

    @Override
    public Object visitLoop_separates_clause(JmlParser.Loop_separates_clauseContext ctx) {
        ImmutableList<Term> sep = accept(ctx.sep);
        ImmutableList<Term> newObs = ImmutableSLList.nil();
        newObs = append(newObs, ctx.newobj);
        return new InfFlowSpec(sep, sep, newObs);
    }

    @Override
    public Object visitDetermines_clause(JmlParser.Determines_clauseContext ctx) {
        ImmutableList<Term> decl = ImmutableSLList.nil();
        ImmutableList<Term> erases = ImmutableSLList.nil();
        ImmutableList<Term> newObs = ImmutableSLList.nil();
        ImmutableList<Term> by = ImmutableSLList.nil();

        ImmutableList<Term> determined = accept(ctx.determined);

        if (ctx.byItself != null) {
            by = determined;
        } else {
            @Nullable
            ImmutableList<Term> t = accept(ctx.by);
            assert t != null;
            by = by.append(t);
        }

        decl = append(decl, ctx.decl);
        erases = append(erases, ctx.erases);
        newObs = append(newObs, ctx.newObs);

        assert determined != null;
        determined = determined.append(erases);
        by = by.append(decl);

        return new InfFlowSpec(by, determined, newObs);
    }

    @Override
    public Object visitLoop_determines_clause(JmlParser.Loop_determines_clauseContext ctx) {
        ImmutableList<Term> newObs = ImmutableSLList.nil();
        ImmutableList<Term> det = append(ImmutableSLList.nil(), ctx.det);
        newObs = append(newObs, ctx.newObs);
        return new InfFlowSpec(det, det, newObs);
    }

    @Override
    public ImmutableList<Term> visitInfflowspeclist(JmlParser.InfflowspeclistContext ctx) {
        if (ctx.NOTHING() != null) {
            return ImmutableSLList.nil();
        }
        ImmutableList<SLExpression> seq = accept(ctx.expressionlist());
        assert seq != null;
        ImmutableList<Term> result = ImmutableList
                .fromList(seq.stream().map(SLExpression::getTerm).collect(Collectors.toList()));
        return termFactory.infflowspeclist(result);
    }
    // endregion

    @Override
    public Object visitSignals_clause(JmlParser.Signals_clauseContext ctx) {
        LogicVariable eVar = null;
        KeYJavaType excType = accept(ctx.referencetype());
        String vName = accept(ctx.IDENT());
        if (vName != null) {
            assert excType != null;
            eVar = new LogicVariable(new Name(vName), excType.getSort());
            resolverManager.pushLocalVariablesNamespace();
            resolverManager.putIntoTopLocalVariablesNamespace(eVar, excType);
        }
        SLExpression result = accept(ctx.predornot());
        if (vName != null) {
            resolverManager.popLocalVariablesNamespace();
        }
        assert result != null;
        Term r = termFactory.signals(result.getTerm(), eVar, excVar, excType);
        contractClauses.signalsOnly = r;
        return new SLExpression(r);
    }

    @Override
    public Object visitName_clause(JmlParser.Name_clauseContext ctx) {
        raiseError(ctx, "Name clauses are not handled by the %s", getClass().getName());
        return null;
    }


    @Override
    public Object visitField_declaration(JmlParser.Field_declarationContext ctx) {
        raiseError(ctx, "Field declarations are not handled by the %s", getClass().getName());
        return null;
    }

    @Override
    public SLExpression visitMethod_declaration(JmlParser.Method_declarationContext ctx) {
        if (ctx.method_body() == null) {
            return new SLExpression(tb.tt());
        }

        String paramsString;
        List<JmlParser.Param_declContext> paramDecls = ctx.param_list().param_decl();
        if (!paramDecls.isEmpty()) {
            paramsString =
                "(" + paramDecls.stream().map(it -> it.p.getText()).collect(Collectors.joining(","))
                    + ")";
        } else {
            paramsString = "()"; // default no params
        }

        ParserRuleContext equal = JmlFacade.parseExpr(ctx.IDENT() + paramsString);
        Object a = accept(equal);

        SLExpression body = accept(ctx.method_body().expression());
        SLParameters params = visitParameters(ctx.param_list());
        SLExpression apply = lookupIdentifier(ctx.IDENT().getText(), null, params, ctx);

        return termFactory.eq(apply, body);
    }


    @Override
    public Object visitHistory_constraint(JmlParser.History_constraintContext ctx) {
        raiseError(ctx, "History constraints are not handled by the %s", getClass().getName());
        return null;
    }

    @Override
    public Object visitDatagroup_clause(JmlParser.Datagroup_clauseContext ctx) {
        raiseError(ctx, "Datagroup clause are not handled by the %s", getClass().getName());
        return null;
    }

    @Override
    public Object visitMonitors_for_clause(JmlParser.Monitors_for_clauseContext ctx) {
        raiseError(ctx, "Monitors-For clause are not handled by the %s", getClass().getName());
        return null;
    }

    @Override
    public Object visitReadable_if_clause(JmlParser.Readable_if_clauseContext ctx) {
        raiseError(ctx, "Readable-If clause are not handled by the %s", getClass().getName());
        return null;
    }

    @Override
    public Object visitWritable_if_clause(JmlParser.Writable_if_clauseContext ctx) {
        raiseError(ctx, "Writeable-If clause are not handled by the %s", getClass().getName());
        return null;
    }

    @Override
    public Object visitIn_group_clause(JmlParser.In_group_clauseContext ctx) {
        raiseError(ctx, "In-Group clauses are not handled by the %s", getClass().getName());
        return null;
    }

    @Override
    public Object visitMaps_into_clause(JmlParser.Maps_into_clauseContext ctx) {
        raiseError(ctx, "'maps into' are not handled by the %s", getClass().getName());
        return null;
    }

    @Override
    public Object visitNowarn_pragma(JmlParser.Nowarn_pragmaContext ctx) {
        raiseError(ctx, "Nowarn pragma is not handled by the %s", getClass().getName());
        return null;
    }

    @Override
    public Object visitDebug_statement(JmlParser.Debug_statementContext ctx) {
        raiseError(ctx, "Debug statements are not handled by the %s", getClass().getName());
        return null;
    }

    @Override
    public Object visitSet_statement(JmlParser.Set_statementContext ctx) {
        raiseError(ctx, "Set statements are not handled by the %s", getClass().getName());
        return null;
    }

    @Override
    public Object visitMerge_point_statement(JmlParser.Merge_point_statementContext ctx) {
        raiseError(ctx, "Merge points are not handled by the %s", getClass().getName());
        return null;
    }

    @Override
    public Object visitMergeparamsspec(JmlParser.MergeparamsspecContext ctx) {
        String latticeType = ctx.latticetype.getText();
        KeYJavaType phType = accept(ctx.typespec());
        String phName = ctx.phName.getText();
        LocationVariable placeholder = new LocationVariable(new ProgramElementName(phName), phType);
        resolverManager.putIntoTopLocalVariablesNamespace(placeholder);
        ImmutableList<SLExpression> expr = listOf(ctx.predicate());

        ImmutableList<Term> preds = ImmutableList
                .fromList(expr.stream().map(SLExpression::getTerm).collect(Collectors.toList()));
        return new MergeParamsSpec(latticeType, placeholder, preds);
    }

    @Override
    public Object visitLoop_specification(JmlParser.Loop_specificationContext ctx) {
        raiseError(ctx, "Loop specification are not handled by the %s", getClass().getName());
        return null;
    }

    @Override
    public Object visitLoop_invariant(JmlParser.Loop_invariantContext ctx) {
        return accept(ctx.expression());
    }

    @Override
    public SLExpression visitVariant_function(JmlParser.Variant_functionContext ctx) {
        List<SLExpression> exprs = mapOf(ctx.expression());
        Optional<SLExpression> t =
            exprs.stream().reduce((a, b) -> new SLExpression(tb.pair(a.getTerm(), b.getTerm())));
        return new SLExpression(t.orElse(exprs.get(0)).getTerm());
    }

    @Override
    public Object visitInitialiser(JmlParser.InitialiserContext ctx) {
        raiseError(ctx, "Initialisers are not handled by the %s", getClass().getName());
        return null;
    }

    @Override
    public Object visitBlock_specification(JmlParser.Block_specificationContext ctx) {
        raiseError(ctx, "Block specification are not handled by the %s", getClass().getName());
        return null;
    }

    @Override
    public Object visitBlock_loop_specification(JmlParser.Block_loop_specificationContext ctx) {
        raiseError(ctx, "'block loop' are not handled by the %s", getClass().getName());
        return null;
    }

    @Override
    public Object visitAssert_statement(JmlParser.Assert_statementContext ctx) {
        if (ctx.UNREACHABLE() != null) {
            return new SLExpression(tb.not(tb.tt()));
        }
        return accept(ctx.expression());
    }

    @Override
    public Object visitAssume_statement(JmlParser.Assume_statementContext ctx) {
        return accept(ctx.expression());
    }

    @Override
    public LocationVariable[] visitTargetHeap(JmlParser.TargetHeapContext ctx) {
        if (ctx == null || ctx.SPECIAL_IDENT().isEmpty()) {
            return new LocationVariable[] { getBaseHeap() };
        }

        LocationVariable[] heaps = new LocationVariable[ctx.SPECIAL_IDENT().size()];
        for (int i = 0; i < ctx.SPECIAL_IDENT().size(); i++) {
            String heapName = ctx.SPECIAL_IDENT(i).getText();
            switch (heapName) {
            case "<permission>":
            case "<permissions>":
                heaps[i] = getPermissionHeap();
                break;
            case "<savedHeap>":
            case "<saved>":
                heaps[i] = getSavedHeap();
                break;
            case "<heap>":
                heaps[i] = getBaseHeap();
                break;
            default:
                heaps[i] = heapLDT.getHeapForName(new Name(heapName));
            }
        }
        return heaps;
    }
    // endregion

    // region exception helper
    protected void addWarning(ParserRuleContext node, String description) {
        exc.addWarning(description, node.start);
    }

    public List<PositionedString> getWarnings() {
        return exc.getWarnings();
    }

    public static void raiseError(ParserRuleContext ctx, Exception e) {
        throw new BuildingException(ctx, e);
    }

    public static void raiseError(ParserRuleContext ctx, String message, Object... args) {
        throw new BuildingException(ctx, format(message, args));
    }


    public static void raiseError(String message, ParserRuleContext ctx) {
        throw new BuildingException(ctx, message);
    }

    // endregion
}
