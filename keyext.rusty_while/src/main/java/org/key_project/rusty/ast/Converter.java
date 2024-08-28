/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast;

import java.math.BigInteger;
import java.util.*;

import org.key_project.logic.Name;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.expr.*;
import org.key_project.rusty.ast.fn.Function;
import org.key_project.rusty.ast.fn.FunctionParam;
import org.key_project.rusty.ast.fn.FunctionParamPattern;
import org.key_project.rusty.ast.fn.SelfParam;
import org.key_project.rusty.ast.pat.*;
import org.key_project.rusty.ast.stmt.EmptyStatement;
import org.key_project.rusty.ast.stmt.ExpressionStatement;
import org.key_project.rusty.ast.stmt.LetStatement;
import org.key_project.rusty.ast.stmt.Statement;
import org.key_project.rusty.ast.ty.KeYRustyType;
import org.key_project.rusty.ast.ty.PrimitiveType;
import org.key_project.rusty.ast.ty.Type;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.parsing.RustyWhileParser;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import org.antlr.v4.runtime.tree.TerminalNode;
import org.jspecify.annotations.Nullable;

public class Converter {
    // TODO: Rework this properly
    private final Map<String, VariableDeclaration> variables = new HashMap<>();
    private final Map<VariableDeclaration, ProgramVariable> programVariables = new HashMap<>();

    private final Services services;

    public Converter(Services services) {
        this.services = services;
    }

    public Services getServices() {
        return services;
    }

    private void declareVariable(Pattern pat, LetStatement decl) {
        if (pat instanceof IdentPattern ip) {
            Name name = ip.name();
            variables.put(name.toString(), decl);
            programVariables.put(decl, new ProgramVariable(name,
                new KeYRustyType(decl.getType().getSort(services))));
        }
    }

    private void declareVariable(String name, FunctionParamPattern decl) {
        variables.put(name, decl);
        programVariables.put(decl, services.getNamespaces().programVariables().lookup(name));
    }

    private VariableDeclaration getDecl(PathInExpression path) {
        // TODO: For now, only use local vars, i.e., ignore all but the last segment
        return variables.get(path.segments().last().segment().ident().name().toString());
    }

    private ProgramVariable getProgramVariable(PathInExpression path) {
        return programVariables.get(getDecl(path));
    }

    private Label getLabel(String name) {
        throw new UnsupportedOperationException("TODO @ DD : implement getLabel");
    }

    public Crate convertCrate(org.key_project.rusty.parsing.RustyWhileParser.CrateContext ctx) {
        return new Crate(ctx.item().stream().map(this::convertItem)
                .collect(ImmutableList.collector()));
    }


    private Item convertItem(org.key_project.rusty.parsing.RustyWhileParser.ItemContext ctx) {
        // TODO: Rework
        return convertFunction(ctx.function_());
    }

    public Function convertFunction(
            org.key_project.rusty.parsing.RustyWhileParser.Function_Context ctx) {
        Name name = convertIdentifier(ctx.identifier()).name();
        ImmutableArray<FunctionParam> params =
            convertFunctionParams(ctx.functionParams());
        Type returnType = convertType(ctx.functionRetTy().type_());
        BlockExpression body =
            convertBlockExpr(ctx.blockExpr());
        return new Function(name,
            params,
            returnType,
            body);
    }

    private Expr convertExpr(org.key_project.rusty.parsing.RustyWhileParser.ExprContext ctx) {
        if (ctx instanceof org.key_project.rusty.parsing.RustyWhileParser.LiteralExpressionContext lit)
            return convertLiteralExpr(lit.literalExpr());
        if (ctx instanceof org.key_project.rusty.parsing.RustyWhileParser.PathExpressionContext path)
            return convertPathExpr(path.pathExpr());
        if (ctx instanceof RustyWhileParser.MethodCallExpressionContext x)
            return convertMethodCallExpression(x);
        if (ctx instanceof RustyWhileParser.FieldExpressionContext x)
            return convertFieldExpression(x);
        if (ctx instanceof RustyWhileParser.TupleIndexingExpressionContext x)
            return convertTupleIndexingExpression(x);
        if (ctx instanceof RustyWhileParser.CallExpressionContext x)
            return convertCallExpression(x);
        if (ctx instanceof RustyWhileParser.IndexExpressionContext x)
            return convertIndexExpression(x);
        if (ctx instanceof RustyWhileParser.ErrorPropagationExpressionContext x)
            return convertErrorPropagationExpression(x);
        if (ctx instanceof RustyWhileParser.BorrowExpressionContext x)
            return convertBorrowExpression(x);
        if (ctx instanceof RustyWhileParser.DereferenceExpressionContext x)
            return convertDereferenceExpression(x);
        if (ctx instanceof RustyWhileParser.NegationExpressionContext x)
            return convertNegationExpression(x);
        if (ctx instanceof RustyWhileParser.TypeCastExpressionContext x)
            return convertTypeCastExpression(x);
        if (ctx instanceof org.key_project.rusty.parsing.RustyWhileParser.ArithmeticOrLogicalExpressionContext ale)
            return convertArithmeticOrLogicalExpression(ale);
        if (ctx instanceof RustyWhileParser.ComparisonExpressionContext x)
            return convertComparisonExpression(x);
        if (ctx instanceof RustyWhileParser.LazyBooleanExpressionContext x)
            return convertLazyBooleanExpression(x);
        if (ctx instanceof RustyWhileParser.RangeExpressionContext x)
            return convertRangeExpression(x);
        if (ctx instanceof org.key_project.rusty.parsing.RustyWhileParser.AssignmentExpressionContext ae)
            return convertAssignmentExpression(ae);
        if (ctx instanceof RustyWhileParser.CompoundAssignmentExpressionContext x)
            return convertCompoundAssignmentExpression(x);
        if (ctx instanceof RustyWhileParser.ContinueExpressionContext x)
            return convertContinueExpression(x);
        if (ctx instanceof RustyWhileParser.BreakExpressionContext x)
            return convertBreakExpression(x);
        if (ctx instanceof RustyWhileParser.ReturnExpressionContext x)
            return convertReturnExpression(x);
        if (ctx instanceof RustyWhileParser.GroupedExpressionContext x)
            return convertGroupedExpression(x);
        if (ctx instanceof RustyWhileParser.ArrayExpressionContext x)
            if (x.arrayElements() == null || x.arrayElements().SEMI() == null)
                return convertEnumeratedArrayExpression(x);
            else
                return convertRepeatedArrayExpression(x);
        if (ctx instanceof RustyWhileParser.TupleExpressionContext x)
            return convertTupleExpression(x);
        if (ctx instanceof RustyWhileParser.StructExpression_Context x) {
            if (x.structExpr().structExprUnit() != null)
                return convertUnitStructExpression(x.structExpr().structExprUnit());
            if (x.structExpr().structExprTuple() != null)
                return convertTupleStructExpression(x.structExpr().structExprTuple());
            if (x.structExpr().structExprStruct() != null)
                return convertStructStructExpression(x.structExpr().structExprStruct());
        }
        if (ctx instanceof RustyWhileParser.EnumerationVariantExpression_Context x) {
            if (x.enumerationVariantExpr().enumExprStruct() != null)
                return convertEnumVariantStruct(x.enumerationVariantExpr().enumExprStruct());
            if (x.enumerationVariantExpr().enumExprTuple() != null)
                return convertEnumVariantTuple(x.enumerationVariantExpr().enumExprTuple());
            if (x.enumerationVariantExpr().enumExprFieldless() != null)
                return convertEnumVariantFieldless(x.enumerationVariantExpr().enumExprFieldless());
        }
        if (ctx instanceof RustyWhileParser.ClosureExpression_Context x)
            return convertClosureExpression(x.closureExpr());
        if (ctx instanceof RustyWhileParser.ExpressionWithBlock_Context x)
            return convertExprWithBlock(x.exprWithBlock());
        throw new UnsupportedOperationException(
            "Unknown expr: " + ctx.getText() + " class: " + ctx.getClass());
    }

    private Expr convertLiteralExpr(
            org.key_project.rusty.parsing.RustyWhileParser.LiteralExprContext ctx) {
        if (ctx.KW_TRUE() != null)
            return new BooleanLiteralExpression(true);
        if (ctx.KW_FALSE() != null)
            return new BooleanLiteralExpression(false);
        var intLit = ctx.INTEGER_LITERAL();
        if (intLit != null) {
            var text = intLit.getText();
            var signed = text.contains("i");
            var split = text.split("[ui]");
            var size = split[split.length - 1];
            var suffix = IntegerLiteralExpression.IntegerSuffix.get(signed, size);
            var lit = split[0];

            var value = new BigInteger(
                lit);
            return new IntegerLiteralExpression(value, suffix);
        }

        throw new IllegalArgumentException("Expected boolean or integer literal");
    }

    private ProgramVariable convertPathExpr(
            org.key_project.rusty.parsing.RustyWhileParser.PathExprContext ctx) {
        if (ctx.qualifiedPathInExpr() != null)
            throw new IllegalArgumentException("TODO @ DD: Qual path");
        else {
            var pieCtx = ctx.pathInExpr();
            var segments =
                pieCtx.pathExprSegment().stream().map(this::convertPathExprSegment).toList();
            var pie = new PathInExpression(new ImmutableArray<>(segments));
            return Objects.requireNonNull(getProgramVariable(pie));
        }
    }

    private MethodCallExpression convertMethodCallExpression(
            RustyWhileParser.MethodCallExpressionContext ctx) {
        var callee = convertExpr(ctx.expr());
        var seg = convertPathExprSegment(ctx.pathExprSegment());
        ImmutableArray<Expr> params = ctx.callParams() == null ? new ImmutableArray<>()
                : new ImmutableArray<>(
                    ctx.callParams().expr().stream().map(this::convertExpr).toList());
        return new MethodCallExpression(callee, seg, params);
    }

    private FieldExpression convertFieldExpression(RustyWhileParser.FieldExpressionContext ctx) {
        var base = convertExpr(ctx.expr());
        var ident = convertIdentifier(ctx.identifier());
        return new FieldExpression(base, ident);
    }

    private TupleIndexingExpression convertTupleIndexingExpression(
            RustyWhileParser.TupleIndexingExpressionContext ctx) {
        var base = convertExpr(ctx.expr());
        int idx = Integer.parseInt(ctx.tupleIndex().INTEGER_LITERAL().getText());
        return new TupleIndexingExpression(base, idx);
    }

    private CallExpression convertCallExpression(RustyWhileParser.CallExpressionContext ctx) {
        var callee = convertExpr(ctx.expr());
        ImmutableArray<Expr> params = ctx.callParams() == null ? new ImmutableArray<>()
                : new ImmutableArray<>(
                    ctx.callParams().expr().stream().map(this::convertExpr).toList());
        return new CallExpression(callee, params);
    }

    private IndexExpression convertIndexExpression(RustyWhileParser.IndexExpressionContext ctx) {
        var base = convertExpr(ctx.expr(0));
        var idx = convertExpr(ctx.expr(1));
        return new IndexExpression(base, idx);
    }

    private ErrorPropagationExpression convertErrorPropagationExpression(
            RustyWhileParser.ErrorPropagationExpressionContext ctx) {
        var base = convertExpr(ctx.expr());
        return new ErrorPropagationExpression(base);
    }

    private BorrowExpression convertBorrowExpression(RustyWhileParser.BorrowExpressionContext ctx) {
        var base = convertExpr(ctx.expr());
        return new BorrowExpression(ctx.ANDAND() != null, ctx.KW_MUT() != null, base);
    }

    private DereferenceExpression convertDereferenceExpression(
            RustyWhileParser.DereferenceExpressionContext ctx) {
        var base = convertExpr(ctx.expr());
        return new DereferenceExpression(base);
    }

    private NegationExpression convertNegationExpression(
            RustyWhileParser.NegationExpressionContext ctx) {
        var base = convertExpr(ctx.expr());
        var op =
            ctx.NOT() != null ? NegationExpression.Operator.Not : NegationExpression.Operator.Neg;
        return new NegationExpression(base, op);
    }

    private TypeCastExpression convertTypeCastExpression(
            RustyWhileParser.TypeCastExpressionContext ctx) {
        var base = convertExpr(ctx.expr());
        var ty = convertTypeNoBounds(ctx.typeNoBounds());
        return new TypeCastExpression(base, ty);
    }

    private Expr convertArithmeticOrLogicalExpression(
            org.key_project.rusty.parsing.RustyWhileParser.ArithmeticOrLogicalExpressionContext ctx) {
        ArithLogicalExpression.Operator op = null;
        if (ctx.AND() != null)
            op = ArithLogicalExpression.Operator.BitwiseAnd;
        if (ctx.OR() != null)
            op = ArithLogicalExpression.Operator.BitwiseOr;
        if (ctx.CARET() != null)
            op = ArithLogicalExpression.Operator.BitwiseXor;
        if (ctx.PLUS() != null)
            op = ArithLogicalExpression.Operator.Plus;
        if (ctx.MINUS() != null)
            op = ArithLogicalExpression.Operator.Minus;
        if (ctx.PERCENT() != null)
            op = ArithLogicalExpression.Operator.Modulo;
        if (ctx.STAR() != null)
            op = ArithLogicalExpression.Operator.Multiply;
        if (ctx.SLASH() != null)
            op = ArithLogicalExpression.Operator.Divide;
        assert op != null;
        return new ArithLogicalExpression(convertExpr(ctx.expr(0)), op,
            convertExpr(ctx.expr(1)));
    }

    private ComparisonExpression convertComparisonExpression(
            RustyWhileParser.ComparisonExpressionContext ctx) {
        var left = convertExpr(ctx.expr(0));
        var right = convertExpr(ctx.expr(1));
        var opCtx = ctx.comparisonOperator();
        var op = opCtx.EQEQ() != null ? ComparisonExpression.Operator.Equal
                : opCtx.GT() != null ? ComparisonExpression.Operator.Greater
                        : opCtx.LT() != null ? ComparisonExpression.Operator.Less
                                : opCtx.NE() != null ? ComparisonExpression.Operator.NotEqual
                                        : opCtx.GE() != null
                                                ? ComparisonExpression.Operator.GreaterOrEqual
                                                : opCtx.LE() != null
                                                        ? ComparisonExpression.Operator.LessOrEqual
                                                        : null;
        assert op != null;
        return new ComparisonExpression(left, op, right);
    }

    private LazyBooleanExpression convertLazyBooleanExpression(
            RustyWhileParser.LazyBooleanExpressionContext ctx) {
        var left = convertExpr(ctx.expr(0));
        var right = convertExpr(ctx.expr(1));
        var op = ctx.ANDAND() != null ? LazyBooleanExpression.Operator.And
                : LazyBooleanExpression.Operator.Or;
        return new LazyBooleanExpression(left, op, right);
    }

    private RangeExpression convertRangeExpression(RustyWhileParser.RangeExpressionContext ctx) {
        var left =
            ctx.getChild(0) instanceof RustyWhileParser.ExprContext e ? convertExpr(e) : null;
        var right = left == null ? convertExpr(ctx.expr(0)) : convertExpr(ctx.expr(1));
        var inclusive = ctx.DOTDOTEQ() != null;
        return new RangeExpression(left, right, inclusive);
    }

    private AssignmentExpression convertAssignmentExpression(
            org.key_project.rusty.parsing.RustyWhileParser.AssignmentExpressionContext ctx) {
        var lhs = convertExpr(ctx.expr(0));
        var rhs = convertExpr(ctx.expr(1));
        return new AssignmentExpression(lhs, rhs);
    }

    private CompoundAssignmentExpression convertCompoundAssignmentExpression(
            RustyWhileParser.CompoundAssignmentExpressionContext ctx) {
        var left = convertExpr(ctx.expr(0));
        var right = convertExpr(ctx.expr(1));
        var opCtx = ctx.compoundAssignOperator();
        var op = opCtx.PLUSEQ() != null ? CompoundAssignmentExpression.Operator.Plus
                : opCtx.MINUSEQ() != null ? CompoundAssignmentExpression.Operator.Minus
                        : opCtx.STAREQ() != null ? CompoundAssignmentExpression.Operator.Divide
                                : opCtx.PERCENTEQ() != null
                                        ? CompoundAssignmentExpression.Operator.Modulo
                                        : opCtx.ANDEQ() != null
                                                ? CompoundAssignmentExpression.Operator.And
                                                : opCtx.OREQ() != null
                                                        ? CompoundAssignmentExpression.Operator.Or
                                                        : opCtx.CARETEQ() != null
                                                                ? CompoundAssignmentExpression.Operator.Xor
                                                                : opCtx.SHLEQ() != null
                                                                        ? CompoundAssignmentExpression.Operator.Shl
                                                                        : CompoundAssignmentExpression.Operator.Shr;
        return new CompoundAssignmentExpression(left, op, right);
    }

    private ContinueExpression convertContinueExpression(
            RustyWhileParser.ContinueExpressionContext ctx) {
        var label = ctx.LIFETIME_OR_LABEL() != null ? convertLabel(ctx.LIFETIME_OR_LABEL()) : null;
        var expr = ctx.expr() != null ? convertExpr(ctx.expr()) : null;
        return new ContinueExpression(label, expr);
    }

    private BreakExpression convertBreakExpression(RustyWhileParser.BreakExpressionContext ctx) {
        var label = ctx.LIFETIME_OR_LABEL() != null ? convertLabel(ctx.LIFETIME_OR_LABEL()) : null;
        var expr = ctx.expr() != null ? convertExpr(ctx.expr()) : null;
        return new BreakExpression(label, expr);
    }

    private ReturnExpression convertReturnExpression(RustyWhileParser.ReturnExpressionContext ctx) {
        var expr = ctx.expr() != null ? convertExpr(ctx.expr()) : null;
        return new ReturnExpression(expr);
    }

    private GroupedExpression convertGroupedExpression(
            RustyWhileParser.GroupedExpressionContext ctx) {
        return new GroupedExpression(convertExpr(ctx.expr()));
    }

    private EnumeratedArrayExpression convertEnumeratedArrayExpression(
            RustyWhileParser.ArrayExpressionContext ctx) {
        if (ctx.arrayElements() == null)
            return new EnumeratedArrayExpression(new ImmutableArray<>());
        assert ctx.arrayElements().SEMI() == null;
        return new EnumeratedArrayExpression(new ImmutableArray<>(
            ctx.arrayElements().expr().stream().map(this::convertExpr).toList()));
    }

    private RepeatedArrayExpression convertRepeatedArrayExpression(
            RustyWhileParser.ArrayExpressionContext ctx) {
        return new RepeatedArrayExpression(convertExpr(ctx.arrayElements().expr(0)),
            convertExpr(ctx.arrayElements().expr(1)));
    }

    private TupleExpression convertTupleExpression(RustyWhileParser.TupleExpressionContext ctx) {
        if (ctx.tupleElements() == null)
            return TupleExpression.UNIT;
        return new TupleExpression(new ImmutableArray<>(
            ctx.tupleElements().expr().stream().map(this::convertExpr).toList()));
    }

    private UnitStructExpression convertUnitStructExpression(
            RustyWhileParser.StructExprUnitContext ctx) {
        throw new UnsupportedOperationException("TODO @ DD: Unit struct expr");
    }

    private TupleStructExpression convertTupleStructExpression(
            RustyWhileParser.StructExprTupleContext ctx) {
        throw new UnsupportedOperationException("TODO @ DD: Tuple struct expr");
    }

    private StructStructExpression convertStructStructExpression(
            RustyWhileParser.StructExprStructContext ctx) {
        throw new UnsupportedOperationException("TODO @ DD: Field struct expr");
    }

    private EnumVariantFieldless convertEnumVariantFieldless(
            RustyWhileParser.EnumExprFieldlessContext ctx) {
        throw new UnsupportedOperationException("TODO @ DD: Fieldless enum variant expr");
    }

    private EnumVariantTuple convertEnumVariantTuple(RustyWhileParser.EnumExprTupleContext ctx) {
        throw new UnsupportedOperationException("TODO @ DD: Tuple enum variant expr");
    }

    private EnumVariantStruct convertEnumVariantStruct(RustyWhileParser.EnumExprStructContext ctx) {
        throw new UnsupportedOperationException("TODO @ DD: Struct enum variant expr");
    }

    private ClosureExpression convertClosureExpression(RustyWhileParser.ClosureExprContext ctx) {
        ImmutableArray<ClosureParam> params =
            ctx.closureParameters() == null ? new ImmutableArray<>()
                    : new ImmutableArray<>(ctx.closureParameters().closureParam().stream()
                            .map(this::convertClosureParam).toList());
        var ty = ctx.typeNoBounds() == null ? null : convertTypeNoBounds(ctx.typeNoBounds());
        var body = ctx.expr() == null ? convertBlockExpr(ctx.blockExpr()) : convertExpr(ctx.expr());
        return new ClosureExpression(ctx.KW_MOVE() != null, params, ty, body);
    }

    private Expr convertExprWithBlock(RustyWhileParser.ExprWithBlockContext ctx) {
        if (ctx.blockExpr() != null)
            return convertBlockExpr(ctx.blockExpr());
        if (ctx.loopExpr() != null)
            return convertLoopExpr(ctx.loopExpr());
        if (ctx.ifExpr() != null)
            return convertIfExpr(ctx.ifExpr());
        if (ctx.ifLetExpr() != null)
            return convertIfLetExpr(ctx.ifLetExpr());
        return convertMatchExpr(ctx.matchExpr());
    }

    private BlockExpression convertBlockExpr(
            org.key_project.rusty.parsing.RustyWhileParser.BlockExprContext ctx) {
        var stmtsCtx = ctx.stmts();

        var stmts = stmtsCtx.stmt().stream().map(this::convertStmt)
                .collect(ImmutableList.collector());
        var value = convertExpr(stmtsCtx.expr());

        return new BlockExpression(stmts, value);
    }

    private LoopExpression convertLoopExpr(RustyWhileParser.LoopExprContext ctx) {
        var label =
            ctx.loopLabel() == null ? null : convertLabel(ctx.loopLabel().LIFETIME_OR_LABEL());
        if (ctx.infiniteLoopExpr() != null)
            return convertInfiniteLoopExpr(ctx.infiniteLoopExpr(), label);
        if (ctx.predicateLoopExpr() != null)
            return convertPredicateLoopExpr(ctx.predicateLoopExpr(), label);
        if (ctx.predicatePatternLoopExpr() != null)
            return convertPredicatePatternLoopExpr(ctx.predicatePatternLoopExpr(), label);
        if (ctx.iteratorLoopExpr() != null)
            return convertIteratorLoopExpr(ctx.iteratorLoopExpr(), label);
        throw new UnsupportedOperationException("Unknown loop: " + ctx.getText());
    }

    private InfiniteLoopExpression convertInfiniteLoopExpr(
            RustyWhileParser.InfiniteLoopExprContext ctx, @Nullable Label label) {
        return new InfiniteLoopExpression(label, convertBlockExpr(ctx.blockExpr()));
    }

    private PredicateLoopExpression convertPredicateLoopExpr(
            RustyWhileParser.PredicateLoopExprContext ctx, @Nullable Label label) {
        return new PredicateLoopExpression(label, convertExpr(ctx.expr()),
            convertBlockExpr(ctx.blockExpr()));
    }

    private PredicatePatternLoopExpression convertPredicatePatternLoopExpr(
            RustyWhileParser.PredicatePatternLoopExprContext ctx, @Nullable Label label) {
        return new PredicatePatternLoopExpression(label, convertPattern(ctx.pattern()),
            convertExpr(ctx.expr()), convertBlockExpr(ctx.blockExpr()));
    }

    private IteratorLoopExpression convertIteratorLoopExpr(
            RustyWhileParser.IteratorLoopExprContext ctx, @Nullable Label label) {
        return new IteratorLoopExpression(label, convertPattern(ctx.pattern()),
            convertExpr(ctx.expr()), convertBlockExpr(ctx.blockExpr()));
    }

    private IfExpression convertIfExpr(RustyWhileParser.IfExprContext ctx) {
        var cond = convertExpr(ctx.expr());
        var then = convertBlockExpr(ctx.blockExpr(0));
        var else_ = ctx.blockExpr().size() > 1 ? convertBlockExpr(ctx.blockExpr(1))
                : ctx.ifExpr() != null ? convertIfExpr(ctx.ifExpr())
                        : null;
        return new IfExpression(cond, then, else_);
    }

    private IfLetExpression convertIfLetExpr(RustyWhileParser.IfLetExprContext ctx) {
        var pat = convertPattern(ctx.pattern());
        var expr = convertExpr(ctx.expr());
        var then = convertBlockExpr(ctx.blockExpr(0));
        var else_ = ctx.blockExpr().size() > 1 ? convertBlockExpr(ctx.blockExpr(1))
                : ctx.ifExpr() != null ? convertIfExpr(ctx.ifExpr())
                        : ctx.ifLetExpr() != null ? convertIfLetExpr(ctx.ifLetExpr()) : null;
        return new IfLetExpression(pat, expr, then, else_);
    }

    private MatchExpression convertMatchExpr(RustyWhileParser.MatchExprContext ctx) {
        var expr = convertExpr(ctx.expr());
        ImmutableArray<MatchArm> arms = ctx.matchArms() == null ? new ImmutableArray<>()
                : convertMatchArms(ctx.matchArms());
        return new MatchExpression(expr, arms);
    }

    private ImmutableArray<MatchArm> convertMatchArms(RustyWhileParser.MatchArmsContext ctx) {
        if (ctx.expr() != null) {
            var arms = new MatchArm[ctx.matchArm().size()];
            for (int i = 0; i < ctx.matchArm().size() - 1; i++) {
                var armCtx = ctx.matchArm().get(i);
                var pat = convertPattern(armCtx.pattern());
                var expr = armCtx.matchArmGuard() == null ? null
                        : convertExpr(armCtx.matchArmGuard().expr());
                var armExprCtx = ctx.matchArmExpression(i);
                var body = armExprCtx.expr() != null ? convertExpr(armExprCtx.expr())
                        : convertExprWithBlock(armExprCtx.exprWithBlock());
                arms[i] = new MatchArm(pat, expr, body);
            }
            var armCtx = ctx.matchArm().get(arms.length - 1);
            var pat = convertPattern(armCtx.pattern());
            var expr =
                armCtx.matchArmGuard() == null ? null : convertExpr(armCtx.matchArmGuard().expr());
            arms[arms.length - 1] = new MatchArm(pat, expr, convertExpr(ctx.expr()));
            return new ImmutableArray<>(arms);
        } else {
            var arms = new MatchArm[ctx.matchArm().size()];
            for (int i = 0; i < ctx.matchArm().size(); i++) {
                var armCtx = ctx.matchArm().get(i);
                var pat = convertPattern(armCtx.pattern());
                var expr = armCtx.matchArmGuard() == null ? null
                        : convertExpr(armCtx.matchArmGuard().expr());
                var armExprCtx = ctx.matchArmExpression(i);
                var body = armExprCtx.expr() != null ? convertExpr(armExprCtx.expr())
                        : convertExprWithBlock(armExprCtx.exprWithBlock());
                arms[i] = new MatchArm(pat, expr, body);
            }
            return new ImmutableArray<>(arms);
        }
    }

    private Statement convertExprStmt(
            org.key_project.rusty.parsing.RustyWhileParser.ExprStmtContext ctx) {
        return new ExpressionStatement(convertExpr(ctx.expr()));
    }

    private Statement convertLetStmt(
            org.key_project.rusty.parsing.RustyWhileParser.LetStmtContext ctx) {
        Pattern pat = convertPatternNoTopAlt(ctx.patternNoTopAlt());
        LetStatement letStatement = new LetStatement(pat,
            convertType(ctx.type_()),
            convertExpr(ctx.expr()));
        declareVariable(pat, letStatement);
        return letStatement;
    }

    private Statement convertStmt(org.key_project.rusty.parsing.RustyWhileParser.StmtContext ctx) {
        if (ctx.SEMI() != null) {
            return new EmptyStatement();
        }
        if (ctx.item() != null)
            return convertItem(ctx.item());
        if (ctx.letStmt() != null)
            return convertLetStmt(ctx.letStmt());
        if (ctx.exprStmt() != null)
            return convertExprStmt(ctx.exprStmt());
        throw new IllegalArgumentException("Expected statement, got: " + ctx.getText());
    }

    private Identifier convertIdentifier(
            org.key_project.rusty.parsing.RustyWhileParser.IdentifierContext ctx) {
        return new Identifier(new Name(ctx.getText()));
    }

    private Pattern convertPattern(
            org.key_project.rusty.parsing.RustyWhileParser.PatternContext ctx) {
        var alts = ctx.patternNoTopAlt();
        if (alts.size() == 1) {
            return convertPatternNoTopAlt(alts.get(0));
        }
        return new AltPattern(
            new ImmutableArray<>(alts.stream().map(this::convertPatternNoTopAlt).toList()));
    }

    private Pattern convertPatternNoTopAlt(RustyWhileParser.PatternNoTopAltContext ctx) {
        if (ctx.patternWithoutRange() != null) {
            var pat = ctx.patternWithoutRange();
            if (pat.literalPattern() != null) {
                return new LiteralPattern();
            }
            if (pat.identifierPattern() != null) {
                return new IdentPattern(pat.identifierPattern().KW_REF() != null,
                    pat.identifierPattern().KW_MUT() != null,
                    convertIdentifier(pat.identifierPattern().identifier()));
            }
            if (pat.wildcardPattern() != null) {
                return WildCardPattern.WILDCARD;
            }
        }
        throw new IllegalArgumentException("Unknown pattern " + ctx.getText());
    }

    private Type convertType(org.key_project.rusty.parsing.RustyWhileParser.Type_Context ctx) {
        if (ctx.typeNoBounds() != null) {
            return convertTypeNoBounds(ctx.typeNoBounds());
        }
        throw new IllegalArgumentException("Unknown type " + ctx.getText());
    }

    private Type convertTypeNoBounds(RustyWhileParser.TypeNoBoundsContext ctx) {
        if (ctx.parenthesizedType() != null)
            return convertParenthesizedType(ctx.parenthesizedType());
        if (ctx.traitObjectTypeOneBound() != null)
            return convertTraitObjectOneBound(ctx.traitObjectTypeOneBound());
        if (ctx.typePath() != null)
            return convertTypePath(ctx.typePath());
        if (ctx.tupleType() != null)
            throw new IllegalArgumentException("TODO @ DD");
        if (ctx.neverType() != null)
            throw new IllegalArgumentException("TODO @ DD");
        throw new IllegalArgumentException("Unknown type " + ctx.getText());
    }

    private Type convertParenthesizedType(
            org.key_project.rusty.parsing.RustyWhileParser.ParenthesizedTypeContext ctx) {
        return convertType(ctx.type_());
    }

    private Type convertTraitObjectOneBound(
            org.key_project.rusty.parsing.RustyWhileParser.TraitObjectTypeOneBoundContext ctx) {
        var tbCtx = ctx.traitBound();
        if (ctx.KW_DYN() == null && tbCtx.QUESTION() == null && tbCtx.forLifetimes() == null) {
            return convertTypePath(tbCtx.typePath());
        }
        throw new IllegalArgumentException("TODO @ DD");
    }

    private Type convertTypePath(
            org.key_project.rusty.parsing.RustyWhileParser.TypePathContext ctx) {
        assert ctx.typePathSegment().size() == 1;
        var text = ctx.typePathSegment(0).pathIdentSegment().identifier().getText();
        return switch (text) {
        case "bool" -> PrimitiveType.BOOL;
        case "u8" -> PrimitiveType.U8;
        case "u16" -> PrimitiveType.U16;
        case "u32" -> PrimitiveType.U32;
        case "u64" -> PrimitiveType.U64;
        case "u128" -> PrimitiveType.U128;
        case "usize" -> PrimitiveType.USIZE;
        case "i8" -> PrimitiveType.I8;
        case "i16" -> PrimitiveType.I16;
        case "i32" -> PrimitiveType.I32;
        case "i64" -> PrimitiveType.I64;
        case "i128" -> PrimitiveType.I128;
        case "isize" -> PrimitiveType.ISIZE;
        case "char" -> PrimitiveType.CHAR;
        case "str" -> PrimitiveType.STR;
        case "!" -> PrimitiveType.NEVER;
        default -> throw new IllegalArgumentException("Unknown type '" + text + "'");
        };
    }

    private ImmutableArray<FunctionParam> convertFunctionParams(
            org.key_project.rusty.parsing.RustyWhileParser.FunctionParamsContext ctx) {
        if (ctx == null)
            return new ImmutableArray<>();
        List<FunctionParam> params = new LinkedList<>();
        if (ctx.selfParam() != null) {
            params.add(convertSelfParam(ctx.selfParam()));
        }
        for (var param : ctx.functionParam()) {
            params.add(convertFunctionParamPattern(param.functionParamPattern()));
        }
        return new ImmutableArray<>(params);
    }

    private SelfParam convertSelfParam(
            org.key_project.rusty.parsing.RustyWhileParser.SelfParamContext ctx) {
        if (ctx.shorthandSelf() != null) {
            var shortSelf = ctx.shorthandSelf();
            return new SelfParam(shortSelf.AND() != null, shortSelf.KW_MUT() != null, null);
        } else {
            var self = ctx.typedSelf();
            return new SelfParam(/* TODO */ false, self.KW_MUT() != null,
                convertType(self.type_()));
        }
    }

    private FunctionParamPattern convertFunctionParamPattern(
            org.key_project.rusty.parsing.RustyWhileParser.FunctionParamPatternContext ctx) {
        FunctionParamPattern param = new FunctionParamPattern(convertPattern(ctx.pattern()),
            convertType(ctx.type_()));
        declareVariable(((IdentPattern) param.getPattern()).name().toString(), param);
        return param;
    }

    private PathExprSegment convertPathExprSegment(RustyWhileParser.PathExprSegmentContext ctx) {
        return new PathExprSegment(convertPathIdentSegment(ctx.pathIdentSegment()));
    }

    private PathIdentSegment convertPathIdentSegment(
            org.key_project.rusty.parsing.RustyWhileParser.PathIdentSegmentContext ctx) {
        return new PathIdentSegment(convertIdentifier(ctx.identifier()));
    }

    private Label convertLabel(TerminalNode l) {
        return getLabel(l.getText().substring(1));
    }

    private ClosureParam convertClosureParam(RustyWhileParser.ClosureParamContext ctx) {
        var pat = convertPattern(ctx.pattern());
        var ty = ctx.type_() == null ? null : convertType(ctx.type_());
        return new ClosureParam(pat, ty);
    }
}
