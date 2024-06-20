/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast;

import java.math.BigInteger;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.expr.*;
import org.key_project.rusty.ast.fn.Function;
import org.key_project.rusty.ast.fn.Param;
import org.key_project.rusty.ast.pat.IdentPattern;
import org.key_project.rusty.ast.pat.Pattern;
import org.key_project.rusty.ast.stmt.ExpressionStatement;
import org.key_project.rusty.ast.stmt.LetStatement;
import org.key_project.rusty.ast.stmt.Statement;
import org.key_project.rusty.ast.ty.PrimitiveType;
import org.key_project.rusty.ast.ty.Type;
import org.key_project.util.collection.ImmutableList;

public class Converter
        extends org.key_project.rusty.parsing.RustyWhileParserBaseVisitor<SyntaxElement> {
    private static final CrateConverter crateConverter = new CrateConverter();
    private static final ItemConverter itemConverter = new ItemConverter();
    private static final ExprConverter exprConverter = new ExprConverter();
    private static final StmtConverter stmtConverter = new StmtConverter();
    private static final IdentifierConverter identifierConverter = new IdentifierConverter();
    private static final PatternConverter patternConverter = new PatternConverter();
    private static final TypeConverter typeConverter = new TypeConverter();
    private static final ParamConverter paramConverter = new ParamConverter();

    public static Crate convertCrate(
            org.key_project.rusty.parsing.RustyWhileParser.CrateContext ctx) {
        return ctx.accept(crateConverter);
    }

    @Override
    public Expr visitAssignmentExpression(
            org.key_project.rusty.parsing.RustyWhileParser.AssignmentExpressionContext ctx) {
        return exprConverter.visitAssignmentExpression(ctx);
    }

    @Override
    public Expr visitBlockExpr(
            org.key_project.rusty.parsing.RustyWhileParser.BlockExprContext ctx) {
        return exprConverter.visitBlockExpr(ctx);
    }

    @Override
    public Expr visitLiteralExpr(
            org.key_project.rusty.parsing.RustyWhileParser.LiteralExprContext ctx) {
        return exprConverter.visitLiteralExpr(ctx);
    }

    @Override
    public Expr visitPathExpr(org.key_project.rusty.parsing.RustyWhileParser.PathExprContext ctx) {
        return exprConverter.visitPathExpr(ctx);
    }

    @Override
    public Statement visitExprStmt(
            org.key_project.rusty.parsing.RustyWhileParser.ExprStmtContext ctx) {
        return stmtConverter.visitExprStmt(ctx);
    }

    @Override
    public Statement visitLetStmt(
            org.key_project.rusty.parsing.RustyWhileParser.LetStmtContext ctx) {
        return stmtConverter.visitLetStmt(ctx);
    }

    @Override
    public Identifier visitIdentifier(
            org.key_project.rusty.parsing.RustyWhileParser.IdentifierContext ctx) {
        return identifierConverter.visitIdentifier(ctx);
    }

    @Override
    public Pattern visitPattern(org.key_project.rusty.parsing.RustyWhileParser.PatternContext ctx) {
        return patternConverter.visitPattern(ctx);
    }

    public Type convertParenthesizedType(
            org.key_project.rusty.parsing.RustyWhileParser.ParenthesizedTypeContext ctx) {
        return typeConverter.visitParenthesizedType(ctx);
    }

    public Type convertTypePath(
            org.key_project.rusty.parsing.RustyWhileParser.TypePathContext ctx) {
        return typeConverter.visitTypePath(ctx);
    }

    private static class CrateConverter
            extends org.key_project.rusty.parsing.RustyWhileParserBaseVisitor<Crate> {
        @Override
        public Crate visitCrate(org.key_project.rusty.parsing.RustyWhileParser.CrateContext ctx) {
            return new Crate(ctx.item().stream().map(i -> i.accept(itemConverter))
                    .collect(ImmutableList.collector()));
        }
    }

    private static class ItemConverter
            extends org.key_project.rusty.parsing.RustyWhileParserBaseVisitor<Item> {
        @Override
        public Item visitItem(org.key_project.rusty.parsing.RustyWhileParser.ItemContext ctx) {
            // TODO: Rework
            return ctx.function_().accept(this);
        }

        @Override
        public Function visitFunction_(
                org.key_project.rusty.parsing.RustyWhileParser.Function_Context ctx) {
            return new Function(ctx.identifier().accept(identifierConverter).name(),
                ctx.functionParams().functionParam().stream().map(p -> p.accept(paramConverter))
                        .collect(ImmutableList.collector()),
                ctx.functionRetTy().type_().accept(typeConverter),
                (BlockExpression) ctx.blockExpr().accept(exprConverter));
        }
    }

    private static class ExprConverter
            extends org.key_project.rusty.parsing.RustyWhileParserBaseVisitor<Expr> {
        @Override
        public Expr visitArithmeticOrLogicalExpression(
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
            return new ArithLogicalExpression(ctx.expr(0).accept(this), op,
                ctx.expr(1).accept(this));
        }

        @Override
        public AssignmentExpression visitAssignmentExpression(
                org.key_project.rusty.parsing.RustyWhileParser.AssignmentExpressionContext ctx) {
            var lhs = ctx.expr(0).accept(this);
            var rhs = ctx.expr(1).accept(this);
            return new AssignmentExpression(lhs, rhs);
        }

        @Override
        public BlockExpression visitBlockExpr(
                org.key_project.rusty.parsing.RustyWhileParser.BlockExprContext ctx) {
            var stmtsCtx = ctx.stmts();

            var stmts = stmtsCtx.stmt().stream().map(s -> s.accept(stmtConverter))
                    .collect(ImmutableList.collector());
            var value = stmtsCtx.expr().accept(this);

            return new BlockExpression(stmts, value);
        }

        @Override
        public Expr visitLiteralExpr(
                org.key_project.rusty.parsing.RustyWhileParser.LiteralExprContext ctx) {
            if (ctx.KW_TRUE() != null)
                return new BooleanLiteralExpression(true);
            if (ctx.KW_FALSE() != null)
                return new BooleanLiteralExpression(false);
            var intLit = ctx.INTEGER_LITERAL();
            if (intLit != null) {
                var text = intLit.getText();
                var split = text.split("_");
                var suffix = switch (split[split.length - 1]) {
                case "u8" -> IntegerLiteralExpression.IntegerSuffix.u8;
                case "u16" -> IntegerLiteralExpression.IntegerSuffix.u16;
                case "u32" -> IntegerLiteralExpression.IntegerSuffix.u32;
                case "u64" -> IntegerLiteralExpression.IntegerSuffix.u64;
                case "u128" -> IntegerLiteralExpression.IntegerSuffix.u128;
                case "usize" -> IntegerLiteralExpression.IntegerSuffix.usize;
                case "i8" -> IntegerLiteralExpression.IntegerSuffix.i8;
                case "i16" -> IntegerLiteralExpression.IntegerSuffix.i16;
                case "i32" -> IntegerLiteralExpression.IntegerSuffix.i32;
                case "i64" -> IntegerLiteralExpression.IntegerSuffix.i64;
                case "i128" -> IntegerLiteralExpression.IntegerSuffix.i128;
                case "isize" -> IntegerLiteralExpression.IntegerSuffix.isize;
                default -> throw new IllegalArgumentException(
                    "Right now we require a suffix on all literals");
                };

                var value = new BigInteger(
                    text.substring(0, text.length() - split[split.length - 1].length()));
                return new IntegerLiteralExpression(value, suffix);
            }

            throw new IllegalArgumentException("Expected boolean or integer literal");
        }

        @Override
        public PathExpression visitPathExpr(
                org.key_project.rusty.parsing.RustyWhileParser.PathExprContext ctx) {
            assert ctx.pathExprSegment().size() == 1;
            return new PathExpression(
                ctx.pathExprSegment(0).pathIdentSegment().identifier().accept(identifierConverter));
        }
    }

    private static class StmtConverter
            extends org.key_project.rusty.parsing.RustyWhileParserBaseVisitor<Statement> {
        @Override
        public Statement visitExprStmt(
                org.key_project.rusty.parsing.RustyWhileParser.ExprStmtContext ctx) {
            return new ExpressionStatement(ctx.expr().accept(exprConverter));
        }

        @Override
        public Statement visitLetStmt(
                org.key_project.rusty.parsing.RustyWhileParser.LetStmtContext ctx) {
            return new LetStatement(ctx.pattern().accept(patternConverter),
                ctx.type_().accept(typeConverter), ctx.expr().accept(exprConverter));
        }
    }

    private static class IdentifierConverter
            extends org.key_project.rusty.parsing.RustyWhileParserBaseVisitor<Identifier> {
        @Override
        public Identifier visitIdentifier(
                org.key_project.rusty.parsing.RustyWhileParser.IdentifierContext ctx) {
            return new Identifier(new Name(ctx.getText()));
        }
    }

    private static class PatternConverter
            extends org.key_project.rusty.parsing.RustyWhileParserBaseVisitor<Pattern> {
        @Override
        public Pattern visitPattern(
                org.key_project.rusty.parsing.RustyWhileParser.PatternContext ctx) {
            return new IdentPattern(ctx.KW_MUT() != null,
                ctx.identifier().accept(identifierConverter));
        }
    }

    private static class TypeConverter
            extends org.key_project.rusty.parsing.RustyWhileParserBaseVisitor<Type> {
        @Override
        public Type visitParenthesizedType(
                org.key_project.rusty.parsing.RustyWhileParser.ParenthesizedTypeContext ctx) {
            return ctx.type_().accept(this);
        }

        @Override
        public Type visitTypePath(
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
    }

    private static class ParamConverter
            extends org.key_project.rusty.parsing.RustyWhileParserBaseVisitor<Param> {
        @Override
        public Param visitFunctionParamPattern(
                org.key_project.rusty.parsing.RustyWhileParser.FunctionParamPatternContext ctx) {
            return new Param(ctx.pattern().accept(patternConverter),
                ctx.type_().accept(typeConverter));
        }
    }
}
