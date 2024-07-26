/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast;

import java.math.BigInteger;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
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
import org.key_project.rusty.logic.op.sv.OperatorSV;
import org.key_project.rusty.logic.op.sv.ProgramSV;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

public class SchemaConverter {
    private Namespace<@NonNull SchemaVariable> svNS;

    private final CrateConverter crateConverter;
    private final ItemConverter itemConverter;
    private final ExprConverter exprConverter;
    private final StmtConverter stmtConverter;
    private final IdentifierConverter identifierConverter;
    private final PatternConverter patternConverter;
    private final TypeConverter typeConverter;
    private final ParamConverter paramConverter;

    public SchemaConverter(Namespace<@NonNull SchemaVariable> svNS) {
        this.svNS = svNS;
        crateConverter = new CrateConverter(this);
        itemConverter = new ItemConverter(this);
        exprConverter = new ExprConverter(this);
        stmtConverter = new StmtConverter(this);
        identifierConverter = new IdentifierConverter(this);
        patternConverter = new PatternConverter(this);
        typeConverter = new TypeConverter(this);
        paramConverter = new ParamConverter(this);
    }

    public OperatorSV lookupSchemaVariable(String s) {
        OperatorSV sv;
        SchemaVariable n = svNS.lookup(new Name(s));
        if (n instanceof OperatorSV asv) {
            sv = asv;
        } else {
            throw new RuntimeException("Schema variable not declared: " + s);
        }
        return sv;
    }

    public Crate convertCrate(
            org.key_project.rusty.parsing.RustyWhileSchemaParser.CrateContext ctx) {
        return ctx.accept(crateConverter);
    }

    public BlockExpression convertBlockExpr(
            org.key_project.rusty.parsing.RustyWhileSchemaParser.BlockExprContext ctx) {
        return (BlockExpression) ctx.accept(exprConverter);
    }

    private static class CrateConverter
            extends org.key_project.rusty.parsing.RustyWhileSchemaParserBaseVisitor<Crate> {
        SchemaConverter converter;

        private CrateConverter(SchemaConverter converter) {
            this.converter = converter;
        }

        @Override
        public Crate visitCrate(
                org.key_project.rusty.parsing.RustyWhileSchemaParser.CrateContext ctx) {
            return new Crate(ctx.item().stream().map(i -> i.accept(converter.itemConverter))
                    .collect(ImmutableList.collector()));
        }
    }

    private static class ItemConverter
            extends org.key_project.rusty.parsing.RustyWhileSchemaParserBaseVisitor<Item> {
        SchemaConverter converter;

        private ItemConverter(SchemaConverter converter) {
            this.converter = converter;
        }

        @Override
        public Item visitItem(
                org.key_project.rusty.parsing.RustyWhileSchemaParser.ItemContext ctx) {
            // TODO: Rework
            return ctx.function_().accept(this);
        }

        @Override
        public Function visitFunction_(
                org.key_project.rusty.parsing.RustyWhileSchemaParser.Function_Context ctx) {
            return new Function(ctx.identifier().accept(converter.identifierConverter).name(),
                ctx.functionParams().functionParam().stream()
                        .map(p -> p.accept(converter.paramConverter))
                        .collect(ImmutableList.collector()),
                ctx.functionRetTy().type_().accept(converter.typeConverter),
                (BlockExpression) ctx.blockExpr().accept(converter.exprConverter));
        }
    }

    private static class ExprConverter
            extends org.key_project.rusty.parsing.RustyWhileSchemaParserBaseVisitor<Expr> {
        SchemaConverter converter;

        private ExprConverter(SchemaConverter converter) {
            this.converter = converter;
        }

        @Override
        public Expr visitArithmeticOrLogicalExpression(
                org.key_project.rusty.parsing.RustyWhileSchemaParser.ArithmeticOrLogicalExpressionContext ctx) {
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
                org.key_project.rusty.parsing.RustyWhileSchemaParser.AssignmentExpressionContext ctx) {
            var lhs = ctx.expr(0).accept(this);
            var rhs = ctx.expr(1).accept(this);
            return new AssignmentExpression(lhs, rhs);
        }

        @Override
        public BlockExpression visitStandardBlockExpr(
                org.key_project.rusty.parsing.RustyWhileSchemaParser.StandardBlockExprContext ctx) {
            var stmtsCtx = ctx.stmts();

            var stmts = stmtsCtx.stmt().stream().map(s -> s.accept(converter.stmtConverter))
                    .collect(ImmutableList.collector());
            var value = stmtsCtx.expr().accept(this);

            return new BlockExpression(stmts, value);
        }

        @Override
        public Expr visitContextBlockExpr(
                org.key_project.rusty.parsing.RustyWhileSchemaParser.ContextBlockExprContext ctx) {
            var stmtsCtx = ctx.stmts();

            var stmts = stmtsCtx.stmt().stream().map(s -> s.accept(converter.stmtConverter))
                    .collect(ImmutableList.collector());
            var value = stmtsCtx.expr().accept(this);

            return new ContextBlockExpression(stmts, value);
        }

        @Override
        public Expr visitLiteralExpr(
                org.key_project.rusty.parsing.RustyWhileSchemaParser.LiteralExprContext ctx) {
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

        @Override
        public PathExpression visitPathExpr(
                org.key_project.rusty.parsing.RustyWhileSchemaParser.PathExprContext ctx) {
            assert ctx.pathExprSegment().size() == 1;
            return new PathExpression(
                ctx.pathExprSegment(0).pathIdentSegment().identifier()
                        .accept(converter.identifierConverter));
        }

        @Override
        public Expr visitSchemaVarExpression(
                org.key_project.rusty.parsing.RustyWhileSchemaParser.SchemaVarExpressionContext ctx) {
            return (ProgramSV) converter
                    .lookupSchemaVariable(ctx.schemaVariable().getText().substring(2));
        }
    }

    private static class StmtConverter
            extends org.key_project.rusty.parsing.RustyWhileSchemaParserBaseVisitor<Statement> {
        SchemaConverter converter;

        private StmtConverter(SchemaConverter converter) {
            this.converter = converter;
        }

        @Override
        public Statement visitExprStmt(
                org.key_project.rusty.parsing.RustyWhileSchemaParser.ExprStmtContext ctx) {
            return new ExpressionStatement(ctx.expr().accept(converter.exprConverter));
        }

        @Override
        public Statement visitLetStmt(
                org.key_project.rusty.parsing.RustyWhileSchemaParser.LetStmtContext ctx) {
            return new LetStatement(ctx.pattern().accept(converter.patternConverter),
                ctx.type_().accept(converter.typeConverter),
                ctx.expr().accept(converter.exprConverter));
        }

        @Override
        public Statement visitSchemaStmt(
                org.key_project.rusty.parsing.RustyWhileSchemaParser.SchemaStmtContext ctx) {
            return (ProgramSV) converter
                    .lookupSchemaVariable(ctx.schemaVariable().getText().substring(2));
        }
    }

    private static class IdentifierConverter
            extends org.key_project.rusty.parsing.RustyWhileSchemaParserBaseVisitor<Identifier> {
        SchemaConverter converter;

        private IdentifierConverter(SchemaConverter converter) {
            this.converter = converter;
        }

        @Override
        public Identifier visitIdentifier(
                org.key_project.rusty.parsing.RustyWhileSchemaParser.IdentifierContext ctx) {
            return new Identifier(new Name(ctx.getText()));
        }
    }

    private static class PatternConverter
            extends org.key_project.rusty.parsing.RustyWhileSchemaParserBaseVisitor<Pattern> {
        SchemaConverter converter;

        private PatternConverter(SchemaConverter converter) {
            this.converter = converter;
        }

        @Override
        public Pattern visitPattern(
                org.key_project.rusty.parsing.RustyWhileSchemaParser.PatternContext ctx) {
            var isMut = ctx.KW_MUT() != null;
            if (ctx.identifier() != null) {
                return new IdentPattern(isMut,
                    ctx.identifier().accept(converter.identifierConverter));
            }
            return (ProgramSV) converter
                    .lookupSchemaVariable(ctx.schemaVariable().getText().substring(2));
        }
    }

    private static class TypeConverter
            extends org.key_project.rusty.parsing.RustyWhileSchemaParserBaseVisitor<Type> {
        SchemaConverter converter;

        private TypeConverter(SchemaConverter converter) {
            this.converter = converter;
        }

        @Override
        public Type visitParenthesizedType(
                org.key_project.rusty.parsing.RustyWhileSchemaParser.ParenthesizedTypeContext ctx) {
            return ctx.type_().accept(this);
        }

        @Override
        public Type visitTypePath(
                org.key_project.rusty.parsing.RustyWhileSchemaParser.TypePathContext ctx) {
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
            extends org.key_project.rusty.parsing.RustyWhileSchemaParserBaseVisitor<Param> {
        SchemaConverter converter;

        private ParamConverter(SchemaConverter converter) {
            this.converter = converter;
        }

        @Override
        public Param visitFunctionParamPattern(
                org.key_project.rusty.parsing.RustyWhileSchemaParser.FunctionParamPatternContext ctx) {
            return new Param(ctx.pattern().accept(converter.patternConverter),
                ctx.type_().accept(converter.typeConverter));
        }
    }
}
