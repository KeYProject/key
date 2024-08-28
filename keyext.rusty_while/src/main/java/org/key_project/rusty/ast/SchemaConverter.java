/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast;

import java.math.BigInteger;
import java.util.*;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
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
import org.key_project.rusty.logic.op.sv.OperatorSV;
import org.key_project.rusty.logic.op.sv.ProgramSV;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.logic.sort.ProgramSVSort;
import org.key_project.rusty.parsing.RustyWhileSchemaParser;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;

public class SchemaConverter {
    private Namespace<@NonNull SchemaVariable> svNS;

    // TODO: Rework this properly
    private final Map<String, VariableDeclaration> variables = new HashMap<>();
    private final Map<VariableDeclaration, ProgramVariable> programVariables = new HashMap<>();

    private final Services services;

    public SchemaConverter(Namespace<@NonNull SchemaVariable> svNS, Services services) {
        this.svNS = svNS;
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

    private void declareVariable(String name, VariableDeclaration decl) {
        variables.put(name, decl);
        programVariables.put(decl, new ProgramVariable(new Name(name),
            new KeYRustyType(decl.getType().getSort(services))));
    }

    private VariableDeclaration getDecl(PathInExpression path) {
        // TODO: For now, only use local vars, i.e., ignore all but the last segment
        return variables.get(path.segments().last().segment().ident().name().toString());
    }

    private ProgramVariable getProgramVariable(PathInExpression path) {
        return programVariables.get(getDecl(path));
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
        return new Crate(ctx.item().stream().map(this::convertItem)
                .collect(ImmutableList.collector()));
    }


    public Item convertItem(org.key_project.rusty.parsing.RustyWhileSchemaParser.ItemContext ctx) {
        // TODO: Rework
        return convertFunction(ctx.function_());
    }

    public Function convertFunction(
            org.key_project.rusty.parsing.RustyWhileSchemaParser.Function_Context ctx) {
        Name name = convertIdentifier(ctx.identifier()).name();
        ImmutableArray<FunctionParam> params =
            convertFunctionParams(ctx.functionParams());
        Type returnType = convertType(ctx.functionRetTy().type_());
        BlockExpression body =
            convertBlockExpr(
                ctx.blockExpr());
        return new Function(name,
            params,
            returnType,
            body);
    }

    public Expr convertExpr(org.key_project.rusty.parsing.RustyWhileSchemaParser.ExprContext ctx) {
        if (ctx instanceof org.key_project.rusty.parsing.RustyWhileSchemaParser.LiteralExpressionContext lit)
            return convertLiteralExpr(lit.literalExpr());
        if (ctx instanceof org.key_project.rusty.parsing.RustyWhileSchemaParser.PathExpressionContext path)
            return convertPathExpr(path.pathExpr());
        if (ctx instanceof org.key_project.rusty.parsing.RustyWhileSchemaParser.ArithmeticOrLogicalExpressionContext ale)
            return convertArithmeticOrLogicalExpression(ale);
        if (ctx instanceof org.key_project.rusty.parsing.RustyWhileSchemaParser.AssignmentExpressionContext ae)
            return convertAssignmentExpression(ae);
        if (ctx instanceof RustyWhileSchemaParser.SchemaVarExpressionContext  se)
            return convertSchemaVarExpression(se);
        throw new IllegalArgumentException("TODO @ DD: handle " + ctx.getText());
    }

    public Expr convertArithmeticOrLogicalExpression(
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
        return new ArithLogicalExpression(convertExpr(ctx.expr(0)), op,
            convertExpr(ctx.expr(1)));
    }

    public AssignmentExpression convertAssignmentExpression(
            org.key_project.rusty.parsing.RustyWhileSchemaParser.AssignmentExpressionContext ctx) {
        var lhs = convertExpr(ctx.expr(0));
        var rhs = convertExpr(ctx.expr(1));
        return new AssignmentExpression(lhs, rhs);
    }

    public BlockExpression convertBlockExpr(org.key_project.rusty.parsing.RustyWhileSchemaParser.BlockExprContext ctx) {
        if (ctx instanceof RustyWhileSchemaParser.ContextBlockExprContext cctx) {
            return convertContextBlockExpr(cctx);
        }
        return convertStandardBlockExpr((RustyWhileSchemaParser.StandardBlockExprContext) ctx);
    }

    public BlockExpression convertStandardBlockExpr(
            org.key_project.rusty.parsing.RustyWhileSchemaParser.StandardBlockExprContext ctx) {
        var stmtsCtx = ctx.stmts();

        var stmts = stmtsCtx.stmt().stream().map(this::convertStmt)
                .collect(ImmutableList.collector());
        if (stmts.size() == 1 && stmts.get(0) instanceof ProgramSV psv && (psv.sort() == ProgramSVSort.EXPRESSION || psv.sort() == ProgramSVSort.SIMPLE_EXPRESSION
                || psv.sort() == ProgramSVSort.NONSIMPLEEXPRESSION)) {
            return new BlockExpression(ImmutableSLList.nil(), psv);
        }
        var value = convertExpr(stmtsCtx.expr());

        return new BlockExpression(stmts, value);
    }

    public ContextBlockExpression convertContextBlockExpr(
            org.key_project.rusty.parsing.RustyWhileSchemaParser.ContextBlockExprContext ctx) {
        var stmtsCtx = ctx.stmts();

        ImmutableList<Statement> stmts = stmtsCtx == null ? ImmutableSLList.nil()
                : stmtsCtx.stmt().stream().map(this::convertStmt)
                        .collect(ImmutableList.collector());
        return new ContextBlockExpression(stmts);
    }

    public Expr convertLiteralExpr(
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

    public ProgramVariable convertPathExpr(
            org.key_project.rusty.parsing.RustyWhileSchemaParser.PathExprContext ctx) {
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

    public Expr convertSchemaVarExpression(
            org.key_project.rusty.parsing.RustyWhileSchemaParser.SchemaVarExpressionContext ctx) {
        return (ProgramSV) lookupSchemaVariable(ctx.schemaVariable().getText().substring(2));
    }

    public Statement convertExprStmt(
            org.key_project.rusty.parsing.RustyWhileSchemaParser.ExprStmtContext ctx) {
        return new ExpressionStatement(convertExpr(ctx.expr()));
    }

    public Statement convertLetStmt(
            org.key_project.rusty.parsing.RustyWhileSchemaParser.LetStmtContext ctx) {
        Pattern pat = convertPatternNoTopAlt(ctx.patternNoTopAlt());
        LetStatement letStatement = new LetStatement(pat,
            convertType(ctx.type_()),
            convertExpr(ctx.expr()));
        declareVariable(pat, letStatement);
        return letStatement;
    }

    public Statement convertStmt(
            org.key_project.rusty.parsing.RustyWhileSchemaParser.StmtContext ctx) {
        if (ctx.SEMI() != null) {
            return new EmptyStatement();
        }
        if (ctx.item() != null)
            return convertItem(ctx.item());
        if (ctx.letStmt() != null)
            return convertLetStmt(ctx.letStmt());
        if (ctx.exprStmt() != null)
            return convertExprStmt(ctx.exprStmt());
        if (ctx.schemaStmt() != null)
            return convertSchemaStmt(ctx.schemaStmt());
        throw new IllegalArgumentException("Expected statement, got: " + ctx.getText());
    }

    public Statement convertSchemaStmt(
            org.key_project.rusty.parsing.RustyWhileSchemaParser.SchemaStmtContext ctx) {
        return (ProgramSV) lookupSchemaVariable(ctx.schemaVariable().getText().substring(2));
    }

    public Identifier convertIdentifier(
            org.key_project.rusty.parsing.RustyWhileSchemaParser.IdentifierContext ctx) {
        return new Identifier(new Name(ctx.getText()));
    }

    public Pattern convertPattern(
            org.key_project.rusty.parsing.RustyWhileSchemaParser.PatternContext ctx) {
        var alts = ctx.patternNoTopAlt();
        if (alts.size() == 1) {
            return convertPatternNoTopAlt(alts.get(0));
        }
        return new AltPattern(
            new ImmutableArray<>(alts.stream().map(this::convertPatternNoTopAlt).toList()));
    }

    private Pattern convertPatternNoTopAlt(
            org.key_project.rusty.parsing.RustyWhileSchemaParser.PatternNoTopAltContext ctx) {
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

    public Type convertType(org.key_project.rusty.parsing.RustyWhileSchemaParser.Type_Context ctx) {
        if (ctx.typeNoBounds() != null) {
            var ty = ctx.typeNoBounds();
            if (ty.parenthesizedType() != null)
                return convertParenthesizedType(ty.parenthesizedType());
            if (ty.traitObjectTypeOneBound() != null)
                return convertTraitObjectOneBound(ty.traitObjectTypeOneBound());
            if (ty.typePath() != null)
                return convertTypePath(ty.typePath());
            if (ty.tupleType() != null)
                throw new IllegalArgumentException("TODO @ DD");
            if (ty.neverType() != null)
                throw new IllegalArgumentException("TODO @ DD");
        }
        throw new IllegalArgumentException("Unknown type " + ctx.getText());
    }

    public Type convertParenthesizedType(
            org.key_project.rusty.parsing.RustyWhileSchemaParser.ParenthesizedTypeContext ctx) {
        return convertType(ctx.type_());
    }

    private Type convertTraitObjectOneBound(RustyWhileSchemaParser.TraitObjectTypeOneBoundContext ctx) {
        var tbCtx =ctx.traitBound();
        if (ctx.KW_DYN() == null && tbCtx.QUESTION() == null && tbCtx.forLifetimes() == null) {
            return convertTypePath(tbCtx.typePath());
        }
        throw new IllegalArgumentException("TODO @ DD");
    }

    public PrimitiveType convertTypePath(
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

    public ImmutableArray<FunctionParam> convertFunctionParams(
            org.key_project.rusty.parsing.RustyWhileSchemaParser.FunctionParamsContext ctx) {
        if (ctx == null) return new ImmutableArray<>();
        List<FunctionParam> params = new LinkedList<>();
        if (ctx.selfParam() != null) {
            params.add(convertSelfParam(ctx.selfParam()));
        }
        for (var param : ctx.functionParam()) {
            params.add(convertFunctionParamPattern(param.functionParamPattern()));
        }
        return new ImmutableArray<>(params);
    }

    public SelfParam convertSelfParam(
            org.key_project.rusty.parsing.RustyWhileSchemaParser.SelfParamContext ctx) {
        if (ctx.shorthandSelf() != null) {
            var shortSelf = ctx.shorthandSelf();
            return new SelfParam(shortSelf.AND() != null, shortSelf.KW_MUT() != null, null);
        } else {
            var self = ctx.typedSelf();
            return new SelfParam(/* TODO */ false, self.KW_MUT() != null,
                convertType(self.type_()));
        }
    }

    public FunctionParamPattern convertFunctionParamPattern(
            org.key_project.rusty.parsing.RustyWhileSchemaParser.FunctionParamPatternContext ctx) {
        FunctionParamPattern param = new FunctionParamPattern(convertPattern(ctx.pattern()),
            convertType(ctx.type_()));
        declareVariable(((IdentPattern) param.getPattern()).name().toString(), param);
        return param;
    }

    public PathExprSegment convertPathExprSegment(
            org.key_project.rusty.parsing.RustyWhileSchemaParser.PathExprSegmentContext ctx) {
        return new PathExprSegment(convertPathIdentSegment(ctx.pathIdentSegment()));
    }

    public PathIdentSegment convertPathIdentSegment(
            org.key_project.rusty.parsing.RustyWhileSchemaParser.PathIdentSegmentContext ctx) {
        return new PathIdentSegment(convertIdentifier(ctx.identifier()));
    }
}
