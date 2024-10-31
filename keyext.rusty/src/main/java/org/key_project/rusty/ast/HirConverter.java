/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;

import org.key_project.logic.Name;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.abstraction.PrimitiveType;
import org.key_project.rusty.ast.expr.*;
import org.key_project.rusty.ast.expr.Expr;
import org.key_project.rusty.ast.fn.Function;
import org.key_project.rusty.ast.fn.FunctionParam;
import org.key_project.rusty.ast.fn.FunctionParamPattern;
import org.key_project.rusty.ast.pat.BindingPattern;
import org.key_project.rusty.ast.pat.PathPattern;
import org.key_project.rusty.ast.pat.Pattern;
import org.key_project.rusty.ast.pat.WildCardPattern;
import org.key_project.rusty.ast.stmt.ExpressionStatement;
import org.key_project.rusty.ast.stmt.ItemStatement;
import org.key_project.rusty.ast.stmt.LetStatement;
import org.key_project.rusty.ast.stmt.Statement;
import org.key_project.rusty.ast.ty.PathRustType;
import org.key_project.rusty.ast.ty.PrimitiveRustType;
import org.key_project.rusty.ast.ty.RustType;
import org.key_project.rusty.ast.ty.TupleRustType;
import org.key_project.rusty.parser.hir.Ident;
import org.key_project.rusty.parser.hir.QPath;
import org.key_project.rusty.parser.hir.expr.*;
import org.key_project.rusty.parser.hir.hirty.HirTy;
import org.key_project.rusty.parser.hir.hirty.HirTyKind;
import org.key_project.rusty.parser.hir.hirty.PrimHirTy;
import org.key_project.rusty.parser.hir.hirty.UintTy;
import org.key_project.rusty.parser.hir.item.Fn;
import org.key_project.rusty.parser.hir.item.FnRetTy;
import org.key_project.rusty.parser.hir.item.ImplicitSelfKind;
import org.key_project.rusty.parser.hir.pat.ByRef;
import org.key_project.rusty.parser.hir.pat.Pat;
import org.key_project.rusty.parser.hir.pat.PatKind;
import org.key_project.rusty.parser.hir.stmt.LetStmt;
import org.key_project.rusty.parser.hir.stmt.Stmt;
import org.key_project.rusty.parser.hir.stmt.StmtKind;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

public class HirConverter {
    private final Services services;

    public HirConverter(Services services) {
        this.services = services;
    }

    public Services getServices() {
        return services;
    }

    public Crate convertCrate(org.key_project.rusty.parser.hir.Crate crate) {
        return new Crate(convertMod(crate.topMod()));
    }

    private String convertIdent(Ident ident) {
        return ident.name();
    }

    private Mod convertMod(org.key_project.rusty.parser.hir.Mod mod) {
        return new Mod(
            Arrays.stream(mod.items()).map(this::convertItem).collect(ImmutableList.collector()));
    }

    private Item convertItem(org.key_project.rusty.parser.hir.item.Item item) {
        String ident = convertIdent(item.ident());
        return switch (item.kind()) {
            case org.key_project.rusty.parser.hir.item.Use use -> convertUse(use);
            case Fn fn -> convertFn(fn, ident);
            case org.key_project.rusty.parser.hir.item.ExternCrate ec -> convertExternCrate(ec, ident);
            default -> throw new IllegalArgumentException("Unknown item: " + item);
        };
    }

    private Item convertUse(org.key_project.rusty.parser.hir.item.Use use) {
        var path = convertPath(use.path(), rs -> {
            var lst = rs.stream().map(this::convertRes).toList();
            return new ImmutableArray<>(lst);
        });
        var kind = switch (use.kind()) {
        case org.key_project.rusty.parser.hir.item.Use.UseKind.Single -> Use.UseKind.Single;
        case org.key_project.rusty.parser.hir.item.Use.UseKind.Glob -> Use.UseKind.Glob;
        case org.key_project.rusty.parser.hir.item.Use.UseKind.ListStem -> Use.UseKind.ListStem;
        };
        return new Use(path, kind);
    }

    private Function convertFn(Fn fn, String ident) {
        var name = new Name(ident);
        int paramLength = fn.sig().decl().inputs().length;
        int selfCount = 0;
        if (fn.sig().decl().implicitSelf() != ImplicitSelfKind.None) {
            selfCount++;
        }
        var params = new ArrayList<FunctionParam>(paramLength + selfCount);
        for (int i = 0; i < paramLength; i++) {
            var ty = fn.sig().decl().inputs()[i];
            var pat = fn.body().params()[i].pat();
            params.add(new FunctionParamPattern(convertPat(pat), convertHirTy(ty)));
        }
        var retTy = convertFnRetTy(fn.sig().decl().output());
        var body = (BlockExpression) convertExpr(fn.body().value());
        return new Function(name, new ImmutableArray<>(params), retTy, body);
    }

    private RustType convertFnRetTy(FnRetTy retTy) {
        return switch(retTy) {
            case FnRetTy.DefaultReturn x -> TupleRustType.UNIT;
            case FnRetTy.Return r -> convertHirTy(r.ty());
            default -> throw new IllegalArgumentException("Unknown return type: " + retTy);
        };
    }

    private Item convertExternCrate(org.key_project.rusty.parser.hir.item.ExternCrate ec,
            String ident) {
        return new ExternCrate(ident, ec.symbol());
    }

    private Expr convertExpr(org.key_project.rusty.parser.hir.expr.Expr expr) {
        return switch (expr.kind()) {
          case   ExprKind.BlockExpr e -> convertBlockExpr(e);
            case   ExprKind.LitExpr(var e) -> convertLitExpr(e);
            case   ExprKind.Path(var e) -> convertPathExpr(e);
            case   ExprKind.AddrOf e -> convertAddrOf(e);
            case   ExprKind.Assign e -> convertAssign(e);
            case   ExprKind.Binary e -> convertBinary(e);
            case   ExprKind.Unary e -> convertUnary(e);
            default -> throw new IllegalArgumentException("Unknown expression: " + expr);
        };
    }

    private BlockExpression convertBlockExpr(ExprKind.BlockExpr expr) {
        var stmts = Arrays.stream(expr.block().stmts()).map(this::convertStmt).toList();
        var value = expr.block().expr() == null ? null : convertExpr(expr.block().expr());
        return new BlockExpression(ImmutableList.fromList(stmts), value);
    }

    private LiteralExpression convertLitExpr(Lit expr) {
        return switch (expr.node()) {
            case LitKind.Bool(var v) -> new BooleanLiteralExpression(v);
            case LitKind.Int(var val, LitIntTy.Unsigned(var uintTy)) -> new IntegerLiteralExpression(new BigInteger(String.valueOf(val)), switch(uintTy){
                case UintTy.U8 -> IntegerLiteralExpression.IntegerSuffix.u8;
                case UintTy.U16 -> IntegerLiteralExpression.IntegerSuffix.u16;
                case UintTy.U32 -> IntegerLiteralExpression.IntegerSuffix.u32;
                case UintTy.U64 -> IntegerLiteralExpression.IntegerSuffix.u64;
                case UintTy.U128 -> IntegerLiteralExpression.IntegerSuffix.u128;
                case UintTy.Usize -> IntegerLiteralExpression.IntegerSuffix.usize;
            });
            case LitKind.Int(var val, LitIntTy.Unsuffixed u) -> new IntegerLiteralExpression(new BigInteger(String.valueOf(val)), null);
            default -> throw new IllegalArgumentException("Unknown lit: " + expr.node());
        };
    }

    private Expr convertPathExpr(QPath path) {
        return null;
    }

    private BorrowExpression convertAddrOf(ExprKind.AddrOf addrOf) {
        return new BorrowExpression(false, addrOf.mut(), convertExpr(addrOf.expr()));
    }

    private AssignmentExpression convertAssign(ExprKind.Assign assign) {
        return new AssignmentExpression(convertExpr(assign.left()), convertExpr(assign.right()));
    }

    private BinaryExpression convertBinary(ExprKind.Binary binary) {
        return new BinaryExpression(convertBinOp(binary.op().node()), convertExpr(binary.left()),
            convertExpr(binary.right()));
    }

    private UnaryExpression convertUnary(ExprKind.Unary unary) {
        return new UnaryExpression(switch (unary.op()) {
        case Deref -> UnaryExpression.Operator.Deref;
        case Not -> UnaryExpression.Operator.Not;
        case Neg -> UnaryExpression.Operator.Neg;
        }, convertExpr(unary.expr()));
    }

    private BinaryExpression.Operator convertBinOp(BinOpKind binOp) {
        return switch (binOp) {
        case Add -> BinaryExpression.Operator.Add;
        case Sub -> BinaryExpression.Operator.Sub;
        case Mul -> BinaryExpression.Operator.Mul;
        case Div -> BinaryExpression.Operator.Div;
        case Rem -> BinaryExpression.Operator.Rem;
        case And -> BinaryExpression.Operator.And;
        case Or -> BinaryExpression.Operator.Or;
        case BitXor -> BinaryExpression.Operator.BitXor;
        case BitAnd -> BinaryExpression.Operator.BitAnd;
        case BitOr -> BinaryExpression.Operator.BitOr;
        case Shl -> BinaryExpression.Operator.Shl;
        case Shr -> BinaryExpression.Operator.Shr;
        case Eq -> BinaryExpression.Operator.Eq;
        case Lt -> BinaryExpression.Operator.Lt;
        case Le -> BinaryExpression.Operator.Le;
        case Ne -> BinaryExpression.Operator.Ne;
        case Ge -> BinaryExpression.Operator.Ge;
        case Gt -> BinaryExpression.Operator.Gt;
        };
    }

    private Statement convertStmt(Stmt stmt) {
        return switch (stmt.kind()) {
            case StmtKind.Let(var let) -> convertLet(let);
            case StmtKind.ItemStmt(var item) -> new ItemStatement(convertItem(item));
            case StmtKind.ExprStmt(var e) -> new ExpressionStatement(convertExpr(e), false);
            case StmtKind.Semi(var e) -> new ExpressionStatement(convertExpr(e), true);
            default -> throw new IllegalArgumentException("Unknown stmt: " + stmt.kind());
        };
    }

    private LetStatement convertLet(LetStmt let) {
        var pat = convertPat(let.pat());
        var ty = let.ty() == null ? null : convertHirTy(let.ty());
        var init = let.init() == null ? null : convertExpr(let.init());
        return new LetStatement(pat, ty, init);
    }

    private RustType convertHirTy(HirTy ty) {
        return switch (ty.kind()){
            case HirTyKind.Path p -> convertPathHirTy(p);
            default -> throw new IllegalArgumentException("Unknown hirty type: " + ty);
        };
    }

    private RustType convertPathHirTy(HirTyKind.Path ty) {
        if (ty.path() instanceof QPath.Resolved r && r.ty() == null && r.path().res() instanceof PrimHirTy pty) {
            var primTy = switch(pty) {
                case PrimHirTy.Bool b -> PrimitiveType.BOOL;
                case PrimHirTy.Uint(var uintTy) -> switch (uintTy) {
                    case UintTy.U8 -> PrimitiveType.U8;
                    case UintTy.U16 -> PrimitiveType.U16;
                    case UintTy.U32 -> PrimitiveType.U32;
                    case UintTy.U64 -> PrimitiveType.U64;
                    case UintTy.U128 -> PrimitiveType.U128;
                    case UintTy.Usize -> PrimitiveType.USIZE;
                };
                default -> throw new IllegalArgumentException("Unknown prim type: " + ty);
            };
            return new PrimitiveRustType(primTy);
        }
        return new PathRustType();
    }

    private Pattern convertPat(Pat pat) {
        return switch (pat.kind()) {
            case PatKind.Binding p -> {
                boolean ref = false;
                boolean mutRef = false;
                if (p.mode().byRef() instanceof ByRef.Yes y) {
                    ref = true;
                    mutRef = y.mut();
                }
                boolean mut = p.mode().mut();
                Pattern opt = p.pat() == null ? null : convertPat(p.pat());
                yield new BindingPattern(ref, mutRef, mut, opt);
            }
            case PatKind.Wild w -> WildCardPattern.WILDCARD;
            case PatKind.Path p -> {
                yield new PathPattern();
            }
            default -> throw new IllegalArgumentException("Unknown pat: " + pat);
        };
    }

    private <R, S> Path<R> convertPath(org.key_project.rusty.parser.hir.Path<S> path,
            java.util.function.Function<S, R> convertR) {
        var res = convertR.apply(path.res());
        var segments = Arrays.stream(path.segments()).map(this::convertPathSegment).toList();
        return new Path<>(res, new ImmutableArray<>(segments));
    }

    private PathSegment convertPathSegment(org.key_project.rusty.parser.hir.PathSegment segment) {
        return new PathSegment(segment.ident().name(), convertRes(segment.res()));
    }

    private Res convertRes(org.key_project.rusty.parser.hir.Res res) {
        return null;
    }
}
