/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.speclang;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.fn.FunctionParamPattern;
import org.key_project.rusty.ast.pat.BindingPattern;
import org.key_project.rusty.logic.RustyDLTheory;
import org.key_project.rusty.logic.TermBuilder;
import org.key_project.rusty.logic.TermFactory;
import org.key_project.rusty.logic.op.*;
import org.key_project.rusty.parser.hir.HirId;
import org.key_project.rusty.parser.hir.QPath;
import org.key_project.rusty.parser.hir.expr.BinOp;
import org.key_project.rusty.parser.hir.expr.BinOpKind;
import org.key_project.rusty.parser.hir.expr.LitKind;
import org.key_project.rusty.parser.hir.expr.UnOp;
import org.key_project.rusty.parser.hir.item.Param;
import org.key_project.rusty.parser.hir.pat.PatKind;
import org.key_project.rusty.speclang.spec.FnSpec;
import org.key_project.rusty.speclang.spec.SpecCase;
import org.key_project.rusty.speclang.spec.TermKind;
import org.key_project.rusty.speclang.spec.WithParams;
import org.key_project.util.collection.ImmutableList;

public class SpecConverter {
    private final Services services;
    private final TermBuilder tb;
    private final TermFactory tf;

    public SpecConverter(Services services) {
        this.services = services;
        this.tb = services.getTermBuilder();
        this.tf = services.getTermFactory();
    }

    public List<FunctionalOperationContract> convert(FnSpec fnSpec, ProgramFunction target) {
        return Arrays.stream(fnSpec.cases()).flatMap(c -> convert(c, target)).toList();
    }

    public Stream<FunctionalOperationContract> convert(SpecCase specCase, ProgramFunction target) {
        final var kind = specCase.kind();
        final var name = specCase.name();
        final var result = new ProgramVariable(new Name("result"), target.getType());
        var pre = mapAndJoinTerms(specCase.pre(), target, result);
        var post = mapAndJoinTerms(specCase.post(), target, result);
        var variant = specCase.variant() == null ? null
                : convert(specCase.variant().value(),
                params2PVs(specCase.variant().params(), target, result), target);
        var diverges = convert(specCase.diverges().value(),
                params2PVs(specCase.diverges().params(), target, result), target);
        var paramVars = ImmutableList.fromList(target.getFunction().params().stream().map(p -> {
            var fp = (FunctionParamPattern) p;
            var bp = (BindingPattern) fp.pattern();
            return bp.pv();
        }).toList());
        if (diverges == tb.ff()) {
            return Stream.of(new FunctionalOperationContractImpl(name, name, target,
                    Modality.RustyModalityKind.DIA, pre, variant, post, null, paramVars, result,
                    null, 0, true, services));
        }
        if (diverges == tb.tt()) {
            return Stream.of(new FunctionalOperationContractImpl(name, name, target,
                    Modality.RustyModalityKind.BOX, pre, variant, post, null, paramVars, result,
                    null, 0, true, services));
        }
        // TODO
        return null;
    }

    private Term mapAndJoinTerms(WithParams<org.key_project.rusty.speclang.spec.Term>[] terms,
                                 ProgramFunction target, ProgramVariable resultVar) {
        return Arrays.stream(terms)
                .map(wp -> convert(wp.value(), params2PVs(wp.params(), target, resultVar), target))
                .reduce(tb.tt(), (a, b) -> tb.and(a, b));
    }

    private Map<HirId, ProgramVariable> params2PVs(Param[] params, ProgramFunction target, ProgramVariable resultVar) {
        // TODO: Get same PVs as in target or create new ones? Ask RB!
        var map = new HashMap<HirId, ProgramVariable>();
        for (int i = 0; i < params.length; i++) {
            var param = params[i];
            if (param.pat().kind() instanceof PatKind.Binding bp) {
                if (i == target.getNumParams()) {
                    map.put(bp.hirId(), resultVar);
                } else {
                    map.put(bp.hirId(),
                            new ProgramVariable(new Name(bp.ident().name()), target.getParamType(i)));
                }
            }
        }
        return map;
    }

    public Term convert(org.key_project.rusty.speclang.spec.Term term, Map<HirId, ProgramVariable> pvMap, ProgramFunction target) {
        return switch (term.kind()) {
            case TermKind.Binary(var op, var left, var right) -> {
                var l = convert(left, pvMap, target);
                var r = convert(right, pvMap, target);
                yield convert(op, l, r);
            }
            case TermKind.Unary(var op, var child) -> {
                var c = convert(child, pvMap, target);
                yield convert(op, c);
            }
            case TermKind.Lit(var l) -> switch (l.node()) {
                case LitKind.Bool(var b) -> b ? tb.tt() : tb.ff();
                case LitKind.Int(var i, var ignored) -> tb.zTerm(i);
                default -> throw new IllegalStateException("Unexpected value: " + l.node());
            };
            case TermKind.Path(var p) -> convertPath(p, pvMap, target);
            default -> throw new IllegalStateException("Unexpected value: " + term);
        };
    }

    public Term convert(BinOp op, Term left, Term right) {
        // TODO: make this "proper"
        var intLDT = services.getLDTs().getIntLDT();
        var o = switch (op.node()) {
            case BinOpKind.Add -> intLDT.getAdd();
            case BinOpKind.Sub -> intLDT.getSub();
            case BinOpKind.Mul -> intLDT.getMul();
            case BinOpKind.Div -> intLDT.getDiv();
            case BinOpKind.And -> Junctor.AND;
            case BinOpKind.Or -> Junctor.OR;
            case BinOpKind.Lt -> intLDT.getLessThan();
            case BinOpKind.Le -> intLDT.getLessOrEquals();
            case BinOpKind.Gt -> intLDT.getGreaterThan();
            case BinOpKind.Ge -> intLDT.getGreaterOrEquals();
            case BinOpKind.Eq -> left.sort() == RustyDLTheory.FORMULA ? Equality.EQV : Equality.EQUALS;
            case BinOpKind.BitXor, BinOpKind.BitAnd, BinOpKind.BitOr, BinOpKind.Shl, BinOpKind.Rem,
                 BinOpKind.Shr -> throw new RuntimeException("TODO");
            case BinOpKind.Ne -> Junctor.NOT;
        };
        if (o == Junctor.NOT) {
            return tb.not(tb.equals(left, right));
        }
        return tf.createTerm(o, left, right);
    }

    public Term convert(UnOp op, Term child) {
        var intLDT = services.getLDTs().getIntLDT();
        var boolLDT = services.getLDTs().getBoolLDT();
        return switch (op) {
            case Deref -> throw new RuntimeException("TODO");
            case Not -> child.sort() == RustyDLTheory.FORMULA ? tb.not(child)
                    : tb.equals(child, boolLDT.getFalseTerm());
            case Neg -> tf.createTerm(intLDT.getNeg(), child);
        };
    }

    public Term convertPath(QPath path, Map<HirId, ProgramVariable> pvMap, ProgramFunction target) {
        if (path instanceof org.key_project.rusty.parser.hir.QPath.Resolved r
                && r.path().segments().length == 1
                && r.path().res() instanceof org.key_project.rusty.parser.hir.Res.Local lr) {
            var pvo = pvMap.get(lr.id());
            if (pvo != null)
                return tb.var(pvo);
        }
        throw new IllegalArgumentException("Unknown path: " + path);
    }
}
