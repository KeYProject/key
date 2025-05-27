/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.speclang;

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.expr.LoopExpression;
import org.key_project.rusty.ast.fn.Function;
import org.key_project.rusty.logic.RustyDLTheory;
import org.key_project.rusty.logic.TermBuilder;
import org.key_project.rusty.logic.TermFactory;
import org.key_project.rusty.logic.op.Equality;
import org.key_project.rusty.logic.op.Junctor;
import org.key_project.rusty.logic.op.ProgramFunction;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.parser.hir.HirId;
import org.key_project.rusty.parser.hir.QPath;
import org.key_project.rusty.parser.hir.expr.BinOp;
import org.key_project.rusty.parser.hir.expr.BinOpKind;
import org.key_project.rusty.parser.hir.expr.LitKind;
import org.key_project.rusty.parser.hir.expr.UnOp;
import org.key_project.rusty.speclang.spec.LoopSpec;
import org.key_project.rusty.speclang.spec.TermKind;
import org.key_project.rusty.util.MiscTools;
import org.key_project.util.collection.ImmutableList;

public class LoopSpecConverter {
    private final Services services;
    private final TermBuilder tb;
    private final TermFactory tf;

    public LoopSpecConverter(Services services) {
        this.services = services;
        tb = services.getTermBuilder();
        tf = services.getTermFactory();
    }

    public LoopSpecification convert(LoopSpec loopSpec, Function fn, LoopExpression target,
            Map<HirId, ProgramVariable> pvs) {
        var invariant = Arrays.stream(loopSpec.invariants()).map(wp -> convert(wp.value(), pvs))
                .reduce(tb.tt(), (a, b) -> tb.and(a, b));
        var variant = loopSpec.variant() == null ? null : convert(loopSpec.variant().value(), pvs);
        var localIns = tb.var(MiscTools.getLocalIns(target, services));
        var localOuts = tb.var(MiscTools.getLocalOuts(target, services));
        var atPres = createAtPres(ProgramFunction.collectParameters(fn), tb);
        return new LoopSpecImpl(target, invariant, variant, localIns, localOuts, atPres);
    }

    private static Map<ProgramVariable, Term> createAtPres(
            final ImmutableList<ProgramVariable> paramVars, final TermBuilder tb) {
        Map<ProgramVariable, Term> atPres = new LinkedHashMap<>();
        for (var param : paramVars) {
            atPres.put(param,
                tb.var(tb.atPreVar(param.toString(), param.getKeYRustyType(), false)));
        }
        return atPres;
    }

    public Term convert(org.key_project.rusty.speclang.spec.Term term,
            Map<HirId, ProgramVariable> pvs) {
        return switch (term.kind()) {
        case TermKind.Binary(var op, var left, var right) -> {
            var l = convert(left, pvs);
            var r = convert(right, pvs);
            yield convert(op, l, r);
        }
        case TermKind.Unary(var op, var child) -> {
            var c = convert(child, pvs);
            yield convert(op, c);
        }
        case TermKind.Lit(var l) -> switch (l.node()) {
        case LitKind.Bool(var b) -> b ? tb.tt() : tb.ff();
        case LitKind.Int(var i, var ignored) -> tb.zTerm(i);
        default -> throw new IllegalStateException("Unexpected value: " + l.node());
        };
        case TermKind.Path(var p) -> convertPath(p, pvs);
        default -> throw new IllegalStateException("Unexpected value: " + term);
        };
    }

    private Term convertPath(QPath path, Map<HirId, ProgramVariable> pvs) {
        if (path instanceof org.key_project.rusty.parser.hir.QPath.Resolved r
                && r.path().segments().length == 1
                && r.path().res() instanceof org.key_project.rusty.parser.hir.Res.Local lr) {
            var pvo = pvs.get(lr.id());
            if (pvo != null)
                return tb.var(pvo);
        }
        throw new IllegalArgumentException("Unknown path: " + path);
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
                BinOpKind.Shr ->
            throw new RuntimeException("TODO");
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


}
