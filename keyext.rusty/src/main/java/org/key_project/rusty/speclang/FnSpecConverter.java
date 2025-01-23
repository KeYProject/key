/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.speclang;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Stream;

import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.RustyDLTheory;
import org.key_project.rusty.logic.TermBuilder;
import org.key_project.rusty.logic.TermFactory;
import org.key_project.rusty.logic.op.*;
import org.key_project.rusty.parser.hir.expr.BinOp;
import org.key_project.rusty.parser.hir.expr.BinOpKind;
import org.key_project.rusty.parser.hir.expr.LitKind;
import org.key_project.rusty.parser.hir.expr.UnOp;
import org.key_project.rusty.speclang.spec.FnSpec;
import org.key_project.rusty.speclang.spec.SpecCase;
import org.key_project.rusty.speclang.spec.TermKind;
import org.key_project.util.collection.ImmutableSLList;

public class FnSpecConverter {
    private final Services services;
    private final TermBuilder tb;
    private final TermFactory tf;

    public FnSpecConverter(Services services) {
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
        var pre = mapAndJoinTerms(specCase.pre());
        var post = mapAndJoinTerms(specCase.post());
        var variant = specCase.variant() == null ? null : convert(specCase.variant());
        var diverges = convert(specCase.diverges());
        var paramVars = ImmutableSLList.<ProgramVariable>nil();
        ProgramVariable resultVar = null;
        if (diverges == tb.ff()) {
            return Stream.of(new FunctionalOperationContractImpl(name, name, null,
                Modality.RustyModalityKind.DIA, pre, variant, post, null, paramVars, resultVar,
                null, 0, true, services));
        }
        if (diverges == tb.tt()) {
            return Stream.of(new FunctionalOperationContractImpl(name, name, null,
                Modality.RustyModalityKind.BOX, pre, variant, post, null, paramVars, resultVar,
                null, 0, true, services));
        }
        // TODO
        return null;
    }

    private Term mapAndJoinTerms(org.key_project.rusty.speclang.spec.Term[] terms) {
        return Arrays.stream(terms).map(this::convert).reduce(tb.tt(), (a, b) -> tb.and(a, b));
    }

    public Term convert(org.key_project.rusty.speclang.spec.Term term) {
        return switch (term.kind()){
            case TermKind.Binary(var op, var left, var right) -> {
                var l = convert(left);
                var r = convert(right);
                yield convert(op, l, r);
            }
            case TermKind.Unary(var op, var child) -> {
                var c = convert(child);
                yield convert(op, c);
            }
            case TermKind.Lit(var l) -> switch (l.node()) {
                case LitKind.Bool(var b) -> b ? tb.tt() : tb.ff();
                case LitKind.Int(var i, var ignored) -> tb.zTerm(i);
                default -> throw new IllegalStateException("Unexpected value: " + l.node());
            };
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
