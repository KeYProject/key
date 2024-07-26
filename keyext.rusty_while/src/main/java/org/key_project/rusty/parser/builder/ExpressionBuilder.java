/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.builder;


import java.math.BigInteger;
import java.util.List;
import java.util.Objects;
import java.util.function.Supplier;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.Term;
import org.key_project.logic.TermCreationException;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyReader;
import org.key_project.rusty.ast.SchemaRustyReader;
import org.key_project.rusty.ldt.LDT;
import org.key_project.rusty.logic.*;
import org.key_project.rusty.logic.op.*;
import org.key_project.rusty.logic.op.sv.ModalOperatorSV;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.parser.KeYRustyLexer;
import org.key_project.rusty.parser.KeYRustyParser;
import org.key_project.rusty.util.parsing.BuildingException;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.StringUtil;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.jspecify.annotations.NonNull;

public class ExpressionBuilder extends DefaultBuilder {
    private boolean rustySchemaModeAllowed;

    public ExpressionBuilder(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    /**
     * Given a raw modality string, this function trims the modality information.
     *
     * @param raw non-null string
     * @return non-null string
     */
    public static String trimRustyBlock(String raw) {
        if (raw.startsWith("\\<")) {
            return StringUtil.trim(raw, "\\<>");
        }
        if (raw.startsWith("\\[")) {
            return StringUtil.trim(raw, "\\[]");
        }
        int end = raw.length() - (raw.endsWith("\\endmodality") ? "\\endmodality".length() : 0);
        int start = 0;
        if (raw.startsWith("\\diamond")) {
            start = "\\diamond".length();
        } else if (raw.startsWith("\\box")) {
            start = "\\box".length();
        } else if (raw.startsWith("\\modality")) {
            start = raw.indexOf('}') + 1;
        }
        return raw.substring(start, end);
    }

    /**
     * Given a raw modality string, this method determines the operator name.
     */
    public static String operatorOfJavaBlock(String raw) {
        if (raw.startsWith("\\<")) {
            return "diamond";
        }
        if (raw.startsWith("\\[")) {
            return "box";
        }
        if (raw.startsWith("\\diamond")) {
            return "diamond";
        }
        if (raw.startsWith("\\box")) {
            return "box";
        }
        if (raw.startsWith("\\modality")) {
            int start = raw.indexOf('{') + 1;
            int end = raw.indexOf('}');
            return raw.substring(start, end);
        }
        return "n/a";
    }

    @Override
    public Term visitParallel_term(KeYRustyParser.Parallel_termContext ctx) {
        List<Term> t = mapOf(ctx.elementary_update_term());
        Term a = t.get(0);
        for (int i = 1; i < t.size(); i++) {
            a = getTermFactory().createTerm(UpdateJunctor.PARALLEL_UPDATE, a, t.get(i));
        }
        return a;
    }

    @Override
    public Term visitTermEOF(KeYRustyParser.TermEOFContext ctx) {
        return accept(ctx.term());
    }

    @Override
    public Term visitElementary_update_term(KeYRustyParser.Elementary_update_termContext ctx) {
        Term a = accept(ctx.a);
        Term b = accept(ctx.b);
        if (b != null) {
            return getServices().getTermBuilder().elementary(a, b);
        }
        return a;
    }

    @Override
    public Term visitEquivalence_term(KeYRustyParser.Equivalence_termContext ctx) {
        Term a = accept(ctx.a);
        if (ctx.b.isEmpty()) {
            return a;
        }

        Term cur = a;
        for (KeYRustyParser.Implication_termContext context : ctx.b) {
            Term b = accept(context);
            cur = binaryTerm(ctx, Equality.EQV, cur, b);

        }
        return cur;
    }

    private Term binaryTerm(ParserRuleContext ctx, Operator operator, Term left, Term right) {
        if (right == null) {
            return left;
        }
        return capsulateTf(ctx,
            () -> getTermFactory().createTerm(operator, left, right));
    }

    @Override
    public Term visitImplication_term(KeYRustyParser.Implication_termContext ctx) {
        Term termL = accept(ctx.a);
        Term termR = accept(ctx.b);
        return binaryTerm(ctx, Junctor.IMP, termL, termR);
    }

    @Override
    public Term visitDisjunction_term(KeYRustyParser.Disjunction_termContext ctx) {
        Term t = accept(ctx.a);
        for (KeYRustyParser.Conjunction_termContext c : ctx.b) {
            t = binaryTerm(ctx, Junctor.OR, t, accept(c));
        }
        return t;
    }

    @Override
    public Term visitConjunction_term(KeYRustyParser.Conjunction_termContext ctx) {
        Term t = accept(ctx.a);
        for (KeYRustyParser.Term60Context c : ctx.b) {
            t = binaryTerm(ctx, Junctor.AND, t, accept(c));
        }
        return t;
    }

    @Override
    public Object visitUnary_minus_term(KeYRustyParser.Unary_minus_termContext ctx) {
        Term result = accept(ctx.sub);
        assert result != null;
        if (ctx.MINUS() != null) {
            Operator Z = functions().lookup("Z");
            if (result.op() == Z) {
                // weigl: rewrite neg(Z(1(#)) to Z(neglit(1(#))
                // This mimics the old KeYRustyParser behaviour. Unknown if necessary.
                final Function neglit = functions().lookup("neglit");
                final Term num = result.sub(0);
                return capsulateTf(ctx,
                    () -> getTermFactory().createTerm(Z, getTermFactory().createTerm(neglit, num)));
            } else if (result.sort() != RustyDLTheory.FORMULA) {
                Sort sort = result.sort();
                if (sort == null) {
                    semanticError(ctx, "No sort for %s", result);
                }
                LDT ldt = services.getLDTs().getLDTFor(sort);
                if (ldt == null) {
                    // falling back to integer ldt (for instance for untyped schema variables)
                    ldt = services.getLDTs().getIntLDT();
                }
                Function op = ldt.getFunctionFor("neg", services);
                if (op == null) {
                    semanticError(ctx, "Could not find function symbol 'neg' for sort '%s'.", sort);
                }
                return capsulateTf(ctx, () -> getTermFactory().createTerm(op, result));
            } else {
                semanticError(ctx, "Formulas cannot be prefixed with '-'");
            }
        }
        return result;
    }

    @Override
    public Term visitNegation_term(KeYRustyParser.Negation_termContext ctx) {
        Term termL = accept(ctx.sub);
        if (ctx.NOT() != null) {
            return capsulateTf(ctx, () -> getTermFactory().createTerm(Junctor.NOT, termL));
        } else {
            return termL;
        }
    }

    @Override
    public Term visitEquality_term(KeYRustyParser.Equality_termContext ctx) {
        Term termL = accept(ctx.a);
        Term termR = accept(ctx.b);
        Term eq = binaryTerm(ctx, Equality.EQUALS, termL, termR);
        if (ctx.NOT_EQUALS() != null) {
            return capsulateTf(ctx, () -> getTermFactory().createTerm(Junctor.NOT, eq));
        }
        return eq;
    }

    @Override
    public Object visitComparison_term(KeYRustyParser.Comparison_termContext ctx) {
        Term termL = accept(ctx.a);
        Term termR = accept(ctx.b);

        if (termR == null) {
            return termL;
        }

        String op_name = "";
        if (ctx.LESS() != null) {
            op_name = "lt";
        }
        if (ctx.LESSEQUAL() != null) {
            op_name = "leq";
        }
        if (ctx.GREATER() != null) {
            op_name = "gt";
        }
        if (ctx.GREATEREQUAL() != null) {
            op_name = "geq";
        }
        return binaryLDTSpecificTerm(ctx, op_name, termL, termR);
    }

    @Override
    public Object visitWeak_arith_term(KeYRustyParser.Weak_arith_termContext ctx) {
        Term termL = Objects.requireNonNull(accept(ctx.a));
        if (ctx.op.isEmpty()) {
            return termL;
        }

        List<Term> terms = mapOf(ctx.b);
        Term last = termL;
        for (int i = 0; i < terms.size(); i++) {
            String opname = "";
            switch (ctx.op.get(i).getType()) {
            case KeYRustyLexer.UTF_INTERSECT -> opname = "intersect";
            case KeYRustyLexer.UTF_SETMINUS -> opname = "setMinus";
            case KeYRustyLexer.UTF_UNION -> opname = "union";
            case KeYRustyLexer.PLUS -> opname = "add";
            case KeYRustyLexer.MINUS -> opname = "sub";
            default -> semanticError(ctx, "Unexpected token: %s", ctx.op.get(i));
            }
            Term cur = terms.get(i);
            last = binaryLDTSpecificTerm(ctx, opname, last, cur);
        }
        return last;
    }

    private Term binaryLDTSpecificTerm(ParserRuleContext ctx, String opname, Term last, Term cur) {
        Sort sort = last.sort();
        if (sort == null) {
            semanticError(ctx, "No sort for %s", last);
        }
        LDT ldt = services.getLDTs().getLDTFor(sort);
        if (ldt == null) {
            // falling back to integer ldt (for instance for untyped schema variables)
            ldt = services.getLDTs().getIntLDT();
        }
        Function op = ldt.getFunctionFor(opname, services);
        if (op == null) {
            semanticError(ctx, "Could not find function symbol '%s' for sort '%s'.", opname, sort);
        }
        return binaryTerm(ctx, op, last, cur);
    }

    @Override
    public Object visitStrong_arith_term_1(KeYRustyParser.Strong_arith_term_1Context ctx) {
        Term termL = accept(ctx.a);
        if (ctx.b.isEmpty()) {
            return termL;
        }
        List<Term> terms = mapOf(ctx.b);
        Term last = termL;
        for (Term cur : terms) {
            last = binaryLDTSpecificTerm(ctx, "mul", last, cur);
        }
        return last;
    }

    // @Override
    // public Object visitEmptyset(KeYRustyParser.EmptysetContext ctx) {
    // var op = services.getLDTs().getLocSetLDT().getEmpty();
    // return updateOrigin(getTermFactory().createTerm(op), ctx, services);
    // }

    protected Term capsulateTf(ParserRuleContext ctx, Supplier<Term> termSupplier) {
        try {
            return termSupplier.get();
        } catch (TermCreationException e) {
            throw new BuildingException(ctx,
                String.format("Could not build term on: %s", ctx.getText()), e);
        }
    }

    @Override
    public Object visitStrong_arith_term_2(KeYRustyParser.Strong_arith_term_2Context ctx) {
        if (ctx.b.isEmpty()) { // fast path
            return accept(ctx.a);
        }

        List<Term> termL = mapOf(ctx.b);
        // List<String> opName = ctx.op.stream().map(it -> it.getType()== KeYLexer.PERCENT ? "mod" :
        // "div").collect(Collectors.toList());

        Term term = accept(ctx.a);
        var sort = term.sort();
        if (sort == null) {
            semanticError(ctx, "No sort for term '%s'", term);
        }

        var ldt = services.getLDTs().getLDTFor(sort);

        if (ldt == null) {
            // falling back to integer ldt (for instance for untyped schema variables)
            ldt = services.getLDTs().getIntLDT();
        }

        assert ctx.op.size() == ctx.b.size();

        for (int i = 0; i < termL.size(); i++) {
            var opName = ctx.op.get(i).getType() == KeYRustyLexer.PERCENT ? "mod" : "div";
            Function op = ldt.getFunctionFor(opName, services);
            if (op == null) {
                semanticError(ctx, "Could not find function symbol '%s' for sort '%s'.", opName,
                    sort);
            }
            term = binaryTerm(ctx, op, term, termL.get(i));
        }
        return term;
    }

    private LogicVariable bindVar(int idx, Sort s) {
        LogicVariable v = new LogicVariable(idx, s);
        namespaces().setVariables(variables().extended(v));
        return v;
    }

    private LogicVariable bindVar(LogicVariable v) {
        namespaces().setVariables(variables().extended(v));
        return v;
    }

    private void bindVar() {
        namespaces().setVariables(new Namespace<>(variables()));
    }

    private Term toZNotation(String literal, Namespace<@NonNull Function> functions) {
        literal = literal.replace("_", "");
        final boolean negative = (literal.charAt(0) == '-');
        if (negative) {
            literal = literal.substring(1);
        }
        int base = 10;

        if (literal.startsWith("0x")) {
            literal = literal.substring(2);
            base = 16;
        }

        if (literal.startsWith("0b")) {
            literal = literal.substring(2);
            base = 8;
        }

        BigInteger bi = new BigInteger(literal, base);
        return toZNotation(bi, functions);
    }

    private Term toZNotation(BigInteger bi, Namespace<@NonNull Function> functions) {
        boolean negative = bi.signum() < 0;
        String s = bi.abs().toString();
        Term result = getTermFactory().createTerm(functions.lookup(new Name("#")));

        for (int i = 0; i < s.length(); i++) {
            result = getTermFactory().createTerm(functions.lookup(new Name(s.substring(i, i + 1))),
                result);
        }

        if (negative) {
            result = getTermFactory().createTerm(functions.lookup(new Name("neglit")), result);
        }
        return getTermFactory().createTerm(functions.lookup(new Name("Z")), result);
    }

    public TermFactory getTermFactory() {
        return getServices().getTermFactory();
    }

    protected ImmutableSet<Modality.RustyModalityKind> opSVHelper(String opName,
            ImmutableSet<Modality.RustyModalityKind> modalityKinds) {
        if (opName.charAt(0) == '#') {
            return lookupOperatorSV(opName, modalityKinds);
        } else {
            Modality.RustyModalityKind m = Modality.RustyModalityKind.getKind(opName);
            if (m == null) {
                semanticError(null, "Unrecognised operator: " + opName);
            }
            modalityKinds = modalityKinds.add(m);
        }
        return modalityKinds;
    }

    @Override
    public Sequent visitSeq(KeYRustyParser.SeqContext ctx) {
        Semisequent ant = accept(ctx.ant);
        Semisequent suc = accept(ctx.suc);
        return Sequent.createSequent(ant, suc);
    }

    @Override
    public Sequent visitSeqEOF(KeYRustyParser.SeqEOFContext ctx) {
        return accept(ctx.seq());
    }

    @Override
    public Object visitTermorseq(KeYRustyParser.TermorseqContext ctx) {
        Term head = accept(ctx.head);
        Sequent s = accept(ctx.s);
        Semisequent ss = accept(ctx.ss);
        if (head != null && s == null && ss == null) {
            return head;
        }
        if (head != null && ss != null) {
            // A sequent with only head in the antecedent.
            Semisequent ant = Semisequent.EMPTY_SEMISEQUENT;
            ant = ant.insertFirst(new SequentFormula(head)).semisequent();
            return Sequent.createSequent(ant, ss);
        }
        if (head != null && s != null) {
            // A sequent. Prepend head to the antecedent.
            Semisequent newAnt = s.antecedent();
            newAnt = newAnt.insertFirst(new SequentFormula(head)).semisequent();
            return Sequent.createSequent(newAnt, s.succedent());
        }
        if (ss != null) {
            return Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT, ss);
        }
        assert (false);
        return null;
    }

    @Override
    public Semisequent visitSemisequent(KeYRustyParser.SemisequentContext ctx) {
        Semisequent ss = accept(ctx.ss);
        if (ss == null) {
            ss = Semisequent.EMPTY_SEMISEQUENT;
        }
        Term head = accept(ctx.term());
        if (head != null) {
            ss = ss.insertFirst(new SequentFormula(head)).semisequent();
        }
        return ss;
    }

    private ImmutableSet<Modality.RustyModalityKind> lookupOperatorSV(String opName,
            ImmutableSet<Modality.RustyModalityKind> modalityKinds) {
        SchemaVariable sv = schemaVariables().lookup(new Name(opName));
        if (sv instanceof ModalOperatorSV osv) {
            modalityKinds = modalityKinds.union(osv.getModalities());
        } else {
            semanticError(null, "Schema variable " + opName + " not defined.");
        }
        return modalityKinds;
    }

    protected void enableJavaSchemaMode() {
        rustySchemaModeAllowed = true;
    }

    protected void disableJavaSchemaMode() {
        rustySchemaModeAllowed = false;
    }

    private PairOfStringAndRustyBlock getRustyBlock(Token t) {
        PairOfStringAndRustyBlock sjb = new PairOfStringAndRustyBlock();
        String s = t.getText().trim();
        String cleanJava = trimRustyBlock(s);
        sjb.opName = operatorOfJavaBlock(s);

        try {
            try {
                if (rustySchemaModeAllowed) {// TEST
                    SchemaRustyReader jr = new SchemaRustyReader(services, nss);
                    jr.setSVNamespace(schemaVariables());
                    try {
                        sjb.rustyBlock =
                            jr.readBlockWithProgramVariables(programVariables(), cleanJava);
                    } catch (Exception e) {
                        sjb.rustyBlock = jr.readBlockWithEmptyContext(cleanJava);
                    }
                }
            } catch (Exception e) {
                if (cleanJava.startsWith("{..")) {// do not fallback
                    throw e;
                }
            }

            if (sjb.rustyBlock == null) {
                RustyReader jr = new RustyReader(services, nss);
                try {
                    sjb.rustyBlock =
                        jr.readBlockWithProgramVariables(programVariables(), cleanJava);
                } catch (Exception e1) {
                    sjb.rustyBlock = jr.readBlockWithEmptyContext(cleanJava);
                }
            }
        } catch (Exception e) {
            throw new BuildingException(t, "Could not parse java: '" + cleanJava + "'", e);
        }
        return sjb;
    }

    private static class PairOfStringAndRustyBlock {
        String opName;
        RustyBlock rustyBlock;
    }
}
