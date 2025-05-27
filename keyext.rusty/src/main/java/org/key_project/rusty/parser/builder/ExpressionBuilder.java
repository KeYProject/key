/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.builder;


import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.function.Supplier;

import org.key_project.logic.*;
import org.key_project.logic.op.AbstractSortedOperator;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.HirRustyReader;
import org.key_project.rusty.ast.SchemaRustyReader;
import org.key_project.rusty.ldt.LDT;
import org.key_project.rusty.logic.*;
import org.key_project.rusty.logic.op.*;
import org.key_project.rusty.logic.op.sv.ModalOperatorSV;
import org.key_project.rusty.logic.op.sv.OperatorSV;
import org.key_project.rusty.logic.op.sv.ProgramSV;
import org.key_project.rusty.logic.op.sv.VariableSV;
import org.key_project.rusty.parser.KeYRustyLexer;
import org.key_project.rusty.parser.KeYRustyParser;
import org.key_project.rusty.proof.calculus.RustySequentKit;
import org.key_project.rusty.util.parsing.BuildingException;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.StringUtil;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public class ExpressionBuilder extends DefaultBuilder {
    public record BoundVar(Name name, Sort sort) {
    }

    private boolean rustySchemaModeAllowed;
    private List<BoundVariable> boundVars = new ArrayList<>();

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
    public static String operatorOfRustyBlock(String raw) {
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

    public Term visitMutating_update_term(KeYRustyParser.Mutating_update_termContext ctx) {
        Term a = accept(ctx.a);
        Term b = accept(ctx.b);
        if (b != null) {
            return getServices().getTermBuilder().mutating(a, b);
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

    @Override
    public Object visitBracket_term(KeYRustyParser.Bracket_termContext ctx) {
        Term t = accept(ctx.primitive_labeled_term());
        /*
         * for (int i = 0; i < ctx.bracket_suffix_heap().size(); i++) {
         * KeYRustyParser.Brace_suffixContext brace_suffix =
         * ctx.bracket_suffix_heap(i).brace_suffix();
         * ParserRuleContext heap = ctx.bracket_suffix_heap(i).heap;
         * t = accept(brace_suffix, t);
         * if (heap != null) {
         * t = replaceHeap(t, accept(heap), heap);
         * }
         * }
         */
        if (ctx.attribute().isEmpty()) {
            return t;
        }
        throw new RuntimeException("TODO");
        // return handleAttributes(t, ctx.attribute());
    }

    @Override
    public Object visitPrimitive_labeled_term(KeYRustyParser.Primitive_labeled_termContext ctx) {
        return accept(ctx.primitive_term());
        // return updateOrigin(t, ctx, services);
    }

    public <T> T defaultOnException(T defaultValue, Supplier<T> supplier) {
        try {
            return supplier.get();
        } catch (Exception e) {
            return defaultValue;
        }
    }

    private @Nullable Term[] visitArguments(KeYRustyParser.@Nullable Argument_listContext call) {
        List<Term> arguments = accept(call);
        return arguments == null ? null : arguments.toArray(new Term[0]);
    }

    @Override
    public Term visitAccessterm(KeYRustyParser.AccesstermContext ctx) {
        // weigl: I am unsure if this is wise.
        Sort sortId = defaultOnException(null, () -> accept(ctx.sortId()));
        String firstName = accept(ctx.simple_ident());

        ImmutableArray<QuantifiableVariable> boundVars = null;
        Namespace<QuantifiableVariable> orig = null;
        Term[] args = null;
        if (ctx.call() != null) {
            orig = variables();
            List<QuantifiableVariable> bv = accept(ctx.call().boundVars);
            boundVars =
                bv != null ? new ImmutableArray<>(bv.toArray(new QuantifiableVariable[0])) : null;
            args = visitArguments(ctx.call().argument_list());
            if (boundVars != null) {
                unbindVars(orig);
            }
        }

        assert firstName != null;
        Operator op;

        if ("skip".equals(firstName)) {
            op = UpdateJunctor.SKIP;
        } else {
            op = lookupVarfuncId(ctx, firstName,
                ctx.sortId() != null ? ctx.sortId().getText() : null, sortId);
        }

        Term current;
        Operator finalOp = op;
        if (op instanceof ParsableVariable) {
            if (args != null) {
                semanticError(ctx, "You used the variable `%s` like a predicate or function.", op);
            }
            if (boundVars != null) {
                // addWarning(ctx, "Bounded variable are ignored on a variable");
            }
            current = termForParsedVariable((ParsableVariable) op, ctx);
        } else {
            if (boundVars == null) {
                Term[] finalArgs = args;
                current = capsulateTf(ctx, () -> getTermFactory().createTerm(finalOp, finalArgs));
            } else {
                // sanity check
                assert op instanceof Function;
                for (int i = 0; i < args.length; i++) {
                    if (i < op.arity() && !op.bindVarsAt(i)) {
                        for (QuantifiableVariable qv : args[i].freeVars()) {
                            if (boundVars.contains(qv)) {
                                semanticError(ctx,
                                    "Building function term " + op
                                        + " with bound variables failed: " + "Variable " + qv
                                        + " must not occur free in subterm " + args[i]);
                            }
                        }
                    }
                }
                ImmutableArray<QuantifiableVariable> finalBoundVars = boundVars;
                // create term
                Term[] finalArgs1 = args;
                current = capsulateTf(ctx,
                    () -> getTermFactory().createTerm(finalOp, finalArgs1, finalBoundVars));
            }
        }
        return current;
    }

    private Term termForParsedVariable(ParsableVariable v, ParserRuleContext ctx) {
        if (v instanceof LogicVariable lv) {
            return capsulateTf(ctx, () -> getTermFactory().createTerm(lv));
        } else if (v instanceof ProgramVariable lv) {
            return capsulateTf(ctx, () -> getTermFactory().createTerm(lv));
        } else {
            if (v instanceof OperatorSV sv) {
                return capsulateTf(ctx, () -> getTermFactory().createTerm(sv));
            } else {
                String errorMessage = "";
                errorMessage += v + " is not a logic or program variable";
                semanticError(null, errorMessage);
            }
        }
        return null;
    }

    private BoundVariable bindVar(String name, Sort sort) {
        var e = new BoundVariable(new Name(name), sort);
        boundVars.add(e);
        return e;
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
        return RustySequentKit.createSequent(accept(ctx.ant),
            accept(ctx.suc));
    }

    @Override
    public Sequent visitSeqEOF(KeYRustyParser.SeqEOFContext ctx) {
        return accept(ctx.seq());
    }

    @Override
    public Object visitTermorseq(KeYRustyParser.TermorseqContext ctx) {
        Term head = accept(ctx.head);
        Sequent s = accept(ctx.s);
        ImmutableList<SequentFormula> ss = accept(ctx.ss);
        if (head != null && s == null && ss == null) {
            return head;
        }
        if (head != null && ss != null) {
            // A sequent with only head in the antecedent.
            return RustySequentKit
                    .createSequent(ImmutableSLList.singleton(new SequentFormula(head)), ss);
        }
        if (head != null && s != null) {
            // A sequent. Prepend head to the antecedent.
            ImmutableList<SequentFormula> newAnt =
                s.antecedent().insertFirst(new SequentFormula(head)).getFormulaList();
            return RustySequentKit.createSequent(newAnt, s.succedent().asList());
        }
        if (ss != null) {
            return RustySequentKit.createSequent(ImmutableSLList.nil(), ss);
        }
        assert (false);
        return null;
    }

    @Override
    public ImmutableList<SequentFormula> visitSemisequent(KeYRustyParser.SemisequentContext ctx) {
        ImmutableList<SequentFormula> ss = accept(ctx.ss);
        if (ss == null) {
            ss = ImmutableSLList.nil();
        }
        Term head = accept(ctx.term());
        if (head != null) {
            ss = ss.prepend(new SequentFormula(head));
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

    protected void enableRustySchemaMode() {
        rustySchemaModeAllowed = true;
    }

    protected void disableRustySchemaMode() {
        rustySchemaModeAllowed = false;
    }

    private PairOfStringAndRustyBlock getRustyBlock(Token t) {
        PairOfStringAndRustyBlock srb = new PairOfStringAndRustyBlock();
        String s = t.getText().trim();
        String cleanRusty = trimRustyBlock(s);
        srb.opName = operatorOfRustyBlock(s);

        try {
            try {
                if (rustySchemaModeAllowed) {// TEST
                    var rr = new SchemaRustyReader(services, nss);
                    rr.setSVNamespace(schemaVariables());
                    try {
                        srb.rustyBlock =
                            rr.readBlockWithProgramVariables(programVariables(), cleanRusty);
                    } catch (Exception e) {
                        srb.rustyBlock = rr.readBlockWithEmptyContext(cleanRusty);
                    }
                }
            } catch (Exception e) {
                if (cleanRusty.startsWith("{c#") || cleanRusty.contains("s#")) {// do not fallback
                    throw e;
                }
            }

            if (srb.rustyBlock == null) {
                var rr = new HirRustyReader(services, nss);
                try {
                    srb.rustyBlock =
                        rr.readBlockWithProgramVariables(programVariables(), cleanRusty);
                } catch (Exception e1) {
                    srb.rustyBlock = rr.readBlockWithEmptyContext(cleanRusty);
                }
            }
        } catch (Exception e) {
            throw new BuildingException(t, "Could not parse Rust: '" + cleanRusty + "'", e);
        }
        return srb;
    }

    private static class PairOfStringAndRustyBlock {
        String opName;
        RustyBlock rustyBlock;
    }

    @Override
    public Object visitBoolean_literal(KeYRustyParser.Boolean_literalContext ctx) {
        if (ctx.TRUE() != null) {
            return capsulateTf(ctx, () -> getTermFactory().createTerm(Junctor.TRUE));
        } else {
            return capsulateTf(ctx, () -> getTermFactory().createTerm(Junctor.FALSE));
        }
    }

    @Override
    public Term visitIfThenElseTerm(KeYRustyParser.IfThenElseTermContext ctx) {
        Term condF = (Term) ctx.condF.accept(this);
        if (condF.sort() != RustyDLTheory.FORMULA) {
            semanticError(ctx, "Condition of an \\if-then-else term has to be a formula.");
        }
        Term thenT = (Term) ctx.thenT.accept(this);
        Term elseT = (Term) ctx.elseT.accept(this);
        return capsulateTf(ctx,
            () -> getTermFactory().createTerm(IfThenElse.IF_THEN_ELSE, condF, thenT, elseT));
    }

    @Override
    public Object visitIfExThenElseTerm(KeYRustyParser.IfExThenElseTermContext ctx) {
        Namespace<QuantifiableVariable> orig = variables();
        List<QuantifiableVariable> exVars = accept(ctx.bound_variables());
        Term condF = accept(ctx.condF);
        if (condF.sort() != RustyDLTheory.FORMULA) {
            semanticError(ctx, "Condition of an \\ifEx-then-else term has to be a formula.");
        }

        Term thenT = accept(ctx.thenT);
        Term elseT = accept(ctx.elseT);
        ImmutableArray<QuantifiableVariable> exVarsArray = new ImmutableArray<>(exVars);
        Term result = null;/*
                            * getTermFactory().createTerm(IfExThenElse.IF_EX_THEN_ELSE,
                            * new Term[] { condF, thenT, elseT }, exVarsArray, null);
                            * unbindVars(orig);
                            */
        return result;
    }

    @Override
    public Term visitQuantifierterm(KeYRustyParser.QuantifiertermContext ctx) {
        Operator op = null;
        Namespace<QuantifiableVariable> orig = variables();
        if (ctx.FORALL() != null) {
            op = Quantifier.ALL;
        }
        if (ctx.EXISTS() != null) {
            op = Quantifier.EX;
        }
        List<@NonNull BoundVariable> vars = accept(ctx.bound_variables());
        assert vars != null;
        var bound = new ImmutableArray<QuantifiableVariable>(vars);
        Term a1 = accept(ctx.sub);
        Term a = getTermFactory().createTerm(op, new ImmutableArray<>(a1),
            bound);
        unbindVars(orig);
        unbindVars(vars);
        return a;
    }

    @Override
    public Object visitSubstitution_term(KeYRustyParser.Substitution_termContext ctx) {
        SubstOp op = SubstOp.SUBST;
        Namespace<QuantifiableVariable> orig = variables();
        AbstractSortedOperator v = accept(ctx.bv);
        unbindVars(orig);
        if (v instanceof LogicVariable) {
            // bindVar((LogicVariable) v);
            throw new RuntimeException("TODO @ DD");
        } else {
            bindVar();
        }

        Term a1 = accept(ctx.replacement);
        Term a2 = oneOf(ctx.atom_prefix(), ctx.unary_formula());
        try {
            Term result =
                getServices().getTermBuilder().subst(op, (QuantifiableVariable) v, a1, a2);
            return result;
        } catch (Exception e) {
            throw new BuildingException(ctx, e);
        } finally {
            unbindVars(orig);
        }
    }

    @Override
    public Object visitUpdate_term(KeYRustyParser.Update_termContext ctx) {
        Term t = oneOf(ctx.atom_prefix(), ctx.unary_formula());
        if (ctx.u.isEmpty()) {
            return t;
        }
        Term u = accept(ctx.u);
        return getTermFactory().createTerm(UpdateApplication.UPDATE_APPLICATION, u, t);
    }

    public List<@NonNull BoundVar> visitBound_variables(KeYRustyParser.Bound_variablesContext ctx) {
        return mapOf(ctx.one_bound_variable());
    }

    @Override
    public Object visitOne_bound_variable(
            KeYRustyParser.One_bound_variableContext ctx) {
        String id = accept(ctx.simple_ident());
        Sort sort = accept(ctx.sortId());

        assert id != null;
        SchemaVariable ts = schemaVariables().lookup(new Name(id));
        if (ts != null) {
            if (!(ts instanceof VariableSV)) {
                semanticError(ctx,
                    ts + " is not allowed in a quantifier. Note, that you can't "
                        + "use the normal syntax for quantifiers of the form \"\\exists int i;\""
                        + " in taclets. You have to define the variable as a schema variable"
                        + " and use the syntax \"\\exists i;\" instead.");
            }
            bindVar();
            return ts;
        }

        if (sort != null) {
            return bindVar(id, sort);
        }

        QuantifiableVariable result =
            doLookup(new Name(ctx.id.getText()), variables());

        if (result == null) {
            semanticError(ctx, "There is no schema variable or variable named " + id);
        }

        return result;
    }

    @Override
    public Object visitModality_term(KeYRustyParser.Modality_termContext ctx) {
        Term a1 = accept(ctx.sub);
        if (ctx.MODALITY() == null) {
            return a1;
        }

        PairOfStringAndRustyBlock sjb = getRustyBlock(ctx.MODALITY().getSymbol());
        Operator op;
        if (sjb.opName.charAt(0) == '#') {
            /*
             * if (!inSchemaMode()) { semanticError(ctx,
             * "No schema elements allowed outside taclet declarations (" + sjb.opName + ")"); }
             */
            var kind = (Modality.RustyModalityKind) schemaVariables().lookup(new Name(sjb.opName));
            op = Modality.getModality(kind, sjb.rustyBlock);
        } else {
            var kind = Modality.RustyModalityKind.getKind(sjb.opName);
            op = Modality.getModality(kind, sjb.rustyBlock);
        }
        if (op == null) {
            semanticError(ctx, "Unknown modal operator: " + sjb.opName);
        }

        return capsulateTf(ctx,
            () -> getTermFactory().createTerm(op, new Term[] { a1 }, null));
    }

    @Override
    public List<Term> visitArgument_list(KeYRustyParser.Argument_listContext ctx) {
        return mapOf(ctx.term());
    }

    /**
     * Handles "[sort]::a.name.or.something.else"
     *
     * @param ctx
     * @return a Term or an operator, depending on the referenced object.
     */
    @Override
    public Object visitFuncpred_name(KeYRustyParser.Funcpred_nameContext ctx) {
        Sort sortId = accept(ctx.sortId());
        List<String> parts = mapOf(ctx.name.simple_ident());
        String varfuncid = ctx.name.getText();

        if (ctx.INT_LITERAL() != null) {// number
            return toZNotation(ctx.INT_LITERAL().getText(), functions());
        }

        assert parts != null && varfuncid != null;

        if ("skip".equals(varfuncid)) {
            return UpdateJunctor.SKIP;
        }

        Operator op;
        String firstName =
            ctx.name == null ? ctx.INT_LITERAL().getText()
                    : ctx.name.simple_ident(0).getText();
        op = lookupVarfuncId(ctx, firstName,
            ctx.sortId() != null ? ctx.sortId().getText() : null, sortId);
        if (op instanceof ProgramVariable v && ctx.name.simple_ident().size() > 1) {
            List<KeYRustyParser.Simple_identContext> otherParts =
                ctx.name.simple_ident().subList(1, ctx.name.simple_ident().size());
            Term tv = getServices().getTermFactory().createTerm(v);
            String memberName = otherParts.get(0).getText();
            memberName = StringUtil.trim(memberName, "()");
            // Operator attr = getAttributeInPrefixSort(v.sort(), memberName);
            // return createAttributeTerm(tv, attr, ctx);
            throw new RuntimeException("TODO");
        }
        return op;
    }

    @Override
    public Object visitTermParen(KeYRustyParser.TermParenContext ctx) {
        Term base = accept(ctx.term());
        if (ctx.attribute().isEmpty()) {
            return base;
        }
        return null;// handleAttributes(base, ctx.attribute());
    }

    public Term visitMRef_term(KeYRustyParser.MRef_termContext ctx) {
        String borrowed = accept(ctx.simple_ident());
        var pv = services.getNamespaces().programVariables().lookup(borrowed);
        Place place;
        if (pv != null) {
            place = PVPlace.getInstance(pv);
        } else {
            var sv = schemaVariables().lookup(borrowed);
            assert sv != null;
            place = SVPlace.getInstance((ProgramSV) sv);
        }
        return getTermFactory().createTerm(MutRef.getInstance(place, services));
    }

    @Override
    public Object visitInteger(KeYRustyParser.IntegerContext ctx) {
        return toZNotation(ctx.getText());
    }

    private Term toZNotation(String number) {
        return getTermFactory().createTerm(functions().lookup(new Name("Z")), toNum(number));
    }

    private Term toNum(String number) {
        String s = number;
        final boolean negative = (s.charAt(0) == '-');
        if (negative) {
            s = number.substring(1, s.length());
        }
        if (s.startsWith("0x")) {
            try {
                BigInteger bi = new BigInteger(s.substring(2), 16);
                s = bi.toString();
            } catch (NumberFormatException nfe) {
                // Debug.fail("Not a hexadecimal constant (BTW, this should not have happened).");
            }
        }
        Term result = getTermFactory().createTerm(functions().lookup(new Name("#")));

        for (int i = 0; i < s.length(); i++) {
            result = getTermFactory()
                    .createTerm(functions().lookup(new Name(s.substring(i, i + 1))), result);
        }

        if (negative) {
            result = getTermFactory().createTerm(functions().lookup(new Name("neglit")), result);
        }

        return result;
    }

    @Override
    protected Operator lookupVarfuncId(ParserRuleContext ctx, String varfuncName, String sortName,
            Sort sort) {
        // Might be quantified variable
        var idx = -1;
        for (int i = 0; i < boundVars.size(); ++i) {
            if (varfuncName.equals(boundVars.get(i).name().toString())) {
                idx = i;
                break;
            }
        }
        if (idx != -1) {
            var deBruijn = boundVars.size() - idx;
            return new LogicVariable(deBruijn, boundVars.get(idx).sort());
        }

        return super.lookupVarfuncId(ctx, varfuncName, sortName, sort);
    }

    private void unbindVars(List<@NonNull BoundVariable> vars) {
        boundVars.removeAll(vars);
    }

    protected void enableJavaSchemaMode() {
        rustySchemaModeAllowed = true;
    }

    protected void disableJavaSchemaMode() {
        rustySchemaModeAllowed = false;
    }
}
