package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import org.antlr.v4.runtime.tree.ParseTree;

/**
 * This visitor converts a Z3 term to a KeY term, descending into the succedents of Z3 proof rule terms
 * if necessary.
 */
class DefCollector extends SMTProofBaseVisitor<Term> {
    private final SMTReplayer smtReplayer;
    private final Services services;
    private final TermFactory tf;
    private final TermBuilder tb;

    public DefCollector(SMTReplayer smtReplayer, Services services) {
        this.smtReplayer = smtReplayer;
        this.services = services;
        this.tf = services.getTermFactory();
        this.tb = services.getTermBuilder();
    }

    @Override
    public Term visitProofsexpr(SMTProofParser.ProofsexprContext ctx) {
        if (ctx.rulename != null) {
            // last proofsexpr holds the succedent of the rule application
            assert ctx.proofsexpr() != null && ctx.proofsexpr().size() >= 2;
            ParseTree succedent = ctx.proofsexpr(ctx.proofsexpr().size() - 1);

            SMTProofParser.ProofsexprContext def = smtReplayer.getSymbolDef(succedent.getText());
            if (def != null) {
                // descend further if this still is a symbol bound by let
                return visit(def);
            } else if (smtReplayer.getTranslationToTerm(succedent.getText()) != null) {
                // not a symbol -> should be in KeY translation table
                return smtReplayer.getTranslationToTerm(succedent.getText());
            } else {
                return visit(succedent);
            }
        } else if (ctx.noproofterm() != null) {
            return visit(ctx.noproofterm());
        }
        //return super.visitProofsexpr(ctx);
        throw new IllegalStateException("The subtree is neither a Proofsexpr nor a Noproofterm!");
    }

    @Override
    public Term visitNoproofterm(SMTProofParser.NoprooftermContext ctx) {
        System.out.println("Trying to translate " + SMTReplayer.getOriginalText(ctx) + " ...");

        // term may be a new symbol introduced by the let binder
        SMTProofParser.ProofsexprContext proofsexpr = smtReplayer.getSymbolDef(ctx.getText());
        if (proofsexpr != null) {
            // descend into nested let term
            return visit(proofsexpr);
        }

        // term may be in cache already
        Term cached = smtReplayer.getTranslationToTerm(ctx.getText());
        if (cached != null) {
            return cached;
        }

        // otherwise: translate top level function or quantifier "by hand" and descend into child terms
        // Note: use TermFactory instead of TermBuilder to prevent from simplification!
        if (ctx.func != null) {
            Term t1, t2;
            int arity;
            IntegerLDT integerLDT;
            switch (ctx.func.getText()) {
                case "=":
                case "~":
                    assert ctx.noproofterm().size() == 3;
                    t1 = visit(ctx.noproofterm(1));
                    t2 = visit(ctx.noproofterm(2));
                    return equals(t1, t2);
                case "=>":
                    assert ctx.noproofterm().size() == 3;
                    t1 = visit(ctx.noproofterm(1));
                    t2 = visit(ctx.noproofterm(2));
                    return tf.createTerm(Junctor.IMP, t1, t2);
                case "not":
                    assert ctx.getChildCount() == 4;
                    t1 = visit(ctx.noproofterm(1));
                    return tf.createTerm(Junctor.NOT, t1);
                case "or":
                    // important: or is n-ary in Z3!
                    // subtract 1: "or" token also is noProofTerm
                    arity = ctx.noproofterm().size() - 1;
                    t1 = visit(ctx.noproofterm(1));
                    for (int i = 2; i <= arity; i++) {
                        t2 = visit(ctx.noproofterm(i));
                        t1 = tf.createTerm(Junctor.OR, t1, t2);
                    }
                    return t1;
                case "and":
                    // important: and is n-ary in Z3!
                    // subtract 1: "and" token also is noProofTerm
                    arity = ctx.noproofterm().size() - 1;
                    t1 = visit(ctx.noproofterm(1));
                    for (int i = 2; i <= arity; i++) {
                        t2 = visit(ctx.noproofterm(i));
                        t1 = tf.createTerm(Junctor.AND, t1, t2);
                    }
                    return t1;
                case "<=":
                    t1 = visit(ctx.noproofterm(1));
                    t2 = visit(ctx.noproofterm(2));
                    return tb.leq(t1, t2);
                case ">=":
                    t1 = visit(ctx.noproofterm(1));
                    t2 = visit(ctx.noproofterm(2));
                    return tb.geq(t1, t2);
                case ">":
                    t1 = visit(ctx.noproofterm(1));
                    t2 = visit(ctx.noproofterm(2));
                    return tb.gt(t1, t2);
                case "<":
                    t1 = visit(ctx.noproofterm(1));
                    t2 = visit(ctx.noproofterm(2));
                    return tb.lt(t1, t2);
                case "+":
                    t1 = visit(ctx.noproofterm(1));
                    t2 = visit(ctx.noproofterm(2));
                    integerLDT = services.getTypeConverter().getIntegerLDT();
                    return tb.func(integerLDT.getAdd(), t1, t2);
                case "-":
                    arity = ctx.noproofterm().size() - 1;
                    t1 = visit(ctx.noproofterm(1));
                    integerLDT = services.getTypeConverter().getIntegerLDT();
                    if (arity == 1) {
                        throw new IllegalStateException("Negative term not yet implemented!");
                        //return tb.func(integerLDT.getNegativeNumberSign(), t1);
                    } else if (arity == 2) {
                        t2 = visit(ctx.noproofterm(2));
                        return tb.func(integerLDT.getSub(), t1, t2);
                    } else {
                        throw new IllegalStateException("Minus with invalid arity: " + arity);
                    }
                case "*":
                    t1 = visit(ctx.noproofterm(1));
                    t2 = visit(ctx.noproofterm(2));
                    integerLDT = services.getTypeConverter().getIntegerLDT();
                    return tb.func(integerLDT.getMul(), t1, t2);
                case "/":
                    t1 = visit(ctx.noproofterm(1));
                    t2 = visit(ctx.noproofterm(2));
                    integerLDT = services.getTypeConverter().getIntegerLDT();
                    return tb.func(integerLDT.getDiv(), t1, t2);
                // TODO: currently, u2i/i2u/sort_int are hardcoded into the translation
                //  (see IntegerOpHandler.preamble.xml)
                case "u2i":     // TODO: hack
                case "i2u":
                    // just skip the additional function application
                    // for faster lookup additionally add it to map
                    t1 = visit(ctx.noproofterm(1));
                    smtReplayer.addTranslationToTerm(ctx.getText(), t1);
                    return t1;
                // marker for instanceof uses w/o direct counterpart in the original sequent
                case "typeguard":
                    // TODO: better detect at and/implies or quantifier case?
                    return tb.tt();
                case "length":
                    t1 = visit(ctx.noproofterm(1));
                    return tb.dotLength(t1);
                default:
                    throw new IllegalStateException("Currently not supported: " + ctx.func.getText());
            }
        } else if (ctx.quant != null) {
            // forall, exists
            if (ctx.quant.getText().equals("forall")) {
                Term t = visit(ctx.noproofterm(0));
                for (int i = ctx.sorted_var().size() - 1; i >= 0; i--) {
                    QuantifiableVariable qv = extractQV(ctx.sorted_var(i), ctx.noproofterm(0));
                    t = tb.all(qv, t);
                }
                return t;
            } else if (ctx.quant.getText().equals("exists")) {
                Term t = visit(ctx.noproofterm(0));
                for (int i = ctx.sorted_var().size() - 1; i >= 0; i--) {
                    QuantifiableVariable qv = extractQV(ctx.sorted_var(i), ctx.noproofterm(0));
                    t = tb.ex(qv, t);
                }
                return t;
            } else {
                throw new IllegalStateException("Unknown quantifier: " + ctx.quant.getText());
            }
        } else {
            //, match, !, spec_const, qual_identifier
            // TODO:
            //throw new IllegalStateException("Currently not supported!");
            return visitChildren(ctx);
        }
    }

    /**
     * Extract the original name of the quantified variable and its sort (from the typeguard).
     *
     * @param sortedVar the context containing the quantified variable with its SMT sort
     * @param quantForm the quantified formula (containing the typeguard)
     * @return a QuantifiableVariable (containing original KeY name and sort)
     */
    private QuantifiableVariable extractQV(SMTProofParser.Sorted_varContext sortedVar, SMTProofParser.NoprooftermContext quantForm) {
        NamespaceSet nss = services.getNamespaces();

        // cut the "var_" prefix
        String varName = sortedVar.SYMBOL().getText().substring(4);
        Term cached = smtReplayer.getTranslationToTerm(sortedVar.SYMBOL().getText());
        if (cached != null) {
            if (cached.op() instanceof QuantifiableVariable) {
                System.out.println("Found QuantifiableVariable " + cached.op());
                return (QuantifiableVariable) cached.op();
            }
        }

        Name name = new Name(varName);

        SMTProofParser.NoprooftermContext typeguard = extractTypeguard(quantForm);
        if (typeguard == null) {
            throw new IllegalStateException("No typeguard found!");
        }
        // typeguard has the following form: (typeguard var_x sort_int)
        SMTProofParser.NoprooftermContext nameCtx = typeguard.noproofterm(1);
        SMTProofParser.NoprooftermContext sortCtx = typeguard.noproofterm(2);
        // cut the "sort_" prefix
        String sortName = sortCtx.getText().substring(5);
        Sort keySort = nss.sorts().lookup(sortName);

        // TODO: SMT quantifiers may have multiple quantified variables

        return new LogicVariable(name, keySort);
    }

    private SMTProofParser.NoprooftermContext extractTypeguard(SMTProofParser.NoprooftermContext quantForm) {
        if (quantForm.func != null && quantForm.func.getText().equals("typeguard")) {
            return quantForm;
        } else {
            for (SMTProofParser.NoprooftermContext child : quantForm.noproofterm()) {
                SMTProofParser.NoprooftermContext res = extractTypeguard(child);
                if (res != null) {
                    return res;
                }
            }
            return null;
        }
    }

    // does no boolean simplification as TermBuilder.equals() does,
    // returns <-> or = according to sort of terms
    private Term equals(Term t1, Term t2) {
        if (t1.sort() == Sort.FORMULA) {
            return tf.createTerm(Equality.EQV, t1, t2);
        } else {
            return tf.createTerm(Equality.EQUALS, t1, t2);
        }
    }

    @Override
    public Term visitIdentifier(SMTProofParser.IdentifierContext ctx) {
        if (ctx.getText().equals("false")) {
            return tb.ff();
        } else if (ctx.getText().equals("true")) {
            return tb.tt();
        } else {
            // the symbol is a new skolem symbol introduced by an sk rule in a proof leaf
            Term skDef = smtReplayer.getSkolemSymbolDef(ctx.getText());
            if (skDef != null) {
                // found definition of skolem symbol (was already in map)
                return skDef;
            } else {    // try to find definition of skolem symbol
                SkolemCollector skCollector = new SkolemCollector(smtReplayer, ctx.getText(), services);
                // collect all skolem symbols and their definitions using ifEx/eps terms
                skCollector.visit(smtReplayer.getTree());
                skDef = smtReplayer.getSkolemSymbolDef(ctx.getText());
                if (skDef != null) {
                    // found definition of skolem symbol
                    return skDef;
                }
            }
        }
        throw new IllegalStateException("Unknown identifier: " + ctx.getText());
        //return super.visitIdentifier(ctx);
    }
}
