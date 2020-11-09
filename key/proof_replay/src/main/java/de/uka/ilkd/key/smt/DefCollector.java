package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTProofParser.Sorted_varContext;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ParseTree;

import de.uka.ilkd.key.smt.SMTProofParser.NoprooftermContext;

import java.util.*;

import static de.uka.ilkd.key.smt.SMTProofParser.*;

/**
 * This visitor converts a Z3 term into a KeY term, descending into the succedents of Z3 proof rule
 * terms if necessary.
 *
 * @author Wolfram Pfeifer
 */
class DefCollector extends SMTProofBaseVisitor<Term> {
    private final SMTReplayer smtReplayer;
    private final Services services;
    private final TermFactory tf;
    private final TermBuilder tb;
    private final Deque<QuantifiableVariable> boundVars = new LinkedList<>();

    public DefCollector(SMTReplayer smtReplayer, Services services) {
        this.smtReplayer = smtReplayer;
        this.services = services;
        this.tf = services.getTermFactory();
        this.tb = services.getTermBuilder();
    }

    @Override
    public Term visitProofsexpr(ProofsexprContext ctx) {
        if (ctx.rulename != null) {

            // for (proof-bind (lambda ... we make the implicit quantification of free vars explicit
            if (ctx.rulename.getText().equals("proof-bind")) {
                // could be lambda or symbol (bound by let)
                ProofsexprContext next = ctx.proofsexpr(0);
                ParserRuleContext def = smtReplayer.getSymbolDef(next.getText(), next);
                if (def != null) {      // bound by let
                    next = (ProofsexprContext) def;
                }
                // now next must be a lambda term
                if (next.rulename != null && next.rulename.getText().equals("lambda")) {
                    // visit and wrap into (possibly multiple) forall
                    Term result = visit(next.proofsexpr(0));
                    for (int i = next.sorted_var().size() - 1; i >= 0; i--) {
                        // we need to extract the actual type from the typeguard
                        //TODO: search for typeguard
                        String varName = next.sorted_var(i).SYMBOL().getText();
                        if (varName.startsWith("var_")) {
                            varName = varName.substring(4);
                        }
                        QuantifiableVariable qv = new TypeguardSortCollector(services, varName).visit(next);
                        //QuantifiableVariable qv = extractQV(next.sorted_var(i), next);
                        //QuantifiableVariable qv = extractQVSimple(next.sorted_var(i));
                        result = tb.all(qv, result);
                    }
                    return result;
                } else {
                    throw new IllegalStateException("After proof-bind, lambda is expected!");
                }
            }

            // last proofsexpr holds the succedent of the rule application
            ParseTree succedent = ctx.proofsexpr(ctx.proofsexpr().size() - 1);

            ParserRuleContext def = smtReplayer.getSymbolDef(succedent.getText(), ctx);
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

    private QuantifiableVariable extractQVSimple(Sorted_varContext ctx) {
        String varName = ctx.SYMBOL().getText();
        String sortName = ctx.sort().identifier().getText();
        if (varName.startsWith("var_")) {
            varName = varName.substring(4);
        }
        if (sortName.startsWith("sort_")) {
            sortName = sortName.substring(5);
        }
        // TODO: does only work for simple sorts!
        Sort keySort = services.getNamespaces().sorts().lookup(sortName);
        return new LogicVariable(new Name(varName), keySort);
    }

    @Override
    public Term visitNoproofterm(NoprooftermContext ctx) {
        System.out.println("Trying to translate " + ReplayTools.getOriginalText(ctx) + " ...");

        // term may be a new symbol introduced by the let binder
        //ProofsexprContext proofsexpr = smtReplayer.getSymbolDef(ctx.getText());
        /*Namespace<NamedParserRuleContext> ctxNS = smtReplayer.getNamespaces().get(ctx);
        NamedParserRuleContext nprc = ctxNS.lookup(ctx.getText());
        ParserRuleContext proofsexpr = nprc.getCtx();*/

        ParserRuleContext proofsexpr = smtReplayer.getSymbolDef(ctx.getText(), ctx);

        if (proofsexpr != null) {
            // descend into nested let term
            return visit(proofsexpr);
        }

        // term may be in cache already
        Term cached = smtReplayer.getTranslationToTerm(ctx.getText());
        if (cached != null) {
            return cached;
        }

        if (ctx.rulename != null && ctx.rulename.getText().equals("let")) {
            // bindings have already been collected, so directly descend into noproofterm
            return visit(ctx.noproofterm(0));
        }

        // otherwise: translate top level function or quantifier "by hand" and descend into children
        // Note: use TermFactory instead of TermBuilder to prevent from simplification!
        if (ctx.func != null) {
            System.out.println("    ctx.func: " + ctx.func.getText());
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
            //case "implies":
                assert ctx.noproofterm().size() == 3;
                t1 = visit(ctx.noproofterm(1));

                /*
                // could be typeguard (special case):
                if (ctx.noproofterm(1) != null) {
                    if (ctx.noproofterm(1).noproofterm(0) != null) {
                        String leftFunc = ctx.noproofterm(1).noproofterm(0).getText();
                        if (leftFunc.equals("typeguard")) {
                            // skip top level "=>" as well as left subterm (typeguard)
                            return visit(ctx.noproofterm(2));
                        }
                    }
                }
                */

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
                // TODO: in Z3 arity == 1 is permitted!
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
                // TODO: in Z3 arity == 1 is permitted!

                /*
                // could be typeguard (special case):
                if (ctx.noproofterm(1) != null) {
                    if (ctx.noproofterm(1).noproofterm(0) != null) {
                        String leftFunc = ctx.noproofterm(1).noproofterm(0).getText();
                        if (leftFunc.equals("typeguard")) {
                            // skip top level "and" as well as left subterm (typeguard)
                            t1 = visit(ctx.noproofterm(2));
                            for (int i = 3; i <= arity; i++) {
                                t2 = visit(ctx.noproofterm(i));
                                t1 = tf.createTerm(Junctor.AND, t1, t2);
                            }
                            return t1;
                        }
                    }
                }*/

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
            /*
            // marker for instanceof uses w/o direct counterpart in the original sequent
            case "typeguard":
                // TODO: better detect at and/implies or quantifier case?
                t1 = visit(ctx.noproofterm(1));
                // TODO: only int currently
                Function typeguard = services.getNamespaces().functions().lookup("typeguard_int");
                return tb.equals(tb.func(typeguard, t1), tb.TRUE());
                //return tb.tt();*/
            case "length":
                t1 = visit(ctx.noproofterm(1));
                return tb.dotLength(t1);
            case "typeguard":
            case "instanceof":
                return createInstanceof(ctx);
            case "subtype":
                // TODO: does not work!
                t1 = visit(ctx.noproofterm(1));
                t2 = visit(ctx.noproofterm(2));
                return tb.instance(t2.sort(), t1);
            case "typeof":
                // TODO: does not work!
                t1 = visit(ctx.noproofterm(1));
                tb.exactInstance(t1.sort(), t1);
            case "cast":
                t1 = visit(ctx.noproofterm(1));
                return tb.cast(t1.sort(), t1);
            default:
                // what about sorts and variables and other?

                // translate KeY predicates/functions (cut "KeY_" prefix)
                String origFuncName = ctx.func.getText().substring(4);
                Function f = services.getNamespaces().functions().lookup(new Name(origFuncName));

                if (f != null) {
                    int n = f.arity();
                    if (n == ctx.noproofterm().size()) {
                        throw new IllegalStateException(
                            "Arity does not match: " + ctx.func.getText()
                                + " with arity " + ctx.noproofterm().size() + " vs. " + n);
                    }
                    List<Term> children = new ArrayList<>();
                    for (int i = 1; i < ctx.noproofterm().size(); i++) {
                        NoprooftermContext child = ctx.noproofterm(i);
                        children.add(visit(child));
                    }
                    return tb.func(f, children.toArray(new Term[0]));
                }

                // Could still be a skolem function e.g. (var8!0 var7)
                // In this case we use the function name (var8!0 w/o parameters as symbol name)
                // the symbol is a new skolem symbol introduced by an sk rule in a proof leaf
                // Note that we ignore the parameters (we do not visit them) here, since the
                // correct definition is found by the SkolemCollector.
                String skName = ctx.func.getText();
                Term skDef = smtReplayer.getSkolemSymbolDef(skName);
                if (skDef != null) {
                    // found definition of skolem symbol (was already in map)
                    return skDef;
                } else {    // try to find definition of skolem symbol
                    SkolemCollector skColl = new SkolemCollector(smtReplayer, skName, services);
                    // collect all skolem symbols and their definitions using ifEx/eps terms
                    skColl.visit(smtReplayer.getTree());
                    skDef = smtReplayer.getSkolemSymbolDef(ctx.getText());
                    if (skDef != null) {
                        // found definition of skolem symbol
                        return skDef;
                    }
                }

                throw new IllegalStateException("Currently not supported: " + ctx.func.getText());
            }
        } else if (ctx.quant != null) {
            // forall, exists
            if (ctx.quant.getText().equals("forall")) {
                for (int i = ctx.sorted_var().size() - 1; i >= 0; i--) {
                    QuantifiableVariable qv = extractQV(ctx.sorted_var(i), ctx.noproofterm(0));
                    boundVars.push(qv);
                }
                Term t = visit(ctx.noproofterm(0));
                for (int i = ctx.sorted_var().size() - 1; i >= 0; i--) {
                    QuantifiableVariable qv = boundVars.pop();
                    //QuantifiableVariable qv = extractQV(ctx.sorted_var(i), ctx.noproofterm(0));
                    t = tb.all(qv, t);
                }
                return t;
            } else if (ctx.quant.getText().equals("exists")) {
                for (int i = ctx.sorted_var().size() - 1; i >= 0; i--) {
                    QuantifiableVariable qv = extractQV(ctx.sorted_var(i), ctx.noproofterm(0));
                    boundVars.push(qv);
                }
                Term t = visit(ctx.noproofterm(0));
                for (int i = ctx.sorted_var().size() - 1; i >= 0; i--) {
                    QuantifiableVariable qv = boundVars.pop();
                    //QuantifiableVariable qv = extractQV(ctx.sorted_var(i), ctx.noproofterm(0));
                    t = tb.ex(qv, t);
                }
                return t;
            } else {
                throw new IllegalStateException("Unknown quantifier: " + ctx.quant.getText());
            }
        } else if (ctx.EXCL() != null) {
            // skip annotations, directly descend into single child term
            return visit(ctx.noproofterm(0));
        } else {
            //, match, !, spec_const, qual_identifier
            // TODO:
            //throw new IllegalStateException("Currently not supported!");
            return visitChildren(ctx);
        }
    }

    private Term createInstanceof(NoprooftermContext ctx) {
        // instanceof/typeguard has the following form: (instanceof/typeguard var_x sort_int)
        Term term = visit(ctx.noproofterm(1));
        NoprooftermContext sortCtx = ctx.noproofterm(2);
        // cut the "sort_" prefix
        String sortName = sortCtx.getText();
        if (sortName.startsWith("sort_")) {
            sortName = sortName.substring(5);
        }
        Sort keySort = services.getNamespaces().sorts().lookup(sortName);
        return tb.instance(keySort, term);
    }

    private QuantifiableVariable extractQV(Sorted_varContext sortedVar,
                                           ProofsexprContext ctx) {
        NamespaceSet nss = services.getNamespaces();
        String origVarName = sortedVar.SYMBOL().getText();

        // TODO:
        // we search ctx until we found a typeguard for the var with the given name
        //for (ProofsexprContext child : ctx.proofsexpr()) ...
        return null;
    }

    /**
     * Extract the original name of the quantified variable and its sort (from the typeguard).
     *
     * @param sortedVar the context containing the quantified variable with its SMT sort
     * @param quantForm the quantified formula (containing the typeguard)
     * @return a QuantifiableVariable (containing original KeY name and sort)
     */
    private QuantifiableVariable extractQV(Sorted_varContext sortedVar,
                                           NoprooftermContext quantForm)
        throws NotReplayableException {
        NamespaceSet nss = services.getNamespaces();

        // fix: some sorts T/U and variables do not have prefixes
        String origVarName = sortedVar.SYMBOL().getText();
        String varName = origVarName;

        // cut the "var_" prefix
        if (origVarName.startsWith("var_")) {
            varName = origVarName.substring(4);
        }

        // TODO: this does only work with non-compound sorts, not arrays/functions
        String origSortName = sortedVar.sort().identifier().getText();
        /*
        if (origSortName.equals("U")) {
            return new LogicVariable(new Name(varName), Sort.ANY);
        } else if (origSortName.equals("T")) {
            // TODO: ?
            //return new LogicVariable(new Name(origVarName), ???);
            throw new IllegalStateException("Not yet implemented!");
        }*/

        //String varName = origVarName.substring(4);
        Term cached = smtReplayer.getTranslationToTerm(sortedVar.SYMBOL().getText());
        if (cached != null) {
            if (cached.op() instanceof QuantifiableVariable) {
                System.out.println("Found QuantifiableVariable " + cached.op());
                return (QuantifiableVariable) cached.op();
            }
        }

        Name name = new Name(varName);

        NoprooftermContext typeguard = extractTypeguard(quantForm);
        if (typeguard == null) {
            throw new NotReplayableException("Can not be replayed due to unknown sort.");
            //throw new IllegalStateException("No typeguard found!");
        }
        // typeguard has the following form: (typeguard var_x sort_int)
        NoprooftermContext nameCtx = typeguard.noproofterm(1);
        NoprooftermContext sortCtx = typeguard.noproofterm(2);
        // cut the "sort_" prefix
        String sortName = sortCtx.getText();
        if (sortName.startsWith("sort_")) {
            sortName = sortName.substring(5);
        }
        Sort keySort = nss.sorts().lookup(sortName);

        // TODO: SMT quantifiers may have multiple quantified variables

        return new LogicVariable(name, keySort);
    }

    private NoprooftermContext extractTypeguard(NoprooftermContext quantForm) {
        if (quantForm.func != null && quantForm.func.getText().equals("typeguard")) {
            return quantForm;
        } else {
            for (NoprooftermContext child : quantForm.noproofterm()) {
                NoprooftermContext res = extractTypeguard(child);
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

    private QuantifiableVariable getBoundVar(String varName) {
        for (QuantifiableVariable qv : boundVars) {
            if (qv.name().toString().equals(varName)) {
                return qv;
            }
        }
        return null;
    }



    @Override
    public Term visitIdentifier(IdentifierContext ctx) {
        if (ctx.getText().equals("false")) {
            return tb.ff();
        } else if (ctx.getText().equals("true")) {
            return tb.tt();
        }
        QuantifiableVariable qv = getBoundVar(ctx.getText());
        if (qv != null) {
            // return the bound variable
            return tb.var(qv);
        } else {
            // the symbol is a new skolem symbol introduced by an sk rule in a proof leaf
            Term skDef = smtReplayer.getSkolemSymbolDef(ctx.getText());
            if (skDef != null) {
                // found definition of skolem symbol (was already in map)
                return skDef;
            } else {    // try to find definition of skolem symbol
                SkolemCollector skColl = new SkolemCollector(smtReplayer, ctx.getText(), services);
                // collect all skolem symbols and their definitions using ifEx/eps terms
                skColl.visit(smtReplayer.getTree());
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
