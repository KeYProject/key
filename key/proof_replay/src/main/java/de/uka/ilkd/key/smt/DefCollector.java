package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.smt.SMTProofParser.Sorted_varContext;
import de.uka.ilkd.key.util.Pair;
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
public class DefCollector extends SMTProofBaseVisitor<Term> {
    private final SMTReplayer smtReplayer;
    private final Services services;
    private final TermFactory tf;
    private final TermBuilder tb;
    private final SMTSymbolRetranslator retranslator;

    /** used to carry variables bound by a quantifier into nested contexts */
    private final Deque<QuantifiableVariable> boundVars;

    /** "free" variables, i.e. variables bound by lambda, but no quantifier, are carried here.
     * When leaving the scope of the lambda, these variables must be replaced by there counterpart,
     * i.e. the "real" variable bound by a quantifier. This ensures that skolemization can be done
     * correctly. */
    private final Deque<Pair<QuantifiableVariable, Term>> skolemSymbols;

    public DefCollector(SMTReplayer smtReplayer, Services services) {
        // no symbols bound by proof-bind/lambda -> empty stack
        this(smtReplayer, services, new LinkedList<>(), new LinkedList<>());
    }

    public DefCollector(SMTReplayer smtReplayer, Deque<QuantifiableVariable> boundVars,
                        Services services) {
        this(smtReplayer, services, new LinkedList<>(), boundVars);
    }

    public DefCollector(SMTReplayer smtReplayer, Services services,
                        Deque<Pair<QuantifiableVariable, Term>> skolemSymbols) {
        this(smtReplayer, services, skolemSymbols, new LinkedList<>());

    }
    public DefCollector(SMTReplayer smtReplayer, Services services,
                        Deque<Pair<QuantifiableVariable, Term>> skolemSymbols,
                        Deque<QuantifiableVariable> boundVars) {
        this.smtReplayer = smtReplayer;
        this.services = services;
        this.tf = services.getTermFactory();
        this.tb = services.getTermBuilder();
        retranslator = new SMTSymbolRetranslator(services);
        // contains the current context, i.e. variables bound by lambda in the context that is to be
        // visited
        this.skolemSymbols = skolemSymbols;
        this.boundVars = boundVars;
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
                    System.out.println(next.getText() + " (shared noproofterm)");
                    next = (ProofsexprContext) def;
                }
                // now next must be a lambda term
                if (next.rulename != null && next.rulename.getText().equals("lambda")) {
                    for (int i = 0; i < next.sorted_var().size(); i++) {
                        // we need to extract the actual type from the typeguard
                        String varName = next.sorted_var(i).SYMBOL().getText();
                        String fallbackSortName = next.sorted_var(i).sort().getText();

                        Sort sort = ReplayTools.extractSort(services, retranslator, varName, next,
                            fallbackSortName);

                        QuantifiableVariable qv =
                            retranslator.translateOrCreateLogicVariable(varName, sort);
                        boundVars.push(qv);
                    }

                    // visit and wrap into (possibly multiple) forall
                    Term result = visit(next.proofsexpr(0));
                    for (int i = 0; i < next.sorted_var().size(); i++) {
                        QuantifiableVariable qv = boundVars.pop();
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
                System.out.println(succedent.getText() + " (shared noproofterm)");
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
        // term may be a new symbol introduced by the let binder
        //ProofsexprContext proofsexpr = smtReplayer.getSymbolDef(ctx.getText());
        /*Namespace<NamedParserRuleContext> ctxNS = smtReplayer.getNamespaces().get(ctx);
        NamedParserRuleContext nprc = ctxNS.lookup(ctx.getText());
        ParserRuleContext proofsexpr = nprc.getCtx();*/

        ParserRuleContext proofsexpr = smtReplayer.getSymbolDef(ctx.getText(), ctx);

        if (proofsexpr != null) {
            // descend into nested let term
            System.out.println(ctx.getText() + " (shared noproofterm)");
            return visit(proofsexpr);
        }

        // TODO: caching while ignoring bound vars leads to replacing bound vars by skolem constants
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
            Term t1;
            Term t2;
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
            case "implies":
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
                    return tb.func(integerLDT.getNeg(), t1);
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
            case "div":
                t1 = visit(ctx.noproofterm(1));
                t2 = visit(ctx.noproofterm(2));
                integerLDT = services.getTypeConverter().getIntegerLDT();
                return tb.func(integerLDT.getDiv(), t1, t2);
            case "mod":
                t1 = visit(ctx.noproofterm(1));
                t2 = visit(ctx.noproofterm(2));
                integerLDT = services.getTypeConverter().getIntegerLDT();
                return tb.func(integerLDT.getMod(), t1, t2);
            case "u2i":     // this is effectively a cast to int
                t1 = visit(ctx.noproofterm(1));
                Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();
                return tb.cast(intSort, t1);
            case "u2b":     // this is effectively a cast to boolean
                return visit(ctx.noproofterm(1));
                /*
                t1 = visit(ctx.noproofterm(1));
                Sort booleanSort = services.getTypeConverter().getBooleanLDT().targetSort();
                return tb.cast(booleanSort, t1);*/
            case "i2u":     // this is effectively a cast to any
                t1 = visit(ctx.noproofterm(1));
                return tb.cast(Sort.ANY, t1);
            case "b2u":
                return visit(ctx.noproofterm(1));
            case "length":
                t1 = visit(ctx.noproofterm(1));
                return tb.dotLength(t1);
            case "typeguard":
            case "instanceof":
                return createInstanceof(ctx);
            case "exactinstanceof":
                return createExactinstanceof(ctx);
            case "cast":
                return createCast(ctx);
            default:

                // translate KeY predicates/functions (cut "u_" prefix)
                String origFuncName = ctx.func.getText().substring(2);
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
                    skColl.visit(smtReplayer.getProofStart());
                    skDef = skColl.getRawTerm();
                    //skDef = smtReplayer.getSkolemSymbolDef(ctx.getText());
                    //skDef = smtReplayer.getSkolemSymbolDef(skName);
                    if (skDef != null) {
                        // found definition of skolem function:
                        // collected term may contain free variables -> replace with bound ones
                        // from current ctx
                        List<NoprooftermContext> params = skColl.getParams();

                        assert params.size() == ctx.noproofterm().size() - 1;

                        for (int i = 1; i < ctx.noproofterm().size(); i++) {
                            // should all be bound variables
                            Term p = visitNoproofterm(ctx.noproofterm(i));

                            String freeVarName = params.get(i - 1).getText();
                            // cut "var_" prefix
                            String origFreeVarName = freeVarName.substring(4);
                            Term toReplace = findQVSubterm(skDef, origFreeVarName);
                            skDef = OpReplacer.replace(toReplace, p, skDef, tf);
                        }

                        return skDef;
                    }
                }

                throw new IllegalStateException("Currently not supported: " + ctx.func.getText());
            }
        } else if (ctx.quant != null) {
            // forall, exists
            if (ctx.quant.getText().equals("forall")) {
                for (int i = 0; i < ctx.sorted_var().size(); i++) {
                    QuantifiableVariable qv = extractQV(ctx.sorted_var(i), ctx.noproofterm(0));
                    boundVars.push(qv);
                }
                Term t = visit(ctx.noproofterm(0));
                for (int i = 0; i < ctx.sorted_var().size(); i++) {
                    QuantifiableVariable qv = boundVars.pop();
                    t = tb.all(qv, t);
                }
                return t;
            } else if (ctx.quant.getText().equals("exists")) {
                for (int i = 0; i < ctx.sorted_var().size(); i++) {
                    QuantifiableVariable qv = extractQV(ctx.sorted_var(i), ctx.noproofterm(0));
                    boundVars.push(qv);
                }
                Term t = visit(ctx.noproofterm(0));
                for (int i = 0; i < ctx.sorted_var().size(); i++) {
                    QuantifiableVariable qv = boundVars.pop();
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

    private static Term findQVSubterm(Term term, String varName) {
        if (term.op() instanceof QuantifiableVariable) {
            if (term.op().name().toString().equals(varName)) {
                return term;
            }
        }
        for (Term s : term.subs()) {
            Term found = findQVSubterm(s, varName);
            if (found != null) {
                return found;
            }
        }
        return null;
    }

    private Term createCast(NoprooftermContext ctx) {
        // cast has the following form: (cast var_x sort_int)
        Term term = visit(ctx.noproofterm(1));
        NoprooftermContext sortCtx = ctx.noproofterm(2);
        Sort keySort = retranslator.translateSort(sortCtx.getText());
        return tb.cast(keySort, term);
    }

    private Term createInstanceof(NoprooftermContext ctx) {
        // instanceof/typeguard has the following form: (instanceof/typeguard var_x sort_int)
        Term term = visit(ctx.noproofterm(1));
        NoprooftermContext sortCtx = ctx.noproofterm(2);
        Sort keySort = retranslator.translateSort(sortCtx.getText());
        return tb.instance(keySort, term);
    }

    private Term createExactinstanceof(NoprooftermContext ctx) {
        // instanceof/typeguard has the following form: (instanceof/typeguard var_x sort_int)
        Term term = visit(ctx.noproofterm(1));
        NoprooftermContext sortCtx = ctx.noproofterm(2);
        Sort keySort = retranslator.translateSort(sortCtx.getText());
        return tb.exactInstance(keySort, term);
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
        //NamespaceSet nss = services.getNamespaces();

        // fix: some sorts T/U and variables do not have prefixes
        String origVarName = sortedVar.SYMBOL().getText();
        //String varName = origVarName;

        /*
        // cut the "var_" prefix
        if (origVarName.startsWith("var_")) {
            varName = origVarName.substring(4);
        }*/

        Term cached = smtReplayer.getTranslationToTerm(origVarName);
        if (cached != null) {
            if (cached.op() instanceof QuantifiableVariable) {
                return (QuantifiableVariable) cached.op();
            }
        }

        //Name name = new Name(varName);

        NoprooftermContext typeguard = extractTypeguard(quantForm);
        if (typeguard == null) {
            // this is not always Any here! For int, the translation is done to Int
            Sort sort = retranslator.translateSort(sortedVar.sort().getText());
            return retranslator.translateOrCreateLogicVariable(origVarName, sort);
        }
        // typeguard has the following form: (typeguard var_x sort_int)
        NoprooftermContext nameCtx = typeguard.noproofterm(1);
        NoprooftermContext sortCtx = typeguard.noproofterm(2);
        Sort keySort = retranslator.translateSort(sortCtx.getText());

        // TODO: SMT quantifiers may have multiple quantified variables
        return retranslator.translateOrCreateLogicVariable(origVarName, keySort);
        //return new LogicVariable(name, keySort);
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
        if (t1.sort() == Sort.FORMULA && t2.sort() == Sort.FORMULA) {
            return tf.createTerm(Equality.EQV, t1, t2);
        } else if (t1.sort() == Sort.FORMULA) {
            // only t1 is of Formula sort
            Term t2Form = tf.createTerm(Equality.EQUALS, t2, tb.TRUE());
            return tf.createTerm(Equality.EQV, t1, t2Form);
        } else if (t2.sort() == Sort.FORMULA) {
            // only t2 is of Formula sort
            Term t1Form = tf.createTerm(Equality.EQUALS, t1, tb.TRUE());
            return tf.createTerm(Equality.EQV, t1Form, t2);
        } else {
            // both are not of Formula sort
            return tf.createTerm(Equality.EQUALS, t1, t2);
        }
    }

    private QuantifiableVariable getBoundVar(String varName) {
        for (QuantifiableVariable qv : boundVars) {
            // sometimes bound vars have not "var_" prefix
            if (qv.name().toString().equals(varName)) {
                return qv;
            // maybe varName still has "var_" prefix
            } else if (varName.length() > 4
                && qv.name().toString().equals(varName.substring(4))) {
                return qv;
            }
        }
        return null;
    }

    private Term findBoundVar(String varName) {
        for (Pair<QuantifiableVariable, Term> p : skolemSymbols) {
            String skName = p.first.name().toString();
            if (skName.equals(varName)) {
                return p.second;
            } else if (skName.startsWith("var_") && skName.substring(4).equals(varName)) {
                return p.second;
            } else if (varName.startsWith("var_") && skName.equals(varName.substring(4))) {
                return p.second;
            }
        }
        return null;
    }

    @Override
    public Term visitSpec_constant(Spec_constantContext ctx) {
        if (ctx.NUM() != null) {
            String num = ctx.NUM().getText();
            return tb.zTerm(num);
        }
        throw new IllegalStateException("Translation of constant " + ctx.getText()
            + " not yet implemented!");
    }

    @Override
    public Term visitIdentifier(IdentifierContext ctx) {
        // possible cases:
        // - symbol that can be handled by retranslator (e.g. k_null)
        // - special symbols (currently only: false, true)
        // - lambda bound variable
        // - bound variable (can be found on stack of bound variables)
        // - skolem constant

        Term t = retranslator.tryToTranslate(ctx.getText());
        if (t != null) {
            return t;
        }

        // special symbols that are not handled by the retranslator (translation to SMT is done in
        // BooleanConnectiveHandler)
        if (ctx.getText().equals("false")) {
            return tb.ff();
        } else if (ctx.getText().equals("true")) {
            return tb.tt();
        } else if (ctx.getText().equals("FALSE")) {
            return tb.FALSE();
        } else if (ctx.getText().equals("TRUE")) {
            return tb.TRUE();
        }

        // TODO: this could probably be unified with bound variables list
        // could be a variable bound by proof-bind/lamba
        Term lambdaBoundVar = findBoundVar(ctx.getText());
        if (lambdaBoundVar != null) {
            return lambdaBoundVar;
        }

        // could be a bound variable
        QuantifiableVariable qv = getBoundVar(ctx.getText());
        if (qv != null) {
            // return the bound variable
            return tb.var(qv);
        }

        // if it is not found until now, the symbol could be a currently unknown skolem symbol
        // introduced by an sk rule in a proof leaf
        Term skDef = smtReplayer.getSkolemSymbolDef(ctx.getText());
        if (skDef != null) {
            // found definition of skolem symbol (was already in map)
            return skDef;
        } else {    // try to find definition of skolem symbol  -> skolem constant here!
            SkolemCollector skColl = new SkolemCollector(smtReplayer, ctx.getText(), services);
            // collect all skolem symbols and their definitions using ifEx/eps terms
            //skColl.visit(smtReplayer.getTree());
            skColl.visit(smtReplayer.getProofStart());
            skDef = skColl.getRawTerm();
            //skDef = smtReplayer.getSkolemSymbolDef(ctx.getText());
            if (skDef != null) {
                // found definition of skolem symbol
                return skDef;
            }
        }

        // still not found -> unknown
        throw new IllegalStateException("Unknown identifier: " + ctx.getText());
    }
}
