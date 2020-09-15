package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.FormulaChangeInfo;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.macros.TryCloseMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.TacletMatcher;
import de.uka.ilkd.key.smt.SMTProofParser.*;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.misc.Interval;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeWalker;
import org.key_project.util.collection.ImmutableSLList;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class SMTReplayer {
    private final String smtOutput;
    /** the current "main goal" of the proof */
    private final Goal original;
    private Goal goal;
    private Map<SequentFormula, NoPosTacletApp> sf2InsertTaclet = new HashMap<>();
    private final Proof proof;
    private final Services services;
    private final TermBuilder tb;
    private final TermFactory tf;
    private SMTProofLexer lexer;
    private SMTProofParser parser;
    private ParseTree tree;

    public ProofsexprContext getProofStart() {
        return proofStart;
    }

    private ProofsexprContext proofStart;

    private final Map<String, ProofsexprContext> symbolTable = new LinkedHashMap<>();   // TODO: why linked?
    private final Map<String, Term> translationToTermMap;
    private final Map<String, Term> skMap = new HashMap<>();

    private final Map<String, Sort> sorts = new HashMap<>();

    public SMTReplayer(SMTProblem problem) {
        if (problem.getSolvers().size() != 1) {
            throw new IllegalStateException("Proof can only be replayed from single solver!");
        }
        SMTSolver solver = problem.getSolvers().iterator().next();
        smtOutput = solver.getSolverOutput();
        goal = problem.getGoal();
        original = goal;
        proof = problem.getGoal().proof();
        services = proof.getServices();
        tb = services.getTermBuilder();
        tf = services.getTermFactory();
        translationToTermMap = problem.getTranslationToTermMap();
    }

    public SMTReplayer(String smtOutput, Goal goal) {
        this.smtOutput = smtOutput;
        this.goal = goal;
        original = goal;
        proof = goal.proof();
        services = proof.getServices();
        tb = services.getTermBuilder();
        tf = services.getTermFactory();
        translationToTermMap = null;
    }

    private SmtoutputContext parse(String s) {
        return parse(CharStreams.fromString(s));
    }

    private SmtoutputContext parse(CharStream input) {
        lexer = new SMTProofLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        //UnbufferedTokenStream<CommonToken> tokens = new UnbufferedTokenStream<>(lexer);
        parser = new SMTProofParser(tokens);

        BailOutErrorStrategy errorStrategy = new BailOutErrorStrategy();
        parser.setErrorHandler(errorStrategy);
        SmtoutputContext result = null;
        try {
            SmtoutputContext tree = parser.smtoutput();
            //Visitor visitor = new Visitor();
            //for (SMTProofParser.S_exprContext ctx : tree.s_expr()) {
            //    result.add(ctx.accept(visitor));
            //}
            return tree;
        } catch (RecognitionException ex) {
            errorStrategy.reportError(parser, ex);
            throw ex;
        } catch (RuntimeException rex) {
            if (rex.getCause() instanceof RecognitionException) {
                errorStrategy.reportError(parser,
                    (RecognitionException) rex.getCause()
                );
                throw rex;
            }
        }
        return result;
    }

    private void findProofStart() {
        // Determine start of actual proof (root of proof tree, last rule application before
        // deriving contradiction). This is the first proofsexpr we encounter that is not inside
        // a var_binding.
        // tree must be walked after parsing (rulename would always be null otherwise)
        ParseTreeWalker.DEFAULT.walk(new SMTProofBaseListener() {
            @Override
            public void enterProofsexpr(ProofsexprContext ctx) {
                if (ctx.rulename != null) {
                    String rulename = ctx.rulename.getText();
                    if (!rulename.equals("let")) {
                        if (proofStart == null) {
                            // this could be the first real proof node ...
                            proofStart = ctx;
                        }
                    }
                }
                super.exitProofsexpr(ctx);
            }

            @Override
            public void exitVar_binding(Var_bindingContext ctx) {
                // was inside var_binding, so not proof start
                proofStart = null;
                super.exitVar_binding(ctx);
            }
        }, tree);
    }

    public void replay() {
        tree = parse(smtOutput);

        findProofStart();

        // collect bindings from let expressions in symbolTable
        BindingsCollector bindingsCollector = new BindingsCollector();
        tree.accept(bindingsCollector);

        // before starting the actual replay: disable OSS (otherwise some taclets will not be found)
        StrategyProperties newProps = proof.getSettings()
                                           .getStrategySettings()
                                           .getActiveStrategyProperties();
        newProps.setProperty(StrategyProperties.OSS_OPTIONS_KEY, StrategyProperties.OSS_OFF);
        Strategy.updateStrategySettings(proof, newProps);

        // hide all original formulas, remember the mapping to insert_hidden_... taclets
        for (SequentFormula sf : goal.sequent().antecedent().asList()) {
            PosInOccurrence pio = new PosInOccurrence(sf, PosInTerm.getTopLevel(), true);
            TacletApp hide = createTacletApp("hide_left", pio, goal);
            goal = goal.apply(hide).head();
            NoPosTacletApp insertRule = goal.node().getLocalIntroducedRules().iterator().next();
            sf2InsertTaclet.put(sf, insertRule);
        }
        for (SequentFormula sf : goal.sequent().succedent().asList()) {
            PosInOccurrence pio = new PosInOccurrence(sf, PosInTerm.getTopLevel(), false);
            TacletApp hide = createTacletApp("hide_right", pio, goal);
            goal = goal.apply(hide).head();
            NoPosTacletApp insertRule = goal.node().getLocalIntroducedRules().iterator().next();
            sf2InsertTaclet.put(sf, insertRule);
        }

        // do actual replay (starting from found proof root)
        ReplayVisitor replayVisitor = new ReplayVisitor();
        try {
            proofStart.accept(replayVisitor);
        } catch (IllegalStateException e) {
            e.printStackTrace();
            // prune back proof to original
            // TODO: disabled for now (debugging)
            // TODO: show error message in GUI
            //goal.proof().pruneProof(original.node());
        }
    }

    /**
     * This visitor collects the definition of a variable introduced in a proof leaf by Z3's skolemization rule (sk).
     *
     */
    private class SkolemCollector extends SMTProofBaseVisitor<Void> {
        private String skVariable;

        public SkolemCollector(String skVariable) {
            this.skVariable = skVariable;
        }

        @Override
        public Void visitProofsexpr(ProofsexprContext ctx) {
            if (ctx.rulename != null && ctx.rulename.getText().equals("sk")) {
                // found sk rule -> create ifEx/epsilon term for skolem variable

                ProofsexprContext succ = ctx.proofsexpr(0);
                // inside of the sk rule there is always an equisatisfiability Noproofterm
                NoprooftermContext eqSat = succ.noproofterm();
                if (!eqSat.func.getText().equals("~")) {
                    throw new IllegalStateException("Found sk rule that does not contain ~ top level!");
                }
                NoprooftermContext ex = eqSat.noproofterm(1);

                DefCollector collector = new DefCollector();
                Term exTerm = collector.visit(ex);
                if (exTerm.op() != Quantifier.EX) {
                    throw new IllegalStateException("Invalid sk rule found (no existential quantifier)!");
                }

                // TODO: check that we have the right variable (sk term may contain other skolem symbols as well!)

                // TODO: how to get a collision free var name?
                Name varName = new Name(skVariable);
                // TODO: currently ifEx supports integer sort only!
                IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();
                QuantifiableVariable qv = new LogicVariable(varName, intLDT.targetSort());

                // as condition, we take the formula under the exists quantifier and replace the bound variable by qv
                QuantifiableVariable exBoundVar = exTerm.boundVars().get(0);
                Term cond = replace(exBoundVar, qv, exTerm.sub(0));
                Term _then = tb.var(qv);
                Term _else = tb.zTerm(-1);    // error value: -1

                Term def = tb.ifEx(qv, cond, _then, _else);

                // add to map
                skMap.put(skVariable, def);
                translationToTermMap.putIfAbsent(skVariable, def);
                return null;
            }
            // descend into rules that are not sk
            return super.visitProofsexpr(ctx);
        }

        // TODO: replace by real equals method in QuantifiableVariable
        private boolean equalsOp(QuantifiableVariable a, QuantifiableVariable b) {
            return a.name().equals(b.name()) && a.sort().equals(b.sort());
        }

        // builds a new Term where orig has been replaced by repl
        private Term replace(QuantifiableVariable toReplace, QuantifiableVariable with, Term in) {
            // using OpReplacer does not replace the QuantifiableVariables (due to missing equals method?)
            //return OpReplacer.replace(tb.var(orig), tb.var(repl), t, tf);
            Operator newOp = in.op();
            //if (newOp.name().equals(toReplace.name())) {
            if (newOp instanceof QuantifiableVariable
                && equalsOp((QuantifiableVariable) newOp, toReplace)) {
                newOp = with;
            }

            Term[] newTerms = new Term[in.subs().size()];
            for (int i = 0; i < newTerms.length; i++) {
                newTerms[i] = replace(toReplace, with, in.subs().get(i));
            }
            return tf.createTerm(newOp, newTerms);
        }
    }

    /**
     * This visitor is responsible for collecting all variables bound by let and their definitions in the symbol table.
     */
    private class BindingsCollector extends SMTProofBaseVisitor<Void> {
        @Override
        public Void visitVar_binding(Var_bindingContext ctx) {

            String symbol = ctx.SYMBOL().getSymbol().getText();
            ProofsexprContext def = ctx.proofsexpr();

            symbolTable.put(symbol, def);
            return super.visitVar_binding(ctx);
        }
    }

    /**
     * This visitor converts a Z3 term to a KeY term, descending into the succedents of Z3 proof rule terms
     * if necessary.
     */
    private class DefCollector extends SMTProofBaseVisitor<Term> {
        @Override
        public Term visitProofsexpr(ProofsexprContext ctx) {
            if (ctx.rulename != null) {
                // last proofsexpr holds the succedent of the rule application
                assert ctx.proofsexpr() != null && ctx.proofsexpr().size() >= 2;
                ParseTree succedent = ctx.proofsexpr(ctx.proofsexpr().size() - 1);

                ProofsexprContext def = symbolTable.get(succedent.getText());
                if (def != null) {
                    // descend further if this still is a symbol bound by let
                    return visit(def);
                } else if (translationToTermMap.get(succedent.getText()) != null) {
                    // not a symbol -> should be in KeY translation table
                    return translationToTermMap.get(succedent.getText());
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
        public Term visitNoproofterm(NoprooftermContext ctx) {
            ProofsexprContext proofsexpr = symbolTable.get(ctx.getText());
            if (proofsexpr != null) {
                // descend into nested let term
                return visit(proofsexpr);
            }

            Term cached = translationToTermMap.get(ctx.getText());
            if (cached != null) {
                return cached;
            }

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
                        translationToTermMap.put(ctx.getText(), t1);
                        return t1;
                    // marker for instanceof uses w/o direct counterpart in the original sequent
                    case "typeguard":
                        // TODO: better detect at and/implies or quantifier case?
                        return tb.tt();
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
         * @param sortedVar
         * @param quantForm the quantified formula (containing the typeguard)
         * @return
         */
        private QuantifiableVariable extractQV(Sorted_varContext sortedVar, NoprooftermContext quantForm) {
            NamespaceSet nss = services.getNamespaces();
            // TODO: look for the original sort (and ignore the SMT sort for now)
            //String smtSort = ctx.sort().getText();
            //Sort sort = nss.sorts().lookup(ctx.sort().getText());

            // cut the "var_" prefix
            String varName = sortedVar.SYMBOL().getText().substring(4);
            Term cached = translationToTermMap.get(sortedVar.SYMBOL().getText());
            if (cached != null) {
                if (cached.op() instanceof QuantifiableVariable) {
                    System.out.println("Found QuantifiableVariable " + cached.op());
                    return (QuantifiableVariable) cached.op();
                }
            }

            Name name = new Name(varName);

            NoprooftermContext typeguard = extractTypeguard(quantForm);
            if (typeguard == null) {
                throw new IllegalStateException("No typeguard found!");
            }
            // typeguard has the following form: (typeguard var_x sort_int)
            NoprooftermContext nameCtx = typeguard.noproofterm(1);
            NoprooftermContext sortCtx = typeguard.noproofterm(2);
            // cut the "sort_" prefix
            String sortName = sortCtx.getText().substring(5);
            Sort keySort = nss.sorts().lookup(sortName);

            // TODO: multiple quantified variables

            //QuantifiableVariable originalVar = nss.variables().lookup(sortedVar.SYMBOL().getText());

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
            TermFactory tf = services.getTermFactory();
            if (t1.sort() == Sort.FORMULA) {
                return tf.createTerm(Equality.EQV, t1, t2);
            } else {
                return tf.createTerm(Equality.EQUALS, t1, t2);
            }
        }

        @Override
        public Term visitIdentifier(IdentifierContext ctx) {
            if (ctx.getText().equals("false")) {
                return tb.ff();
            } else if (ctx.getText().equals("true")) {
                return tb.tt();
            } else {
                // the symbol is a new skolem symbol introduced by an sk rule in a proof leaf
                Term skDef = skMap.get(ctx.getText());
                if (skDef != null) {
                    // found definition of skolem symbol (was already in map)
                    return skDef;
                } else {    // try to find definition of skolem symbol
                    SkolemCollector skCollector = new SkolemCollector(ctx.getText());
                    // collect all skolem symbols and their definitions using ifEx/eps terms
                    skCollector.visit(tree);
                    skDef = skMap.get(ctx.getText());
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

    private class ReplayVisitor extends SMTProofBaseVisitor<Void> {
        @Override
        public Void visitProofsexpr(ProofsexprContext ctx) {

            // do not descend into let terms
            if (ctx.LET() != null) {
                return null;
            }

            Token rule = ctx.rulename;
            if (rule == null) {
                return super.visitProofsexpr(ctx);
            }

            String rulename = ctx.rulename.getText();
            System.out.println(rulename);
            goal.node().getNodeInfo().setNotes(rulename);

            switch (rulename) {
                case "asserted":
                    //runAutoMode(goal, true);
                    replayAsserted(ctx);
                    return null;
                case "rewrite":
                    replayRewrite(ctx);
                    return null;
                case "monotonicity":
                    replayMonotonicity(ctx);
                    return null;
                case "trans":
                    replayTrans(ctx);
                    return null;
                case "iff-true":
                    replayIffTrue(ctx);
                    return null;
                case "iff-false":
                    replayIffFalse(ctx);
                    return null;
                case "not-or-elim":
                    replayNotOrElim(ctx);
                    return null;
                case "and-elim":
                    replayAndElim(ctx);
                    return null;
                case "mp":
                case "mp~":
                    replayMp(ctx);
                    return null;
                case "unit-resolution":
                    replayUnitResolution(ctx);
                    return null;
                case "th-lemma":
                    replayThLemma(ctx);
                    return null;
                case "sk":
                    replaySk(ctx);
                    return null;
                default:
                    throw new IllegalStateException("Replay for rule currently not implemented: " + rulename);
            }
            //return super.visitProofsexpr(ctx);
        }

        private void replaySk(ProofsexprContext ctx) {
            System.out.println("Replaying sk rule not implemented");
        }

        private void replayThLemma(ProofsexprContext ctx) {
            int arity = ctx.proofsexpr().size();

            // two cases: leaf rule or final rule in proof
            if (ctx.proofsexpr(arity - 1).getText().equals("false")) {
                // final rule
                Term cutTerm = extractRuleAntecedents(ctx);
                TacletApp app = createCutApp(goal, cutTerm);
                List<Goal> goals = goal.apply(app).toList();
            } else {
                // leaf rule
                runAutoMode(goal, false);
            }
        }

        private void replayAsserted(ProofsexprContext ctx) {
            // get sequentFormula, get corresponding insert_taclet from map, apply
            SequentFormula seqForm = goal.sequent().succedent().get(0);
            PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);

            // two possible choices:
            TacletApp app = sf2InsertTaclet.get(seqForm);
            TacletApp notApp = sf2InsertTaclet.get(new SequentFormula(tb.not(seqForm.formula())));

            if (app != null) {
                goal = goal.apply(app).head();
            } else if (notApp != null) {
                goal = goal.apply(notApp).head();

                if (seqForm.formula().op() == Junctor.NOT) {
                    app = createTacletApp("notRight", pio, goal);
                    goal = goal.apply(app).head();

                    SequentChangeInfo sci = goal.node().getNodeInfo().getSequentChangeInfo();
                    SequentFormula addedAntec = sci.addedFormulas(true).head();
                    pio = new PosInOccurrence(addedAntec, PosInTerm.getTopLevel(), true);
                    app = createTacletApp("closeAntec", pio, goal);
                    goal = goal.apply(app).head();
                }
            } else {
                //throw new IllegalStateException("The formula " + seqForm.formula() + " is not an assertion!");
                System.out.println("The formula " + seqForm.formula() + " is not found as assertion!");
                //System.out.println("Starting auto mode ...");
                // TODO: insert matching assertion (how to find?)
            }

            /*
            SequentChangeInfo sci = goal.node().getNodeInfo().getSequentChangeInfo();
            SequentFormula addedAntec = sci.addedFormulas(true).head();
            SequentFormula addedSucc = sci.addedFormulas(false).head();

            if (addedAntec != null) {
                pio = new PosInOccurrence(addedAntec, PosInTerm.getTopLevel(), true);
                app = createTacletApp("closeAntec", pio, goal);
                goal = goal.apply(app).head();
            } else if (addedSucc != null) {

                pio = new PosInOccurrence(addedSucc, PosInTerm.getTopLevel(), false);
                app = createTacletApp("notRight", pio, goal);
                goal = goal.apply(app).head();


                //sci = goal.node().getNodeInfo().getSequentChangeInfo();
                pio = new PosInOccurrence(sci.addedFormulas(true).head(), PosInTerm.getTopLevel(), true);
                app = createTacletApp("closeAntec", pio, goal);
                goal = goal.apply(app).head();

            } else {
                throw new IllegalStateException("Error applying insert_hidden_.. taclet!");
            }
             */
        }

        private void replayRewrite(ProofsexprContext ctx) {
            if (goal.sequent().succedent().get(0).formula().op() == Equality.EQV) {
                // equiv_right top level to guide the prover
                SequentFormula seqForm = goal.sequent().succedent().get(0);
                PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
                TacletApp app = createTacletApp("equiv_right", pio, goal);
                List<Goal> goals = goal.apply(app).toList();
                // running automode separately on both goals increases success rate
                runAutoMode(goals.get(0), false);
                runAutoMode(goals.get(1), false);
            } else {
                runAutoMode(goal, false);
            }
        }

        private void replayIffTrue(ProofsexprContext ctx) {
            SequentFormula seqForm = goal.sequent().succedent().get(0);
            PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
            TacletApp concreteEq3 = createTacletApp("concrete_eq_3", pio, goal);
            goal = goal.apply(concreteEq3).head();
            visit(ctx.proofsexpr(0));
        }

        private void replayIffFalse(ProofsexprContext ctx) {
            SequentFormula seqForm = goal.sequent().succedent().get(0);
            PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
            TacletApp concreteEq4 = createTacletApp("concrete_eq_4", pio, goal);
            goal = goal.apply(concreteEq4).head();
            visit(ctx.proofsexpr(0));
        }

        private void replayAndElim(ProofsexprContext ctx) {
            Term cutTerm = extractRuleAntecedents(ctx);
            TacletApp app = createCutApp(goal, cutTerm);
            List<Goal> goals = goal.apply(app).toList();
            Goal left = goals.get(1);
            SequentFormula orig = left.sequent().succedent().get(0);

            SequentFormula seqForm = left.sequent().antecedent().get(0);
            PosInOccurrence pio;
            for (int i = 0; i < ctx.proofsexpr().size(); i++) {
            // while (seqForm.formula().op() == Junctor.AND) {
                pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
                app = createTacletApp("andLeft", pio, left);
                left = left.apply(app).head();
                SequentChangeInfo sci = left.node().getNodeInfo().getSequentChangeInfo();
                // TODO: is the order of the added formulas deterministic?
                seqForm = sci.addedFormulas().tail().head();
                if (seqForm == null) {
                    // attention: the formula may be equal to the original one by chance
                    break;
                }
            }

            seqForm = left.sequent().succedent().get(0);
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
            app = createTacletApp("close", pio, left);
            left = left.apply(app).head();

            ////////////////////////////////////////////////////////////////////////////////////////////////////////////
            goal = goals.get(0);
            replayRightSideHelper(ctx);
        }

        private void replayNotOrElim(ProofsexprContext ctx) {
            Term cutTerm = extractRuleAntecedents(ctx);
            TacletApp app = createCutApp(goal, cutTerm);
            List<Goal> goals = goal.apply(app).toList();
            Goal left = goals.get(1);
            SequentFormula orig = left.sequent().succedent().get(0);

            SequentFormula seqForm = left.sequent().antecedent().get(0);
            PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
            app = createTacletApp("notLeft", pio, left);
            left = left.apply(app).head();

            // orRight
            seqForm = left.sequent().succedent().get(0);
            // better count up to arity
            for (int i = 0; i < ctx.proofsexpr().size(); i++) {
            //while (seqForm.formula().op() == Junctor.OR) {
                pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
                app = createTacletApp("orRight", pio, left);
                left = left.apply(app).head();
                //seqForm = left.sequent().succedent().get(0);
                SequentChangeInfo sci = left.node().getNodeInfo().getSequentChangeInfo();
                // TODO: is the order of the added formulas deterministic?
                seqForm = sci.addedFormulas().tail().head();
                if (seqForm == null) {
                    // attention: the formula may be equal to the original one by chance
                    break;
                }
            }

            pio = new PosInOccurrence(orig, PosInTerm.getTopLevel(), false);
            if (orig.formula().op() == Junctor.NOT) {
                app = createTacletApp("notRight", pio, left);
            } else {
                // TODO: additional rule (not in standard taclets!)
                app = createTacletApp("notElimRight", pio, left);
            }
            left = left.apply(app).head();

            seqForm = left.sequent().antecedent().get(0);
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
            app = createTacletApp("closeAntec", pio, left);
            left = left.apply(app).head();

            ////////////////////////////////////////////////////////////////////////////////////////////////////////
            goal = goals.get(0);
            replayRightSideHelper(ctx);
        }

        private void replayMonotonicity(ProofsexprContext ctx) {
            Term cutTerm = extractRuleAntecedents(ctx);
            TacletApp app = createCutApp(goal, cutTerm);
            List<Goal> goals = goal.apply(app).toList();
            Goal left = goals.get(1);
            SequentFormula seqForm = left.sequent().antecedent().get(0);

            PosInOccurrence pio;

            int params = 1;

            // and left
            while (seqForm.formula().op() == Junctor.AND) {
                pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
                app = createTacletApp("andLeft", pio, left);
                left = left.apply(app).head();
                seqForm = left.sequent().antecedent().get(0);
                params++;
            }

            // apply equalities
            for (int i = 0; i < params; i++) {

                // TODO: =
                //seqForm = left.sequent().succedent().get(0);
                //pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel().down(0).down(i), false);
                //app = createTacletApp("applyEq", pio, left);
                //left = left.apply(app).head();

                // TODO: <->
                seqForm = left.sequent().antecedent().get(i);
                pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
                app = createTacletApp("insert_eqv_once_lr", pio, left);
                left = left.apply(app).head();


                seqForm = left.sequent().succedent().get(0);
                pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel().down(0).down(i), false);
                //app = createTacletApp("insert_eqv", pio, left);
                // TODO: is there always only one locally introduced rule?
                Iterable<NoPosTacletApp> localRules = left.node().getLocalIntroducedRules();
                app = localRules.iterator().next();
                app = autoInst(app, pio, left);
                left = left.apply(app).head();
            }

            // TODO: =
            //seqForm = left.sequent().succedent().get(0);
            //pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
            //app = createTacletApp("eqClose", pio, left);
            //left = left.apply(app).head();

            // TODO: <->
            seqForm = left.sequent().succedent().get(0);
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
            app = createTacletApp("eq_eq", pio, left);
            left = left.apply(app).head();

            seqForm = left.sequent().succedent().get(0);
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), false);
            app = createTacletApp("closeTrue", pio, left);
            left = left.apply(app).head();

            ////////////////////////////////////////////////////////////////////////////////////////////////////////
            goal = goals.get(0);
            replayRightSideHelper(ctx);
        }

        private void replayUnitResolution(ProofsexprContext ctx) {
            Term cutTerm = extractRuleAntecedents(ctx);
            TacletApp app = createCutApp(goal, cutTerm);
            List<Goal> goals = goal.apply(app).toList();

            // last child is succedent, first child is a | b | ..., others are unit clauses
            int unitClauseCount = ctx.proofsexpr().size() - 2;

            Goal left = goals.get(1);
            SequentChangeInfo sci = left.node().getNodeInfo().getSequentChangeInfo();

            SequentFormula seqForm = sci.addedFormulas().head();

            // split unit clauses from cut formula
            PosInOccurrence pio;
            SequentFormula clause = null;
            List<SequentFormula> unitClauses = new ArrayList<>();
            for (int i = 0; i < unitClauseCount; i++) {
                pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
                app = createTacletApp("andLeft", pio, left);
                left = left.apply(app).head();
                sci = left.node().getNodeInfo().getSequentChangeInfo();
                // TODO: is the order of the added formulas deterministic?
                seqForm = sci.addedFormulas().tail().head();
                unitClauses.add(sci.addedFormulas().head());

                // the clause a | b | ... is the last one remaining after the split
                clause = seqForm;
            }

            List<SequentFormula> negUnitClauses = new ArrayList<>();

            // for every unit clause: apply notLeft
            for (SequentFormula unitClause : unitClauses) {
                pio = new PosInOccurrence(unitClause, PosInTerm.getTopLevel(), true);
                app = createTacletApp("notLeft", pio, left);
                left = left.apply(app).head();
                sci = left.node().getNodeInfo().getSequentChangeInfo();
                negUnitClauses.add(sci.addedFormulas().head());
            }

            if (unitClauseCount > 1) {
                for (int i = 0; i < unitClauseCount; i++) {
                    // TODO: order and clause count may differ
                    if (i == unitClauseCount - 1) {
                        // different position for last unit clause!
                        pio = new PosInOccurrence(clause, PosInTerm.getTopLevel(), true);
                    } else {
                        pio = new PosInOccurrence(clause, PosInTerm.getTopLevel().down(0), true);
                    }
                    app = createTacletApp("replace_known_right", pio, left);
                    left = left.apply(app).head();

                    sci = left.node().getNodeInfo().getSequentChangeInfo();
                    clause = sci.modifiedFormulas().head().getNewFormula();

                    // not necessary for last clause!
                    if (i != unitClauseCount - 1) {
                        pio = new PosInOccurrence(clause, PosInTerm.getTopLevel(), true);
                        app = createTacletApp("concrete_or_2", pio, left);
                        left = left.apply(app).head();

                        sci = left.node().getNodeInfo().getSequentChangeInfo();
                        clause = sci.modifiedFormulas().head().getNewFormula();
                    }
                }
                pio = new PosInOccurrence(clause, PosInTerm.getTopLevel(), true);
                app = createTacletApp("closeFalse", pio, left);
                left = left.apply(app).head();
            } else {    // unitClauseCount == 1
                pio = new PosInOccurrence(clause, PosInTerm.getTopLevel(), true);
                app = createTacletApp("closeAntec", pio, left);
                left = left.apply(app).head();
            }

            ////////////////////////////////////////////////////////////////////////////////////////////////////////
            goal = goals.get(0);
            replayRightSideHelper(ctx);
        }

        /**
         * Splits the formula at the right side of a cut into the different antecedents of a rule and starts
         * replay of the corresponding subtrees.
         * @param ctx
         */
        private void replayRightSideHelper(ProofsexprContext ctx) {

            SequentChangeInfo sci = goal.node().getNodeInfo().getSequentChangeInfo();
            SequentFormula cutFormula = sci.addedFormulas().head();

            goal = hideAllOther(cutFormula, goal);

            PosInOccurrence pio;
            TacletApp app;

            // last is succedent, others are subterms
            int antecCount = ctx.proofsexpr().size() - 1;
            System.out.println("Found " + getOriginalText(ctx));
            System.out.println("  Arity is " + antecCount);

            for (int i = antecCount - 1; i > 0; i--) {
                pio = new PosInOccurrence(cutFormula, PosInTerm.getTopLevel(), false);
                app = createTacletApp("andRight", pio, goal);
                List<Goal> antecs = goal.apply(app).toList();

                goal = antecs.get(0);
                visit(ctx.proofsexpr(i));

                goal = antecs.get(1);
                sci = goal.node().getNodeInfo().getSequentChangeInfo();
                cutFormula = sci.addedFormulas().head();
            }
            visit(ctx.proofsexpr(0));
        }

        private void replayTrans(ProofsexprContext ctx) {
            Term cutTerm = extractRuleAntecedents(ctx);
            TacletApp app = createCutApp(goal, cutTerm);
            List<Goal> goals = goal.apply(app).toList();

            Goal left = goals.get(1);
            SequentFormula seqForm = goal.sequent().antecedent().get(0);
            PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
            app = createTacletApp("andLeft", pio, left);
            left = left.apply(app).head();

            seqForm = left.sequent().antecedent().get(1);
            // TODO: other operators
            //if (seqForm.formula().op().equals(Junctor.IMP)) { ... }
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
            app = createTacletApp("insert_eqv_once_lr", pio, left);
            left = left.apply(app).head();

            NoPosTacletApp insert_eqv = findLocalRule("insert_eqv", left);
            seqForm = left.sequent().antecedent().get(0);
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel().down(1), true);
            app = autoInst(insert_eqv, pio, left);
            left = left.apply(app).head();

            seqForm = left.sequent().antecedent().get(0);
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
            app = createTacletApp("closeAntec", pio, left);
            left = left.apply(app).head();

            ////////////////////////////////////////////////////////////////////////////////////////////////////////
            goal = goals.get(0);
            replayRightSideHelper(ctx);
        }

        private void replayMp(ProofsexprContext ctx) {
            ProofsexprContext p = ctx.proofsexpr(0);
            ProofsexprContext p_imp_q = ctx.proofsexpr(1);

            Term cutTerm = extractRuleAntecedents(ctx);
            TacletApp app = createCutApp(goal, cutTerm);
            List<Goal> goals = goal.apply(app).toList();

            ////////////////////////////////////////////////////////////////////////////////////////////////////////
            // left: and_left, replace_known_left, concrete_impl, close
            Goal left = goals.get(1);

            SequentFormula seqForm = left.sequent().antecedent().get(0);
            PosInOccurrence pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
            app = createTacletApp("andLeft", pio, left);
            left = left.apply(app).head();

            seqForm = left.sequent().antecedent().get(1);
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel().down(0), true);
            app = createTacletApp("replace_known_left", pio, left);
            left = left.apply(app).head();

            seqForm = left.sequent().antecedent().get(1);
            pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
            app = createTacletApp("concrete_eq_1", pio, left);
            left = left.apply(app).head();

            // Two cases: Is the last changed formula "false" or not?
            SequentChangeInfo sci = left.node().getNodeInfo().getSequentChangeInfo();
            FormulaChangeInfo fci = sci.modifiedFormulas(true).head();
            Term newTerm = fci.getNewFormula().formula();
            if (newTerm.equals(tb.ff())) {
                // 1. case: Gamma, false ==> Delta
                //   in this case apply closeFalse (used for final refutation of proof)
                seqForm = left.sequent().antecedent().get(1);
                pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
                app = createTacletApp("closeFalse", pio, left);
                left = left.apply(app).head();
            } else {
                // 2. case: Gamma, f ==> Delta, f
                //   in this case apply closeAntec
                seqForm = left.sequent().antecedent().get(1);
                pio = new PosInOccurrence(seqForm, PosInTerm.getTopLevel(), true);
                app = createTacletApp("closeAntec", pio, left);
                left = left.apply(app).head();
            }

            assert left.node().isClosed();

            ////////////////////////////////////////////////////////////////////////////////////////////////////////
            goal = goals.get(0);
            replayRightSideHelper(ctx);
        }

        @Override
        public Void visitIdentifier(IdentifierContext ctx) {
            ProofsexprContext def = symbolTable.get(ctx.getText());
            if (def != null) {
                // continue proof replay with the partial tree from the symbol table
                visit(def);
            }
            return null;
        }
    }

    private static String getOriginalText(ProofsexprContext ctx) {
        if (ctx.start == null || ctx.start.getStartIndex() < 0 || ctx.stop == null || ctx.stop.getStopIndex() < 0) {
            // fallback
            return ctx.getText();
        }
        int start = ctx.start.getStartIndex();
        int end = ctx.stop.getStopIndex();
        return ctx.start.getInputStream().getText(Interval.of(start, end));
    }

    private Goal hideAllOther(SequentFormula remaining, Goal goal) {
        PosInOccurrence pio;
        TacletApp app;
        for (SequentFormula other : goal.sequent().succedent()) {
            if (!other.equals(remaining)) {
                pio = new PosInOccurrence(other, PosInTerm.getTopLevel(), false);
                app = createTacletApp("hide_right", pio, goal);
                goal = goal.apply(app).head();
            }
        }
        for (SequentFormula other : goal.sequent().antecedent()) {
            if (!other.equals(remaining)) {
                pio = new PosInOccurrence(other, PosInTerm.getTopLevel(), true);
                app = createTacletApp("hide_left", pio, goal);
                goal = goal.apply(app).head();
            }
        }
        return goal;
    }

    private NoPosTacletApp findLocalRule(String namePrefix, Goal goal) {
        for (NoPosTacletApp app : goal.node().getLocalIntroducedRules()) {
            // TODO: there may be multiple rules with this prefix
            if (app.taclet().name().toString().startsWith(namePrefix)) {
                return app;
            }
        }
        return null;
    }

    private Term extractRuleAntecedents(ProofsexprContext ctx) {
        List<ProofsexprContext> children = ctx.proofsexpr();
        if (children.size() == 1) {
            // closing rule (e.g. rewrite, asserted, ...)
            return null;
        } else {
            List<Term> antecs = new ArrayList<>();
            // antecendent of the rule are all terms expect the last one
            for (int i = 0; i < children.size() - 1; i++) {
                ProofsexprContext child = children.get(i);
                antecs.add(lookupOrCreate(child));
            }
            if (antecs.size() == 1) {
                return antecs.get(0);
            }
            Term result = antecs.get(0);
            for (int i = 1; i < antecs.size(); i++) {
                result = tf.createTerm(Junctor.AND, result, antecs.get(i));
            }
            return result;
        }
    }

    private Term lookupOrCreate(ProofsexprContext ctx) {
        // child could be:
        // - symbol from KeY (is in translation map)
        // - symbol bound via let
        // - a term with nested rule applications
        Term term = translationToTermMap.get(ctx.getText());
        if (term == null) {
            // recursively descend into let definition
            ProofsexprContext let_def = symbolTable.get(ctx.getText());
            if (let_def != null) {
                term = let_def.accept(new DefCollector());
            } else {
                // could be a term containing nested rule applications again
                term = ctx.accept(new DefCollector());
            }
        }
        return term;
    }

    private static TacletApp createTacletApp(String tacletName, PosInOccurrence pos, Goal goal) {
        TacletApp app = goal.indexOfTaclets().lookup(tacletName);
        System.out.println("Creating TacletApp " + tacletName);
        return autoInst(app, pos, goal);
    }

    // automatically instantiates taclet from PosInOccurrence, only works for taclets where all instantiations
    // are determined by the position
    private static TacletApp autoInst(TacletApp app, PosInOccurrence pos, Goal goal) {
        Services services = goal.proof().getServices();
        Term posTerm = pos.subTerm();
        app = app.setPosInOccurrence(pos, services);

        // automatically find instantiations for matching find term
        TacletMatcher matcher = app.taclet().getMatcher();
        // use app.matchConditions(): must not overwrite fixed instantiations (e.g. insert_hidden taclet)
        MatchConditions current = app.matchConditions();
        MatchConditions mc = matcher.matchFind(posTerm, current, services);
        app = app.setMatchConditions(mc, services);

        // automatically find formulas for matching assume
        app = app.findIfFormulaInstantiations(goal.sequent(), services).head();

        assert app.complete();
        return app;
    }

    private static NoPosTacletApp createCutApp(Goal goal, Term cutFormula) {
        SequentFormula seqForm = new SequentFormula(cutFormula);
        NoPosTacletApp app = goal.indexOfTaclets().lookup("cut");
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();
        // TODO: since all branches in addInstantiation return NoPosTacletApp, the cast should always be safe
        return (NoPosTacletApp) app.addInstantiation(sv, cutFormula, true, goal.proof().getServices());
    }

    private void runAutoMode(Goal goal, boolean insertOriginal) {

        if (insertOriginal) {
            // reinsert original taclet
            Set<NoPosTacletApp> noPosTaclets = goal.indexOfTaclets().allNoPosTacletApps();
            for (NoPosTacletApp app : noPosTaclets) {
                // TODO: how to identify uniquely?
                if (app.taclet().name().toString().startsWith("insert_hidden_taclet_0")) {
                    goal.apply(app);
                }

                /*
                if (app.taclet().displayName().startsWith("insert_hidden")) {
                    //SVInstantiations svinst = app.instantiations();
                    //SchemaVariable sv = app.instantiations().svIterator().next();
                    //Term t = svinst.getTermInstantiation(sv, svinst.getExecutionContext(), goal.proof().getServices());
                    // TODO: do not apply all insert_hidden taclets!
                    goal.apply(app);
                    break;
                }*/
            }
        }

        // current notes could contain rule name -> append
        String currentNotes = goal.node().getNodeInfo().getNotes();
        if (currentNotes != null) {
            goal.node().getNodeInfo().setNotes(currentNotes + " automatic proof search");
        } else {
            goal.node().getNodeInfo().setNotes("automatic proof search");
        }

        TryCloseMacro close = new TryCloseMacro(50);
        try {
            close.applyTo(null, goal.proof(), ImmutableSLList.<Goal>nil().append(goal), null, null);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }
}
