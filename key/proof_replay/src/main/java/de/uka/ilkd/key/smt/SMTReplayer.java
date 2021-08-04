package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.smt.SMTProofParser.ProofsexprContext;
import de.uka.ilkd.key.smt.SMTProofParser.SmtoutputContext;
import de.uka.ilkd.key.smt.SMTProofParser.Var_bindingContext;
import de.uka.ilkd.key.strategy.JavaCardDLStrategyFactory;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.Interval;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeProperty;
import org.antlr.v4.runtime.tree.ParseTreeWalker;

import java.util.*;

public class SMTReplayer {
    private final String smtOutput;
    private final Goal original;
    /** the current "main goal" of the proof */
    private Goal goal;

    public Collection<NoPosTacletApp> getAllAssertionInsertTaclets() {
        return sf2InsertTaclet.values();
    }

    private final Map<SequentFormula, NoPosTacletApp> sf2InsertTaclet = new HashMap<>();
    private final Proof proof;
    private SMTProofLexer lexer;
    private SMTProofParser parser;

    private ParseTree tree;

    public ParseTreeProperty<Namespace<NamedParserRuleContext>> getNamespaces() {
        return namespaces;
    }

    private final ParseTreeProperty<Namespace<NamedParserRuleContext>>
        namespaces = new ParseTreeProperty<>();

    private ProofsexprContext proofStart;


    public ParseTree getTree() {
        return tree;
    }

    public ProofsexprContext getProofStart() {
        return proofStart;
    }

    // HashMap is linked to make debugging easier
    private final Map<String, ProofsexprContext> symbolTable = new LinkedHashMap<>();
    // translation needs to be aware of the context, i.e. the bound variables at the current
    // translation context (contained in SMTExprInContext)!
    private final Map<SMTExprInContext, Term> translationToTermMap;
    private final Map<String, Term> skMap = new HashMap<>();
    private final Map<String, Node> knownReplayedNodes = new HashMap<>();

    public void addKnownReplayedNode(String text, Node node) {
        knownReplayedNodes.put(text, node);
    }

    public Node getKnownReplayedNode(String key) {
        return knownReplayedNodes.get(key);
    }

    public static class SMTExprInContext {
        public final String smtExpr;
        public final Deque<QuantifiableVariable> boundVars;

        public SMTExprInContext(String smtExpr, Deque<QuantifiableVariable> boundVars) {
            this.smtExpr = smtExpr;
            this.boundVars = boundVars;
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) {
                return true;
            }
            if (!(other instanceof SMTExprInContext)) {
                return false;
            }
            SMTExprInContext key = (SMTExprInContext) other;
            return smtExpr.equals(key.smtExpr) && boundVars.equals(key.boundVars);
        }

        @Override
        public int hashCode() {
            int result = smtExpr.hashCode();
            result = 31 * result + boundVars.hashCode();
            return result;
        }

    }

    public void putSkolemSymbol(String symbol, Term def) {
        skMap.put(symbol, def);
    }

    public Term getSkolemSymbolDef(String symbol) {
        return skMap.get(symbol);
    }

    public SMTReplayer(SMTProblem problem) {
        if (problem.getSolvers().size() != 1) {
            throw new IllegalStateException("Proof can only be replayed from single solver!");
        }
        if (problem.getFinalResult().isValid() != SMTSolverResult.ThreeValuedTruth.VALID) {
            throw new IllegalStateException("The SMT solver could not find a proof!");
        }
        if (problem.getSolvers().iterator().next().getType() != SolverType.Z3_NEW_TL_SOLVER) {
            throw new IllegalStateException("Only Z3 proofs using the new modular translation " +
                " can be replayed currently!");
        }
        SMTSolver solver = problem.getSolvers().iterator().next();
        smtOutput = solver.getSolverOutput();
        goal = problem.getGoal();
        original = goal;
        proof = goal.proof();

        // make sure quantifier handling is enabled (otherwise automatic proof search, for example
        // for nnf-pos/-neg, will not be able to close some goals)
        // TODO: this could be set locally for only the relevant sub-goals
        // set to default Java strategy
        StrategyProperties properties = new StrategyProperties();
        Strategy strategy = new JavaCardDLStrategyFactory().create(proof, properties);
        proof.setActiveStrategy(strategy);

        translationToTermMap = new LinkedHashMap<>();

        // we wrap the original String keys in SMTExprInContext to be aware of the bound variables
        for (Map.Entry<String, Term> e : problem.getTranslationToTermMap().entrySet()) {
            // root: no bound variables
            addTranslationToTerm(e.getKey(), e.getValue());
        }
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
        //try {
            return parser.smtoutput();
        /*} catch (RecognitionException ex) {
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
        return result;*/
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
        BindingsCollector bindingsCollector = new BindingsCollector(this);
        tree.accept(bindingsCollector);

        // before starting the actual replay: disable OSS (otherwise some taclets will not be found)
        StrategyProperties newProps = proof.getSettings()
                                           .getStrategySettings()
                                           .getActiveStrategyProperties();
        newProps.setProperty(StrategyProperties.OSS_OPTIONS_KEY, StrategyProperties.OSS_OFF);
        Strategy.updateStrategySettings(proof, newProps);

        // hide all original formulas (assertions), remember mapping to insert_hidden_... taclets
        for (SequentFormula sf : goal.sequent().antecedent().asList()) {
            PosInOccurrence pio = new PosInOccurrence(sf, PosInTerm.getTopLevel(), true);
            TacletApp hide = ReplayTools.createTacletApp("hide_left", pio, goal);
            goal = ReplayTools.applyInteractive(goal, hide).head();
            NoPosTacletApp insertRule = goal.node().getLocalIntroducedRules().iterator().next();
            sf2InsertTaclet.put(sf, insertRule);
        }
        for (SequentFormula sf : goal.sequent().succedent().asList()) {
            PosInOccurrence pio = new PosInOccurrence(sf, PosInTerm.getTopLevel(), false);
            TacletApp hide = ReplayTools.createTacletApp("hide_right", pio, goal);
            goal = ReplayTools.applyInteractive(goal, hide).head();
            NoPosTacletApp insertRule = goal.node().getLocalIntroducedRules().iterator().next();
            sf2InsertTaclet.put(sf, insertRule);
        }

        // do actual replay (starting from found proof root)
        ReplayVisitor replayVisitor = new ReplayVisitor(this, goal);
        proofStart.accept(replayVisitor);
    }

    public NoPosTacletApp getInsertTacletForSF(SequentFormula sequentFormula) {
        return sf2InsertTaclet.get(sequentFormula);
    }

    public Proof getProof() {
        return proof;
    }

    /*
    public void addSymbolDef(String symbol, ProofsexprContext def) {
        symbolTable.put(symbol, def);
    }*/

    /*
    public ProofsexprContext getSymbolDef(String symbol) {
        return symbolTable.get(symbol);
    }*/

    public ParserRuleContext getSymbolDef(String symbol, ParserRuleContext ctx) {
        // term may be a new symbol introduced by the let binder
        Namespace<NamedParserRuleContext> ctxNS = namespaces.get(ctx);
        if (ctxNS != null) {
            NamedParserRuleContext nprc = ctxNS.lookup(symbol);
            if (nprc != null) {
                //System.out.println(symbol + " (shared proof or noproofterm)");
                return nprc.getCtx();
            }
        }
        return null;
    }

    public Term getTranslationToTerm(String smtExpr) {
        // get from root context, i.e. empty bound vars list
        SMTExprInContext exprInContext = new SMTExprInContext(smtExpr, new LinkedList<>());
        return translationToTermMap.get(exprInContext);
    }

    public void addTranslationToTerm(String smtExpr, Term keyTerm) {
        // root context -> empty list
        SMTExprInContext exprInContext = new SMTExprInContext(smtExpr, new LinkedList<>());
        translationToTermMap.put(exprInContext, keyTerm);
    }
    /*
    public Term getTranslationToTerm(String smtExpr, Deque<QuantifiableVariable> boundVars) {
        SMTExprInContext exprInContext = new SMTExprInContext(smtExpr, boundVars);
        return translationToTermMap.get(exprInContext);
    }

    public void addTranslationToTerm(String smtExpr, Deque<QuantifiableVariable> boundVars,
                                     Term keyTerm) {
        SMTExprInContext exprInContext = new SMTExprInContext(smtExpr, boundVars);
        translationToTermMap.put(exprInContext, keyTerm);
    }
     */
}
