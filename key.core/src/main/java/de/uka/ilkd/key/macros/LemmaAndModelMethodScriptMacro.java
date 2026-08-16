package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.java.ast.statement.JmlAssert;
import de.uka.ilkd.key.java.transformations.pipeline.JMLTransformer;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.JmlAssertBuiltInRuleApp;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.scripts.ScriptCommandAst;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLLemmaDecl;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLMethodDecl;
import de.uka.ilkd.key.speclang.njml.JmlIO;
import de.uka.ilkd.key.speclang.njml.JmlParser;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ParseTree;
import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Modality;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.engine.ProverTaskListener;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.proof.OpReplacer;
import org.key_project.util.collection.Pair;

public class LemmaAndModelMethodScriptMacro  extends AbstractProofMacro {

    private static final String ID = "[A-Za-z_$0-9.]+";
    private static final Pattern NAME_PATTERN =
            Pattern.compile(ID+ "\\[(" + ID + "::" + ID + ")\\(.*\\)\\].JML model_behavior operation contract.\\d+");

    public LemmaAndModelMethodScriptMacro() { }

    @Override
    public String getName() {
        return "lemma-script-auto-macro";
    }

    @Override
    public String getCategory() {
        return null;
    }

    @Override
    public String getDescription() {
        return "Apply scripts in lemmas and model methods";
    }

    record CutTree(List<ParseTree> localHistory, JmlParser.ExpressionContext cond, CutTree thenTree, CutTree elseTree) {

        private static final Name CUT_TACLET_NAME = new Name("cut");

        public CutTree(List<ParseTree> localHistory) {
            this(localHistory, null, null, null);
        }

        public boolean hasAssertions() {
            return thenTree != null && thenTree.hasAssertions() || elseTree != null && elseTree.hasAssertions() ||
                    localHistory.stream().anyMatch(x -> x instanceof JmlParser.Assert_statementContext);
        }

        public void splitAndExecuteScripts(UserInterfaceControl uic, Goal goal) {
            if(!hasAssertions()) {
                return;
            }
            List<JmlParser.Mbody_varContext> collectedHistory = new ArrayList<>();
            for (ParseTree parseTree : localHistory) {
                switch(parseTree) {
                    case JmlParser.Mbody_varContext varCtx -> collectedHistory.add(varCtx);
                    case JmlParser.Assert_statementContext assertCtx -> {
                        Pair<Goal, Goal> goals = doCut(collectedHistory, goal, assertCtx.expression());
                        executeScriptsOnAssertion(uic, goals.second, assertCtx.assertionProof());
                        goal = goals.first;
                    }
                    default -> throw new IllegalStateException("Unexpected value: " + parseTree);
                }
            }
            if(cond != null) {
                Pair<Goal, Goal> goals = doCut(collectedHistory, goal, cond);
                thenTree.splitAndExecuteScripts(uic, goals.first);
                elseTree.splitAndExecuteScripts(uic, goals.second);
            }
        }

        private Pair<Goal, Goal> doCut(List<JmlParser.Mbody_varContext> assignments, Goal goal, JmlParser.ExpressionContext expression) {
            if(!assignments.isEmpty()) {
                throw new UnsupportedOperationException("Assignments are not yet supported here");
            }

            Taclet cut = goal.proof().getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(CUT_TACLET_NAME);
            TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
            SchemaVariable sv = app.uninstantiatedVars().iterator().next();

            // todo ...
            JTerm term = new JmlIO(goal.proof().getServices()).translateTerm(expression);
            JTerm formula = goal.proof().getServices().getTermBuilder().convertToFormula(term);

            app = app.addCheckedInstantiation(sv, formula, goal.proof().getServices(), true);
            ImmutableList<Goal> goals = goal.apply(app);
            assert goals.size() == 2;
            return new Pair<>(goals.get(0), goals.get(1));
        }
    }



    @Override
    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals, PosInOccurrence posInOcc) {
        // only applicable on the root of the proof
        // todo change this to allow for subproofs of lemmas and model methods
        if(!goals.stream().allMatch(g -> g.node() == proof.root()))
            return false;

        String name = proof.name().toString();
        Matcher m = NAME_PATTERN.matcher(name);
        return m.matches();
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof, ImmutableList<Goal> goals, PosInOccurrence posInOcc, ProverTaskListener listener) throws Exception {
        String name = proof.name().toString();
        Matcher m = NAME_PATTERN.matcher(name);
        if (!m.matches())
            throw new RuntimeException("This macro was not applicable");

        Services services = proof.getServices();
        String lemmaName = m.group(1);
        Function function = services.getNamespaces().functions().lookup(lemmaName);
        if(function instanceof ProgramMethod pm && pm.isModel()) {
            if(pm.isLemma()) {
                return applyToLemma(uic, goals.head(), pm);
            } else {
                return applyToModel(uic, goals.head(), pm);
            }
        } else {
            // do nothing if this is not a lemma or model method, but return the goals unchanged
            return new ProofMacroFinishedInfo(this, goals);
        }
    }

    private ProofMacroFinishedInfo applyToLemma(UserInterfaceControl uic, Goal root, ProgramMethod pm) {
        // Currently treat lemmas the same way: if an attached JML assert script is present
        // at the current goal, execute it using the shared support.
        TextualJMLLemmaDecl methodDecl = (TextualJMLLemmaDecl) pm.getMethodDeclaration().getAttachedJml().last();
        JmlParser.Lemma_declarationContext ctx =
                (JmlParser.Lemma_declarationContext) methodDecl.getMethodDefinition();
        executeScriptsOnAssertion(uic, root, ctx.assertionProof());
        return new ProofMacroFinishedInfo(this, ImmutableList.of(root));
    }

    private ProofMacroFinishedInfo applyToModel(UserInterfaceControl uic, Goal root, ProgramMethod pm) {
        TextualJMLMethodDecl methodDecl = (TextualJMLMethodDecl) pm.getMethodDeclaration().getAttachedJml().head();
        JmlParser.Method_declarationContext ctx =
                (JmlParser.Method_declarationContext) methodDecl.getMethodDefinition();

        CutTree cutTree = extractCutTree(ctx.method_body);

        cutTree.splitAndExecuteScripts(uic, root);

        return new ProofMacroFinishedInfo(this, ImmutableList.of(root));
    }

    private static void executeScriptsOnAssertion(UserInterfaceControl uic, Goal goal, JmlParser.AssertionProofContext assertionProofContext) {
        JmlAssert jmlAssert = getJmlAssert(goal.node());
        if (jmlAssert == null || jmlAssert.getAssertionProof() == null) {
            return;
        }
        KeyAst.JMLProofScript proofScript = jmlAssert.getAssertionProof();
        JavaBlock javaBlock = getJavaBlock(goal);
        Map<ParserRuleContext, JTerm> termMap =
            JmlProofScriptSupport.getTermMapForAssert(jmlAssert, javaBlock, goal.proof().getServices());
        Map<LocationVariable, JFunction> obtainMap =
            JmlProofScriptSupport.makeObtainVarMap(jmlAssert.collectVariablesInProof(null));
        OpReplacer updateReplacer = JmlProofScriptSupport.getUpdateReplacer(goal);
        try {
            List<ScriptCommandAst> rendered = JmlProofScriptSupport.renderProof(proofScript, termMap, updateReplacer, goal.proof().getServices());
            ProofScriptEngine pse = JmlProofScriptSupport.prepareEngine(goal.proof(), goal, obtainMap);
            pse.execute((AbstractUserInterfaceControl) uic, rendered);
        } catch (de.uka.ilkd.key.scripts.ScriptException e) {
            throw new RuntimeException(e);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
    }

    private static JmlAssert getJmlAssert(Node node) {
        if (node == null || node.parent() == null) {
            return null;
        }
        RuleApp ruleApp = node.parent().getAppliedRuleApp();
        if (ruleApp instanceof JmlAssertBuiltInRuleApp) {
            JTerm target = (JTerm) ruleApp.posInOccurrence().subTerm();
            if (target.op() instanceof UpdateApplication) {
                target = UpdateApplication.getTarget(target);
            }
            final SourceElement activeStatement = JavaTools.getActiveStatement(target.javaBlock());
            if (activeStatement instanceof JmlAssert jmlAssert
                    && jmlAssert.getAssertionProof() != null) {
                return jmlAssert;
            }
        }
        return null;
    }

    private static JavaBlock getJavaBlock(Goal goal) {
        RuleApp ruleApp = goal.node().parent().getAppliedRuleApp();
        JTerm appliedOn = (JTerm) ruleApp.posInOccurrence().subTerm();
        if (appliedOn.op() instanceof UpdateApplication) {
            appliedOn = UpdateApplication.getTarget(appliedOn);
        }
        assert appliedOn.op() instanceof Modality;
        return appliedOn.javaBlock();
    }

    private CutTree extractCutTree(ParserRuleContext ctx) {
        JmlParser.Mbody_statementContext stmCtx;
        List<ParseTree> localHistory;

        switch(ctx) {
            case JmlParser.Mbody_blockContext block -> {
                localHistory = block.children.stream().
                        filter(x -> x instanceof JmlParser.Mbody_varContext
                                || x instanceof JmlParser.Assert_statementContext).
                        toList();
                stmCtx = block.mbody_statement();
            }
            case JmlParser.Mbody_statementContext stm -> {
                localHistory = List.of();
                stmCtx = stm;
            }
            default -> throw new IllegalStateException("Unexpected value: " + ctx);
        }

        if(stmCtx instanceof JmlParser.Mbody_ifContext ifCtx) {
            var cond = ifCtx.getChild(JmlParser.ExpressionContext.class, 0);
            var thenBr = ifCtx.getChild(ParserRuleContext.class, 1);
            var elseBr = ifCtx.getChild(ParserRuleContext.class, 2);

            CutTree thenTree = extractCutTree(thenBr);
            CutTree elseTree = extractCutTree(elseBr);

            if (thenTree.hasAssertions() || elseTree.hasAssertions()) {
                return new CutTree(localHistory, cond, thenTree, elseTree);
            }
        }
        return new CutTree(localHistory);
    }

}
