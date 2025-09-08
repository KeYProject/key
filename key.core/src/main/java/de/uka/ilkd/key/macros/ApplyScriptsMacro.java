package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.JmlAssert;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.JmlAssertBuiltInRuleApp;
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.scripts.ScriptCommandAst;
import de.uka.ilkd.key.speclang.njml.JmlParser;
import de.uka.ilkd.key.speclang.njml.JmlParser.ProofArgContext;
import de.uka.ilkd.key.speclang.njml.JmlParser.ProofCmdCaseContext;
import de.uka.ilkd.key.speclang.njml.JmlParser.ProofCmdContext;
import org.antlr.v4.runtime.ParserRuleContext;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.key_project.logic.op.Function;
import org.key_project.prover.engine.ProverTaskListener;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.StringUtil;

import java.util.*;

public class ApplyScriptsMacro extends AbstractProofMacro {

    private final ProofMacro fallBackMacro;

    public ApplyScriptsMacro(ProofMacro fallBackMacro) {
        this.fallBackMacro = fallBackMacro;
    }

    @Override
    public String getName() {
        return "null";
    }

    @Override
    public String getCategory() {
        return "null";
    }

    @Override
    public String getDescription() {
        return "null";
    }

    @Override
    public boolean canApplyTo(Proof proof, ImmutableList<@NonNull Goal> goals, PosInOccurrence posInOcc) {
        return fallBackMacro.canApplyTo(proof, goals, posInOcc)
                || goals.exists(g -> getScript(g) != null);
    }

    private static JmlAssert getScript(Goal goal) {
        RuleApp ruleApp = goal.node().parent().getAppliedRuleApp();
        if (ruleApp instanceof JmlAssertBuiltInRuleApp) {
            JTerm target = (JTerm) ruleApp.posInOccurrence().subTerm();
            if (target.op() instanceof UpdateApplication) {
                target = UpdateApplication.getTarget(target);
            }
            final SourceElement activeStatement = JavaTools.getActiveStatement(target.javaBlock());
            if (activeStatement instanceof JmlAssert jmlAssert) {
                return jmlAssert;
            }
        }
        return null;
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof,
            ImmutableList<Goal> goals, PosInOccurrence posInOcc, ProverTaskListener listener)
            throws InterruptedException, Exception {
        for (Goal goal : goals) {
            if (Thread.interrupted()) {
                throw new InterruptedException();
            }
            JmlAssert jmlAssert = getScript(goal);
            if (jmlAssert == null || jmlAssert.getAssertionProof() == null) {
                // no script found, use fallback macro
                fallBackMacro.applyTo(uic, proof, ImmutableList.of(goal), posInOcc, listener);
                continue;
            }
            KeyAst.JMLProofScript proofScript = jmlAssert.getAssertionProof();
            Map<ParserRuleContext, JTerm> termMap = getTermMap(jmlAssert, proof.getServices());
            List<ScriptCommandAst> renderedProof = renderProof(proofScript, termMap, proof.getServices());
            ProofScriptEngine pse = new ProofScriptEngine(renderedProof, goal);
            System.out.println("---- Script");
            System.out.println(renderedProof);
            pse.execute((AbstractUserInterfaceControl) uic, proof);
        }
        return new ProofMacroFinishedInfo(this, proof);
    }

    private Map<ParserRuleContext, JTerm> getTermMap(JmlAssert jmlAssert, Services services) {
        SpecificationRepository.@Nullable JmlStatementSpec jmlspec = services.getSpecificationRepository().getStatementSpec(jmlAssert);
        if(jmlspec == null) {
            throw new IllegalStateException("No specification found for JML assert statement at " + jmlAssert);
        }
        ImmutableList<JTerm> terms = jmlspec.terms().tail();
        ImmutableList<ParserRuleContext> jmlExprs = jmlAssert.collectTerms().tail();
        Map<ParserRuleContext, JTerm> result = new IdentityHashMap<>();
        assert terms.size() == jmlExprs.size();
        for(int i = 0; i < terms.size(); i++) {
            // TODO build a map from jmlExprs.get(i) to terms.get(i)
            result.put(jmlExprs.get(i), terms.get(i));
        }
        return result;
    }

    private static List<ScriptCommandAst> renderProof(KeyAst.JMLProofScript script, Map<ParserRuleContext, JTerm> termMap, Services services) {
        List<ScriptCommandAst> result = new ArrayList<>();
        for (ProofCmdContext proofCmdContext : script.ctx.proofCmd()) {
            result.addAll(renderProofCmd(proofCmdContext, termMap, services));
        }
        return result;
    }

    private static List<ScriptCommandAst> renderProofCmd(ProofCmdContext ctx, Map<ParserRuleContext, JTerm> termMap, Services services) {
        List<ScriptCommandAst> result = new ArrayList<>();

        // Push the current branch context
        result.add(new ScriptCommandAst("branches", Map.of(), List.of("push")));

        // Compose the command itself
        Map<String, Object> named = new HashMap<>();
        List<Object> positional = new ArrayList<>();
        for (ProofArgContext argContext : ctx.proofArg()) {
            Object value;
            JmlParser.ExpressionContext exp = argContext.expression();
            if(isStringLiteral(exp)) {
                value = StringUtil.stripQuotes(exp.getText());
            } else {
                value = termMap.get(exp);
            }
            if (argContext.argLabel != null) {
                named.put(argContext.argLabel.getText(), value);
            } else {
                positional.add(value);
            }
        }
        result.add(new ScriptCommandAst(ctx.cmd.getText(), named, positional, null, Location.fromToken(ctx.start)));

        // handle proofCmd if present
        if(!ctx.proofCmd().isEmpty()) {
            result.add(new ScriptCommandAst("branches", Map.of("child", 0), List.of("select")));
            for (ProofCmdContext proofCmdContext : ctx.proofCmd()) {
                result.addAll(renderProofCmd(proofCmdContext, termMap, services));
            }
        }

        // handle proofCmdCase if present
        for (ProofCmdCaseContext pcase : ctx.proofCmdCase()) {
            result.add(new ScriptCommandAst("branches", Map.of("name", pcase.label), List.of("select")));
            for (ProofCmdContext proofCmdContext : pcase.proofCmd()) {
                result.addAll(renderProofCmd(proofCmdContext, termMap, services));
            }
        }

        // Pop the branch stack
        result.add(new ScriptCommandAst("branches", Map.of(), List.of("pop")));

        return result;
    }

    private static boolean isStringLiteral(JmlParser.ExpressionContext ctx) {
        return ctx.start == ctx.stop && ctx.start.getType() == JmlParser.STRING_LITERAL;
    }
}
