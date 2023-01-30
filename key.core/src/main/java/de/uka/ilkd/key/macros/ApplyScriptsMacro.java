package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.JmlAssert;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.rule.JmlAssertBuiltInRuleApp;
import de.uka.ilkd.key.rule.JmlAssertRule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.njml.JmlParser.AssertionProofContext;
import de.uka.ilkd.key.speclang.njml.JmlParser.ProofArgContext;
import de.uka.ilkd.key.speclang.njml.JmlParser.ProofCmdCaseContext;
import de.uka.ilkd.key.speclang.njml.JmlParser.ProofCmdContext;
import org.key_project.util.collection.ImmutableList;

import java.net.URL;
import java.util.Map;

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
    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals, PosInOccurrence posInOcc) {
        return fallBackMacro.canApplyTo(proof, goals, posInOcc)
                || goals.exists(g -> getScript(g) != null);
    }

    private static AssertionProofContext getScript(Goal goal) {
        RuleApp ruleApp = goal.node().parent().getAppliedRuleApp();
        if (ruleApp instanceof JmlAssertBuiltInRuleApp) {
            Term target = ruleApp.posInOccurrence().subTerm();
            if (target.op() instanceof UpdateApplication) {
                target = UpdateApplication.getTarget(target);
            }
            final SourceElement activeStatement = JavaTools.getActiveStatement(target.javaBlock());
            if (activeStatement instanceof JmlAssert) {
                return ((JmlAssert) activeStatement).getAssertionProof();
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
            AssertionProofContext proofCtx = getScript(goal);
            if (proofCtx == null) {
                fallBackMacro.applyTo(uic, proof, ImmutableList.of(goal), posInOcc, listener);
                continue;
            }
            String renderedProof = renderProof(proofCtx);
            // TODO get this location from the jmlAssertion statement ...
            Location loc = new Location(new URL("file:///tmp/unknown.key"), 42, 42);
            ProofScriptEngine pse = new ProofScriptEngine(renderedProof, loc, goal);
            System.out.println("---- Script");
            System.out.println(renderedProof);
            pse.execute((AbstractUserInterfaceControl) uic, proof);
        }
        return new ProofMacroFinishedInfo(this, proof);
    }

    private static String renderProof(AssertionProofContext ctx) {
        StringBuilder sb = new StringBuilder();
        for (ProofCmdContext proofCmdContext : ctx.proofCmd()) {
            renderProofCmd(proofCmdContext, sb);
        }
        return sb.toString();
    }

    private static void renderProofCmd(ProofCmdContext ctx, StringBuilder sb) {
        if (ctx.cmd != null) {
            sb.append(ctx.cmd.getText()).append(" ");
            for (ProofArgContext arg : ctx.proofArg()) {
                if (arg.argLabel != null) {
                    sb.append(arg.argLabel.getText()).append("=");
                }
                sb.append(arg.token.getText()).append(" ");
            }
            sb.append(";\n");

        } else if (ctx.assertion != null) {
            sb.append("cut ").append(ctx.assertion).append(";\n");
            sb.append("branches \"push\";\n");
            sb.append("branches \"select\" child=0;\n");
            if (ctx.proofCmd().isEmpty()) {
                sb.append("auto;\n");
            } else {
                for (ProofCmdContext proofCmdContext : ctx.proofCmd()) {
                    renderProofCmd(proofCmdContext, sb);
                }
            }
            sb.append("branches \"select\" child=1;\n");
            sb.append("branches \"pop\";\n");

        } else if (!ctx.proofCmdCase().isEmpty()) {
            sb.append("branches \"push\";\n");
            int no = 0;
            for (ProofCmdCaseContext caseContext : ctx.proofCmdCase()) {
                if (caseContext.STRING_LITERAL() != null) {
                    sb.append("branches \"select\" branch=")
                            .append(caseContext.STRING_LITERAL().getText()).append(";\n");
                } else {
                    sb.append("branches \"select\" child=").append(no++).append(";\n");
                }
                for (ProofCmdContext proofCmdContext : caseContext.proofCmd()) {
                    renderProofCmd(proofCmdContext, sb);
                }
            }
            sb.append("branches \"pop\";\n");
        }

    }
}
