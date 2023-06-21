package de.uka.ilkd.key.macros;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.JmlAssert;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosTableLayouter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import de.uka.ilkd.key.prover.impl.DefaultTaskStartedInfo;
import de.uka.ilkd.key.rule.JmlAssertBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.njml.JmlParser.AssertionProofContext;
import de.uka.ilkd.key.speclang.njml.JmlParser.ProofArgContext;
import de.uka.ilkd.key.speclang.njml.JmlParser.ProofCmdCaseContext;
import de.uka.ilkd.key.speclang.njml.JmlParser.ProofCmdContext;

import org.key_project.util.collection.ImmutableList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nullable;

public class ApplyScriptsMacro extends AbstractProofMacro {
    public static final Logger LOGGER = LoggerFactory.getLogger(ApplyScriptsMacro.class);

    private final @Nullable ProofMacro fallBackMacro;

    public ApplyScriptsMacro(ProofMacro fallBackMacro) {
        this.fallBackMacro = fallBackMacro;
    }

    @Override
    public String getName() {
        return "Apply scripts macro";
    }

    @Override
    public String getCategory() {
        return null;
    }

    @Override
    public String getDescription() {
        return "Apply scripts";
    }

    @Override
    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals, PosInOccurrence posInOcc) {
        return fallBackMacro != null && fallBackMacro.canApplyTo(proof, goals, posInOcc)
                || goals.exists(g -> getJmlAssert(g.node()) != null);
    }

    private static JmlAssert getJmlAssert(Node node) {
        RuleApp ruleApp = node.parent().getAppliedRuleApp();
        if (ruleApp instanceof JmlAssertBuiltInRuleApp) {
            Term target = ruleApp.posInOccurrence().subTerm();
            if (target.op() instanceof UpdateApplication) {
                target = UpdateApplication.getTarget(target);
            }
            final SourceElement activeStatement = JavaTools.getActiveStatement(target.javaBlock());
            if (activeStatement instanceof JmlAssert) {
                JmlAssert ass = (JmlAssert) activeStatement;
                if (ass.getAssertionProof() != null) {
                    return (JmlAssert) activeStatement;
                }
            }
        }
        return null;
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof,
            ImmutableList<Goal> goals, PosInOccurrence posInOcc, ProverTaskListener listener)
            throws Exception {
        ArrayList<Goal> laterGoals = new ArrayList<>(goals.size());
        for (Goal goal : goals) {
            if (Thread.interrupted()) {
                throw new InterruptedException();
            }
            JmlAssert ass = getJmlAssert(goal.node());
            if (ass == null) {
                laterGoals.add(goal);
                continue;
            }
            listener.taskStarted(new DefaultTaskStartedInfo(TaskStartedInfo.TaskKind.Other,
                "Running attached script from goal " + goal.node().serialNr(), 0));

            AssertionProofContext proofCtx = ass.getAssertionProof();
            String renderedProof = renderProof(proofCtx,
                goal.sequent().succedent().getLast().formula(), proof.getServices());

            Path script = Files.createTempFile("key.script", "key");
            Files.writeString(script, renderedProof);
            script.toFile().deleteOnExit();
            Location loc = new Location(script.toUri(), Position.UNDEFINED);
            ProofScriptEngine pse = new ProofScriptEngine(renderedProof, loc, goal);
            LOGGER.info("Running script");
            LOGGER.info(renderedProof);
            try {
                pse.execute((AbstractUserInterfaceControl) uic, proof);
            } catch (ScriptException e) {
                Position sourcePos = getSourcePos(pse);
                if(sourcePos != null) {
                    Location sloc = new Location(ass.getPositionInfo().getURI().get(), sourcePos);
                    throw new ScriptException(e.getMessage(), sloc, e);
                } else {
                    throw e;
                }
            }
        }
        listener.taskStarted(new DefaultTaskStartedInfo(TaskStartedInfo.TaskKind.Other,
            "Running fallback macro on the remaining goals", 0));
        for (Goal goal : laterGoals) {
            if (Thread.interrupted()) {
                throw new InterruptedException();
            }
            if(fallBackMacro != null) {
                fallBackMacro.applyTo(uic, proof, ImmutableList.of(goal), posInOcc, listener);
            }

        }

        return new ProofMacroFinishedInfo(this, proof);
    }

    private Position getSourcePos(ProofScriptEngine pse) {
        Object entry = pse.getStateMap().getUserData("user.sourcePos");
        if(entry == null) {
            return null;
        }
        String[] parts = entry.toString().split(" *, *");
        try {
            return Position.newOneBased(Integer.parseInt(parts[0]), Integer.parseInt(parts[1]));
        } catch (RuntimeException ex) {
            LOGGER.info("Cannot read sourcePos information", ex);
            return null;
        }
    }

    private static String renderProof(AssertionProofContext ctx, Term assertion,
            Services services) {
        StringBuilder sb = new StringBuilder();
        sb.append("@failonclosed off;\n");
        sb.append("set stack='push';\n");
        sb.append("let @assert='").append(printTerm(assertion, services)).append("';\n");
        for (ProofCmdContext proofCmdContext : ctx.proofCmd()) {
            renderProofCmd(proofCmdContext, sb);
        }
        sb.append("set stack=\"pop\";\n");
        return sb.toString();
    }

    private static void renderProofCmd(ProofCmdContext ctx, StringBuilder sb) {
        sb.append("set userKey=\"sourcePos\" value=\"" + ctx.start.getLine() + "," +
                ctx.start.getCharPositionInLine() + "\";\n");
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
            sb.append("cut ").append(ctx.assertion.getText()).append(";\n");
            sb.append("branches \"push\";\n");
            sb.append("branches \"select\" child=1;\n");
            if (ctx.proofCmd().isEmpty()) {
                sb.append("auto;\n");
            } else {
                for (ProofCmdContext proofCmdContext : ctx.proofCmd()) {
                    renderProofCmd(proofCmdContext, sb);
                }
            }
            sb.append("branches \"select\" child=0;\n");
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


    public static CharSequence printTerm(Term t, Services serv) {
        String result;

        final NotationInfo ni = new NotationInfo();
        ni.refresh(serv, false, false);

        final LogicPrinter logicPrinter =
            new LogicPrinter(ni, null, new PosTableLayouter(100, 4, true));
        logicPrinter.printTerm(t);
        result = logicPrinter.result();
        if (result.charAt(result.length() - 1) == '\n') {
            result = result.substring(0, result.length() - 1);
        }
        return result;
    }


}
