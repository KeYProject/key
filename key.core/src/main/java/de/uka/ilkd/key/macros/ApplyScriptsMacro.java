/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.util.*;
import java.util.ArrayList;
import java.util.stream.Collectors;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.JmlAssert;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.ProgVarReplacer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.prover.impl.DefaultTaskStartedInfo;
import de.uka.ilkd.key.rule.JmlAssertBuiltInRuleApp;
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.scripts.ScriptCommandAst;
import de.uka.ilkd.key.scripts.ScriptException;
import de.uka.ilkd.key.speclang.njml.JmlLexer;
import de.uka.ilkd.key.speclang.njml.JmlParser;
import de.uka.ilkd.key.speclang.njml.JmlParser.ProofArgContext;
import de.uka.ilkd.key.speclang.njml.JmlParser.ProofCmdCaseContext;
import de.uka.ilkd.key.speclang.njml.JmlParser.ProofCmdContext;

import org.key_project.logic.Term;
import org.key_project.prover.engine.ProverTaskListener;
import org.key_project.prover.engine.TaskStartedInfo;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.StringUtil;

import org.antlr.v4.runtime.ParserRuleContext;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ApplyScriptsMacro extends AbstractProofMacro {

    private static final Logger LOGGER = LoggerFactory.getLogger(ApplyScriptsMacro.class);

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
    public boolean canApplyTo(Proof proof, ImmutableList<@NonNull Goal> goals,
            PosInOccurrence posInOcc) {
        return fallBackMacro != null && fallBackMacro.canApplyTo(proof, goals, posInOcc)
                || goals.exists(g -> getJmlAssert(g.node()) != null);
    }

    record ObtainAwareTerm(JTerm term) {
        JTerm resolve(Map<LocationVariable, LocationVariable> obtainMap, Services services) {
            ProgVarReplacer pvr = new ProgVarReplacer(obtainMap, services);
            JTerm result = pvr.replace(term);
            assertNoObtainVarsLeft(result, obtainMap);
            return result;
        }

        private void assertNoObtainVarsLeft(JTerm term, Map<LocationVariable, LocationVariable> obtainMap) {
            var v = new DefaultVisitor() {
                @Override
                public void visit(Term visited) {
                    if(obtainMap.containsKey(term.op())) {
                        throw new RuntimeException("Use of obtain variable before it being obtained: " + term.op());
                    }
                }
            };
            term.execPreOrder(v);
        }
    }

    private static JmlAssert getJmlAssert(Node node) {
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

    private static @Nullable JTerm getUpdate(Goal goal) {
        RuleApp ruleApp = goal.node().parent().getAppliedRuleApp();
        Term appliedOn = ruleApp.posInOccurrence().subTerm();
        if (appliedOn.op() instanceof UpdateApplication) {
            return UpdateApplication.getUpdate((JTerm) appliedOn);
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

            JmlAssert jmlAssert = getJmlAssert(goal.node());
            if (jmlAssert == null) {
                laterGoals.add(goal);
                continue;
            }

            listener.taskStarted(new DefaultTaskStartedInfo(TaskStartedInfo.TaskKind.Other,
                "Running attached script from goal " + goal.node().serialNr(), 0));

            KeyAst.JMLProofScript proofScript = jmlAssert.getAssertionProof();
            Map<ParserRuleContext, JTerm> termMap = getTermMap(jmlAssert, proof.getServices());
            // We heavily rely on that variables have been computed before, otherwise this will raise an NPE.
            Map<LocationVariable, LocationVariable> obtainMap = makeObtainVarMap(jmlAssert.collectVariablesInProof(null));
            JTerm update = getUpdate(goal);
            List<ScriptCommandAst> renderedProof =
                renderProof(proofScript, termMap, update, proof.getServices());
            ProofScriptEngine pse = new ProofScriptEngine(proof);
            pse.setInitiallySelectedGoal(goal);
            pse.getStateMap().putUserData("jml.obtainVarMap", obtainMap);
            pse.getStateMap().getValueInjector().addConverter(JTerm.class, ObtainAwareTerm.class,
                    oat -> oat.resolve(obtainMap, goal.proof().getServices()));
            LOGGER.debug("---- Script");
            LOGGER.debug(renderedProof.stream().map(ScriptCommandAst::asCommandLine)
                    .collect(Collectors.joining("\n")));
            LOGGER.debug("---- End Script");

            pse.execute((AbstractUserInterfaceControl) uic, renderedProof);
        }
        listener.taskStarted(new DefaultTaskStartedInfo(TaskStartedInfo.TaskKind.Other,
            "Running fallback macro on the remaining goals", 0));
        for (Goal goal : laterGoals) {
            if (Thread.interrupted()) {
                throw new InterruptedException();
            }
            if (fallBackMacro != null) {
                fallBackMacro.applyTo(uic, proof, ImmutableList.of(goal), posInOcc, listener);
            }

        }

        return new ProofMacroFinishedInfo(this, proof);
    }


    private Map<ParserRuleContext, JTerm> getTermMap(JmlAssert jmlAssert, Services services) {
        SpecificationRepository.@Nullable JmlStatementSpec jmlspec =
            services.getSpecificationRepository().getStatementSpec(jmlAssert);
        if (jmlspec == null) {
            throw new IllegalStateException(
                "No specification found for JML assert statement at " + jmlAssert);
        }
        ImmutableList<JTerm> terms = jmlspec.terms().tail();
        ImmutableList<JmlParser.ExpressionContext> jmlExprs = jmlAssert.collectTerms().tail();
        Map<ParserRuleContext, JTerm> result = new IdentityHashMap<>();
        assert terms.size() == jmlExprs.size();
        for (int i = 0; i < terms.size(); i++) {
            result.put(jmlExprs.get(i), terms.get(i));
        }
        return result;
    }

    private Map<LocationVariable, LocationVariable> makeObtainVarMap(ImmutableList<LocationVariable> locationVariables) {
        HashMap<LocationVariable, LocationVariable> result = new HashMap<>();
        for (LocationVariable lv : locationVariables) {
            result.put(lv, null);
        }
        return result;
    }

    private static List<ScriptCommandAst> renderProof(KeyAst.JMLProofScript script,
            Map<ParserRuleContext, JTerm> termMap, JTerm update, Services services) throws ScriptException {
        List<ScriptCommandAst> result = new ArrayList<>();
        // Push current settings onto the settings stack
        result.add(new ScriptCommandAst("set", Map.of("stack", "push"), List.of()));
        for (ProofCmdContext proofCmdContext : script.ctx.proofCmd()) {
            result.addAll(renderProofCmd(proofCmdContext, termMap, update, services));
        }
        // Pop settings stack to restore old settings
        result.add(new ScriptCommandAst("set", Map.of("stack", "pop"), List.of()));
        return result;
    }

    private static List<ScriptCommandAst> renderProofCmd(ProofCmdContext ctx,
            Map<ParserRuleContext, JTerm> termMap, JTerm update, Services services) throws ScriptException {
        List<ScriptCommandAst> result = new ArrayList<>();

        // Push the current branch context
        result.add(new ScriptCommandAst("branches", Map.of(), List.of("push")));

        // Compose the command itself
        if(ctx.obtain != null) {
            ScriptCommandAst command = renderObtainCommand(ctx, termMap, update, services);
            result.add(command);
        } else {
            ScriptCommandAst command = renderRegularCommand(ctx, termMap, update, services);
            result.add(command);
        }

        // handle followup proofCmd if present
        JmlParser.ProofCmdSuffixContext suffix = ctx.proofCmdSuffix();
        if(suffix != null) {
            if (!suffix.proofCmd().isEmpty()) {
                result.add(new ScriptCommandAst("branches", Map.of(), List.of("single")));
                for (ProofCmdContext proofCmdContext : suffix.proofCmd()) {
                    result.addAll(renderProofCmd(proofCmdContext, termMap, update, services));
                }
            }

            // handle proofCmdCases if present
            for (ProofCmdCaseContext pcase : suffix.proofCmdCase()) {
                String label = StringUtil.stripQuotes(pcase.label.getText());
                result.add(new ScriptCommandAst("branches", Map.of("branch", label),
                        List.of("select")));
                for (ProofCmdContext proofCmdContext : pcase.proofCmd()) {
                    result.addAll(renderProofCmd(proofCmdContext, termMap, update, services));
                }
            }
        }

        // Pop the branch stack
        result.add(new ScriptCommandAst("branches", Map.of(), List.of("pop")));

        return result;
    }

    private static ScriptCommandAst renderObtainCommand(ProofCmdContext ctx, Map<ParserRuleContext, JTerm> termMap, JTerm update, Services services) throws ScriptException {
        Map<String, Object> named = new HashMap<>();

        String argName = switch(ctx.obtKind.getType()) {
            case JmlLexer.SUCH_THAT -> "such_that";
            case JmlLexer.EQUAL_SINGLE -> "equals";
            case JmlLexer.FROM_GOAL -> "from_goal";
            default -> throw new ScriptException("Unknown obtain kind: " + ctx.obtKind.getText());
        };

        if(ctx.expression() == null) {
            named.put(argName, true);
        } else {
            JmlParser.ExpressionContext exp = ctx.expression();
            Object value;
            if (isStringLiteral(exp)) {
                value = StringUtil.stripQuotes(exp.getText());
            } else {
                value = termMap.get(exp);
                if (update != null) {
                    // Wrap in update application if an update is present
                    value = services.getTermBuilder().apply(update, (JTerm) value);
                }
            }
            named.put(argName, value);
        }

        return new ScriptCommandAst("__obtain", named, List.of(), Location.fromToken(ctx.start));
    }

    private static @NonNull ScriptCommandAst renderRegularCommand(ProofCmdContext ctx, Map<ParserRuleContext, JTerm> termMap, JTerm update, Services services) {
        Map<String, Object> named = new HashMap<>();
        List<Object> positional = new ArrayList<>();
        for (ProofArgContext argContext : ctx.proofArg()) {
            Object value;
            JmlParser.ExpressionContext exp = argContext.expression();
            if (isStringLiteral(exp)) {
                value = StringUtil.stripQuotes(exp.getText());
            } else {
                value = termMap.get(exp);
                if (update != null) {
                    // Wrap in update application if an update is present
                    value = services.getTermBuilder().apply(update, (JTerm) value);
                }
            }
            if (argContext.argLabel != null) {
                named.put(argContext.argLabel.getText(), value);
            } else {
                positional.add(value);
            }
        }
        return new ScriptCommandAst(ctx.cmd.getText(), named, positional,
                Location.fromToken(ctx.start));
    }

    private static boolean isStringLiteral(JmlParser.ExpressionContext ctx) {
        return ctx.start == ctx.stop && ctx.start.getType() == JmlParser.STRING_LITERAL;
    }
}
