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
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.java.ast.statement.JmlAssert;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.prover.impl.DefaultTaskStartedInfo;
import de.uka.ilkd.key.rule.JmlAssertBuiltInRuleApp;
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.scripts.ScriptCommandAst;

import org.key_project.logic.op.Modality;
import org.key_project.prover.engine.ProverTaskListener;
import org.key_project.prover.engine.TaskStartedInfo;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.lookup.Property;

import org.antlr.v4.runtime.ParserRuleContext;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * A proof macro that executes JML proof scripts attached to {@code @assert} statements.
 * <p>
 * This macro processes goals that have JML assertions with embedded proof scripts.
 * For each such goal, it extracts the proof script, resolves any pending updates,
 * handles {@code obtain} variables, and executes the script commands using the
 * {@link ProofScriptEngine}. Goals without JML assertions are delegated to a
 * fallback macro if one is provided.
 * </p>
 * <p>
 * The macro supports:
 * </p>
 * <ul>
 * <li>Execution of proof commands specified in JML assertion proofs</li>
 * <li>Resolution of update applications before script execution</li>
 * <li>Handling of {@code obtain} clauses with various forms (such_that, equals, from_goal)</li>
 * <li>Branch management during script execution</li>
 * <li>Settings stack management (push/pop) to preserve prover configuration</li>
 * </ul>
 *
 * @author Mattias Ulbrich
 */

public class ApplyScriptsMacro extends AbstractProofMacro {
    private static final Logger LOGGER = LoggerFactory.getLogger(ApplyScriptsMacro.class);
    public static final Property<Map<LocationVariable, JFunction>> USER_DATA_JML_OBTAIN_VAR_MAP =
        JmlProofScriptSupport.USER_DATA_JML_OBTAIN_VAR_MAP;

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
            Map<ParserRuleContext, JTerm> termMap =
                JmlProofScriptSupport.getTermMapForAssert(jmlAssert, getJavaBlock(goal), proof.getServices());
            // We heavily rely on that variables have been computed before, otherwise this will
            // raise an NPE.
            Map<LocationVariable, JFunction> obtainMap =
                JmlProofScriptSupport.makeObtainVarMap(jmlAssert.collectVariablesInProof(null));
            OpReplacer updateReplacer = JmlProofScriptSupport.getUpdateReplacer(goal);
            List<ScriptCommandAst> renderedProof =
                JmlProofScriptSupport.renderProof(proofScript, termMap, updateReplacer, proof.getServices());
            ProofScriptEngine pse = JmlProofScriptSupport.prepareEngine(proof, goal, obtainMap);
            LOGGER.debug("---- Script");
            LOGGER.debug(renderedProof.stream()
                    .map(ScriptCommandAst::asCommandLine)
                    .collect(Collectors.joining("\n")));
            LOGGER.debug("---- End Script");

            pse.execute((AbstractUserInterfaceControl) uic, renderedProof);
        }
        listener.taskStarted(new DefaultTaskStartedInfo(TaskStartedInfo.TaskKind.Other,
            "Running fallback macro on the remaining goals", 0));

        if (Thread.interrupted()) {
            throw new InterruptedException();
        }

        if (fallBackMacro != null && !laterGoals.isEmpty()) {
            fallBackMacro.applyTo(uic, proof, ImmutableList.fromList(laterGoals), posInOcc,
                listener);
        }

        return new ProofMacroFinishedInfo(this, proof);
    }

    
}
