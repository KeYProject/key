/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.contractcompletions;

import de.uka.ilkd.key.gui.fx.InteractiveRuleApplicationCompletionF;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.statement.MethodFrame;
import de.uka.ilkd.key.java.ast.statement.While;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.LoopScopeInvariantRule;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.speclang.LoopSpecImpl;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.prover.rules.RuleAbortException;

/**
 * contractcompletions (P2b): JavaFX port of the Swing {@code LoopInvariantRuleCompletion}
 * (LoopInvariantRuleCompletion.java, 94 lines) — the interactive completion of a loop invariant
 * rule application via {@link InvariantConfiguratorF}. The logic is Swing-free; only the dialog
 * differs.
 */
public class LoopInvariantRuleCompletionF implements InteractiveRuleApplicationCompletionF {

    @Override
    public IBuiltInRuleApp complete(IBuiltInRuleApp app, Goal goal, boolean forced) {
        Services services = goal.proof().getServices();
        services = services.getOverlay(goal.getLocalNamespaces());

        LoopInvariantBuiltInRuleApp loopApp =
            ((LoopInvariantBuiltInRuleApp) app).tryToInstantiate(goal);

        JTerm progPost = loopApp.programTerm();
        final While loop = loopApp.getLoopStatement();

        LoopSpecification inv = loopApp.getSpec();
        if (inv == null) { // no invariant present, get it interactively
            MethodFrame mf = JavaTools.getInnermostMethodFrame(progPost.javaBlock(), services);
            inv = new LoopSpecImpl(loop, mf == null ? null : mf.getProgramMethod(),
                mf == null || mf.getProgramMethod() == null ? null
                        : mf.getProgramMethod().getContainerType(),
                mf == null ? null
                        : MiscTools.getSelfTerm(
                            JavaTools.getInnermostMethodFrame(progPost.javaBlock(), services),
                            services),
                null);
            try {
                inv = InvariantConfiguratorF.getInstance().getLoopInvariant(inv, services, false,
                    loopApp.getHeapContext());
            } catch (RuleAbortException e) {
                return null;
            }
        } else { // in interactive mode and there is an invariant in the specification repository
            boolean requiresVariant = loopApp.variantRequired() && !loopApp.variantAvailable();
            if (!forced || !loopApp.invariantAvailable() || requiresVariant) {
                try {
                    inv = InvariantConfiguratorF.getInstance().getLoopInvariant(inv, services,
                        requiresVariant, loopApp.getHeapContext());
                } catch (RuleAbortException e) {
                    return null;
                }
            }
        }

        if (inv != null && forced) {
            services.getSpecificationRepository().addLoopInvariant(inv);
        }

        return inv == null ? null : loopApp.setLoopInvariant(inv);
    }

    @Override
    public boolean canComplete(IBuiltInRuleApp app) {
        return checkCanComplete(app);
    }

    /** Swing {@code checkCanComplete} (also used by the KeY IDE). */
    public static boolean checkCanComplete(final IBuiltInRuleApp app) {
        return app.rule() instanceof WhileInvariantRule
                || app.rule() instanceof LoopScopeInvariantRule;
    }
}
