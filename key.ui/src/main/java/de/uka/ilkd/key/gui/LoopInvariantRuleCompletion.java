/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.speclang.LoopSpecImpl;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.prover.rules.RuleAbortException;

/**
 * This class completes the instantiations of the loop invariant rule applications.
 *
 * If in forced mode then the loop invariant dialog will not be shown if the supplied invariant is
 * complete.
 */
public class LoopInvariantRuleCompletion implements InteractiveRuleApplicationCompletion {

    @Override
    public IBuiltInRuleApp complete(IBuiltInRuleApp app, Goal goal, boolean forced) {
        Services services = goal.proof().getServices();
        // fixing #1090: Local variables must be accessible
        services = services.getOverlay(goal.getLocalNamespaces());

        LoopInvariantBuiltInRuleApp loopApp =
            ((LoopInvariantBuiltInRuleApp) app).tryToInstantiate(goal);

        // leading update?
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
                inv = InvariantConfigurator.getInstance().getLoopInvariant(inv, services, false,
                    loopApp.getHeapContext());
            } catch (RuleAbortException e) {
                return null;
            }
        } else { // in interactive mode and there is an invariant in the
            // repository
            boolean requiresVariant = loopApp.variantRequired() && !loopApp.variantAvailable();
            // Check if a variant is required
            if (!forced || !loopApp.invariantAvailable() || requiresVariant) {
                // get invariant or variant interactively
                try {
                    inv = InvariantConfigurator.getInstance().getLoopInvariant(inv, services,
                        requiresVariant, loopApp.getHeapContext());
                } catch (RuleAbortException e) {
                    return null;
                }
            }
        }

        if (inv != null && forced) {
            // overwrite old loop invariant in spec repo
            services.getSpecificationRepository().addLoopInvariant(inv);
        }

        return inv == null ? null : loopApp.setLoopInvariant(inv);
    }

    @Override
    public boolean canComplete(IBuiltInRuleApp app) {
        return checkCanComplete(app);
    }

    /**
     * Checks if the app is supported. This functionality is also used by the Eclipse plug-ins like
     * the KeYIDE.
     */
    public static boolean checkCanComplete(final IBuiltInRuleApp app) {
        return app.rule() instanceof WhileInvariantRule
                || app.rule() instanceof LoopScopeInvariantRule;
    }
}
