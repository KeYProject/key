/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.statement.MethodFrame;
import de.uka.ilkd.key.java.ast.statement.While;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.speclang.LoopSpecImpl;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.prover.rules.RuleAbortException;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This class completes the instantiations of the loop invariant rule applications.
 *
 * If in forced mode then the loop invariant dialog will not be shown if the supplied invariant is
 * complete.
 */
@NullMarked
public class LoopInvariantRuleCompletion implements InteractiveRuleApplicationCompletion {

    @Override
    public @Nullable IBuiltInRuleApp complete(IBuiltInRuleApp app, Goal goal, boolean forced) {
        Services services = goal.proof().getServices();
        // fixing #1090: Local variables must be accessible
        services = services.getOverlay(goal.getLocalNamespaces());

        LoopInvariantBuiltInRuleApp loopApp =
            ((LoopInvariantBuiltInRuleApp) app).tryToInstantiate(goal);

        // leading update?
        JTerm progPost = loopApp.programTerm();
        if (progPost == null) {
            // a loop-invariant rule app always carries the loop's program term
            throw new NullPointerException("No program term available.");
        }
        final While loop = loopApp.getLoopStatement();

        LoopSpecification inv = loopApp.getSpec();
        if (inv == null) { // no invariant present, get it interactively
            MethodFrame mf = JavaTools.getInnermostMethodFrame(progPost.javaBlock(), services);
            inv = newDefaultSpec(loop, mf, services);
            var heapContext = loopApp.getHeapContext();
            if (heapContext == null) {
                // the invariant dialog enables its heap tabs from this list
                throw new NullPointerException("No heap context available.");
            }
            try {
                inv = InvariantConfigurator.getInstance().getLoopInvariant(inv, services, false,
                    heapContext);
            } catch (RuleAbortException e) {
                return null;
            }
        } else { // in interactive mode and there is an invariant in the
            // repository
            boolean requiresVariant = loopApp.variantRequired() && !loopApp.variantAvailable();
            // Check if a variant is required
            if (!forced || !loopApp.invariantAvailable() || requiresVariant) {
                // get invariant or variant interactively
                var heapContext = loopApp.getHeapContext();
                if (heapContext == null) {
                    // the invariant dialog enables its heap tabs from this list
                    throw new NullPointerException("No heap context available.");
                }
                try {
                    inv = InvariantConfigurator.getInstance().getLoopInvariant(inv, services,
                        requiresVariant, heapContext);
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

    /**
     * Creates the default loop specification used to open the interactive invariant editor.
     *
     * <p>
     * A loop without an enclosing method has no method context, so {@code pm}, {@code kjt} and
     * {@code selfTerm} are passed as {@code null}; {@link LoopSpecImpl} tolerates a missing
     * method context for a freshly created skeleton invariant (the interactive editor only
     * fills it in once a method is chosen), while the constructor declares non-null parameters,
     * suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    private static LoopSpecification newDefaultSpec(While loop, @Nullable MethodFrame mf,
            Services services) {
        IProgramMethod pm = mf == null ? null : mf.getProgramMethod();
        KeYJavaType kjt = pm == null ? null : pm.getContainerType();
        JTerm selfTerm = mf == null ? null : MiscTools.getSelfTerm(mf, services);
        return new LoopSpecImpl(loop, pm, kjt, selfTerm, null);
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
