package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.LoopInvariantImpl;
import de.uka.ilkd.key.util.MiscTools;

/**
 * This class completes the instantiations of the loop invariant rule
 * applications.
 * 
 * If in forced mode then the loop invariant dialog will not be shown if the
 * supplied invariant is complete.
 */
public class LoopInvariantRuleCompletion implements
        InteractiveRuleApplicationCompletion {

    @Override
    public IBuiltInRuleApp complete(IBuiltInRuleApp app, Goal goal,
            boolean forced) {
        Services services = goal.proof().getServices();

        LoopInvariantBuiltInRuleApp loopApp = (LoopInvariantBuiltInRuleApp) app
                .tryToInstantiate(goal);

        // leading update?
        Term progPost = loopApp.programTerm();
        final While loop = loopApp.getLoopStatement();

        LoopInvariant inv = loopApp.getInvariant();
        final boolean isTransaction = ((Modality)loopApp.programTerm().op()).transaction();
        if (inv == null) { // no invariant present, get it interactively
            inv = new LoopInvariantImpl(loop,
                    MiscTools.getInnermostMethodFrame(progPost.javaBlock(),
                            services) == null ? null : MiscTools
                                    .getSelfTerm(MiscTools.getInnermostMethodFrame(
                                            progPost.javaBlock(), services),
                                            services), (Term) null);
            try {
                inv = InvariantConfigurator.getInstance().getLoopInvariant(inv,
                        services, false, isTransaction);
            } catch (RuleAbortException e) {
                return null;
            }
        } else { // in interactive mode and there is an invariant in the
                 // repository            
            boolean requiresVariant = loopApp.variantRequired()
                    && !loopApp.variantAvailable();
            // Check if a variant is required
            if (!forced || !loopApp.invariantAvailable() || requiresVariant) {
                // get invariant or variant interactively
                try {
                    inv = InvariantConfigurator.getInstance().getLoopInvariant(
                            inv, services, requiresVariant, isTransaction);
                } catch (RuleAbortException e) {
                    return null;
                }
            }
        }

        if (inv != null && forced) {
            // overwrite old loop invariant in spec repo
            services.getSpecificationRepository().setLoopInvariant(inv);
        }

        return inv == null ? null : loopApp.setLoopInvariant(inv);
    }

    @Override
    public boolean canComplete(IBuiltInRuleApp app) {
        return app.rule() instanceof WhileInvariantRule;
    }

}
