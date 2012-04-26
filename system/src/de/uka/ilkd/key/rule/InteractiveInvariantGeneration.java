package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.InvariantConfigurator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.LoopInvariantImpl;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;

public class InteractiveInvariantGeneration implements Rule, BuiltInRule {

        public static InteractiveInvariantGeneration INSTANCE = new InteractiveInvariantGeneration();

        private static final Name NAME = new Name("Loop Invariant (Interactive)");

        private InteractiveInvariantGeneration() {
        }

        @Override
        public ImmutableList<Goal> apply(Goal goal, Services services,
                        RuleApp ruleApp) throws RuleAbortException {

                WhileInvariantRule WIR = WhileInvariantRule.INSTANCE;
                // leading update?
                Pair<Term, Term> update = WIR.applyUpdates(ruleApp.posInOccurrence().subTerm());
                final Term u = update.first;
                final Term progPost = update.second;

                // active statement must be while loop
                SourceElement activeStatement = MiscTools
                                .getActiveStatement(progPost.javaBlock());
                final While loop = (While) activeStatement;
                LoopInvariant inv = services.getSpecificationRepository()
                                .getLoopInvariant(loop);

                // The invariant could be nonexistent
                if (inv == null) {
                        inv = new LoopInvariantImpl(
                                        loop,
                                        MiscTools.getInnermostMethodFrame(progPost
                                                        .javaBlock(), services) == null ? null
                                                        : MiscTools
                                                                        .getSelfTerm(
                                                                                        MiscTools
                                                                                                        .getInnermostMethodFrame(
                                                                                                                        progPost
                                                                                                                                        .javaBlock(),
                                                                                                                        services),
                                                                                        services),
                                        (Term) null);
                }

                // Check wether termination must be proved
                boolean requiresVariant = false;
                // Check if a variant is required
                if (progPost.op() == Modality.DIA) {
                        requiresVariant = true;
                }

                LoopInvariant newInv;
                // Get the new invariantloopInvariant
                try {
                    newInv = InvariantConfigurator.getInstance().getLoopInvariant(inv,
                                services, requiresVariant);
                } catch (Exception e) {
                    throw new RuleAbortException("Lazy User!!!");
                }
                
                
                if (newInv != null) {
                        inv = newInv;
                }
                // the new Invariant is put into spec repos
                services.getSpecificationRepository().setLoopInvariant(inv);
                
                
                /**
                 * CHECK THE INVARIANT!!!!
                 */

                

                return WhileInvariantRule.INSTANCE.apply(goal, services,
                                ruleApp);
        }
        
        public String toString(){
            return NAME.toString();
        }

        @Override
        public String displayName() {
                return NAME.toString();
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public boolean isApplicable(Goal goal, PosInOccurrence pio) {

                // 1. Auto Mode? => NO
                if (MainWindow.getInstance().getMediator().autoMode()) {
                        return false;
                } else {
                        // Check if While Rule is applicable
                        WhileInvariantRule WIR = WhileInvariantRule.INSTANCE;
                        if (WIR.checkApplicability(goal, pio)) {

                                return true;

                        }
                }
                return false;
        }

}
