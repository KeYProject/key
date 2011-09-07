package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import java.util.Map;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.WhileInvRule;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.LoopInvariantImpl;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.LoopInvariant;

public class InteractiveInvariantGeneration implements Rule, BuiltInRule {

        public static InteractiveInvariantGeneration INSTANCE = new InteractiveInvariantGeneration();

        private String name = "Loop Invariant - interactive";
        private String displayName = "LI";

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
                    newInv = Main.getInstance().getLoopInvariant(inv,
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

        @Override
        public String displayName() {

                return displayName;
        }

        @Override
        public Name name() {

                return name();
        }

        @Override
        public boolean isApplicable(Goal goal, PosInOccurrence pio) {

                // 1. Auto Mode? => NO
                if (Main.getInstance().mediator().autoMode()) {
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
