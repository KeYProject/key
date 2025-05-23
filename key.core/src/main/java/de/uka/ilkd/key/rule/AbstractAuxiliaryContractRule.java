/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.java.statement.JavaStatement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.AuxiliaryContract;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;

/**
 * <p>
 * Rule for the application of {@link AuxiliaryContract}s.
 * </p>
 *
 * @see AbstractAuxiliaryContractBuiltInRuleApp
 *
 * @author wacker, lanzinger
 */
public abstract class AbstractAuxiliaryContractRule implements BuiltInRule {

    /**
     *
     */
    public static final String FULL_PRECONDITION_TERM_HINT = "fullPrecondition";

    /**
     *
     */
    public static final String NEW_POSTCONDITION_TERM_HINT = "newPostcondition";

    /**
     *
     * @param occurrence an occurrence.
     * @return {@code true} iff the occurrence is not at the top level in the succedent.
     */
    protected static boolean occursNotAtTopLevelInSuccedent(final PosInOccurrence occurrence) {
        return occurrence == null || !occurrence.isTopLevel() || occurrence.isInAntec();
    }

    /**
     * Adds {@code pv} to the {@code sevices}' program variable namespace.
     *
     * @param pv a variable.
     * @param services services.
     */
    protected static void register(ProgramVariable pv, Services services) {
        Namespace<IProgramVariable> progVarNames = services.getNamespaces().programVariables();
        if (pv != null && progVarNames.lookup(pv.name()) == null) {
            progVarNames.addSafely(pv);
        }
    }

    /**
     *
     * @return the instantiation from the last time this rule was applied.
     */
    public abstract Instantiation getLastInstantiation();

    /**
     *
     * @return the term on which the rule was last applied.
     */
    public abstract Term getLastFocusTerm();

    /**
     *
     * @param inst the last instantiation.
     * @see #getLastInstantiation()
     */
    protected abstract void setLastInstantiation(Instantiation inst);

    /**
     *
     * @param formula the last focus term.
     * @see #getLastFocusTerm()
     */
    protected abstract void setLastFocusTerm(Term formula);

    @Override
    public String displayName() {
        return name().toString();
    }

    @Override
    public String toString() {
        return name().toString();
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    /**
     *
     * @param localOuts a set of variables.
     * @param services services.
     * @return an anonymizing update for the specified variables.
     */
    protected static Term createLocalAnonUpdate(ImmutableSet<LocationVariable> localOuts,
            Services services) {
        Term anonUpdate = null;
        final TermBuilder tb = services.getTermBuilder();
        for (LocationVariable pv : localOuts) {
            final Name anonFuncName = new Name(tb.newName(pv.name().toString()));
            final JFunction anonFunc = new JFunction(anonFuncName, pv.sort(), true);
            services.getNamespaces().functions().addSafely(anonFunc);
            final Term elemUpd = tb.elementary(pv, tb.func(anonFunc));
            if (anonUpdate == null) {
                anonUpdate = elemUpd;
            } else {
                anonUpdate = tb.parallel(anonUpdate, elemUpd);
            }
        }

        return anonUpdate == null ? services.getTermBuilder().skip() : anonUpdate;
    }

    /**
     *
     * @param nameBase a base name.
     * @param type a type.
     * @param services services.
     * @return a new local variable with the specified base name of the specified type.
     */
    protected static LocationVariable createLocalVariable(final String nameBase,
            final KeYJavaType type, final Services services) {
        return KeYJavaASTFactory.localVariable(
            services.getVariableNamer().getTemporaryNameProposal(nameBase), type);
    }

    /**
     * This encapsulates all information from the rule application that is needed to apply the rule.
     *
     * @param update The context update.
     * @param formula The update target.
     * @param modality The contract's modality.
     * @param self The self variable.
     * @param statement The statement the contract belongs to.
     * @param context The execution context in which the block occurs.
     * @see AbstractAuxiliaryContractBuiltInRuleApp
     */
    public record Instantiation(@NonNull Term update, @NonNull Term formula,
            @NonNull Modality modality, Term self,
            @NonNull JavaStatement statement,
            ExecutionContext context) {
        public Instantiation {
            assert update != null;
            assert update.sort() == JavaDLTheory.UPDATE;
            assert formula != null;
            assert formula.sort() == JavaDLTheory.FORMULA;
            assert modality != null;
            assert statement != null;
        }

        /**
         * @return {@code true} iff the modality is transactional.
         */
        public boolean isTransactional() {
            return modality.transaction();
        }
    }

    /**
     * A builder for {@link Instantiation}s.
     */
    protected static abstract class Instantiator {

        /**
         * The formula on which the rule is to be applied.
         */
        private final Term formula;

        /**
         * The current goal.
         */
        private final Goal goal;

        /**
         * Services.
         */
        private final Services services;

        /**
         *
         * @param formula the formula on which the rule is to be applied.
         * @param goal the current goal.
         * @param services services.
         */
        public Instantiator(final Term formula, final Goal goal, final Services services) {
            this.formula = formula;
            this.goal = goal;
            this.services = services;
        }

        /**
         *
         * @return a new instantiation.
         */
        public Instantiation instantiate() {
            final Term update = extractUpdate();
            final Term target = extractUpdateTarget();
            if (!(target.op() instanceof Modality modality)) {
                return null;
            }
            final JavaStatement statement =
                getFirstStatementInPrefixWithAtLeastOneApplicableContract(modality,
                    goal);
            if (statement == null) {
                return null;
            }
            final MethodFrame frame =
                JavaTools.getInnermostMethodFrame(target.javaBlock(), services);
            final Term self = extractSelf(frame);
            final ExecutionContext context = extractExecutionContext(frame);
            return new Instantiation(update, target, modality, self, statement, context);
        }

        /**
         *
         * @return the update if {@link #formula} is an update application, {@code null} otherwise.
         */
        private Term extractUpdate() {
            if (formula.op() instanceof UpdateApplication) {
                return UpdateApplication.getUpdate(formula);
            } else {
                return services.getTermBuilder().skip();
            }
        }

        /**
         *
         * @return the update target if {@link #formula} is an update application, {@code formula}
         *         otherwise.
         */
        private Term extractUpdateTarget() {
            if (formula.op() instanceof UpdateApplication) {
                return UpdateApplication.getTarget(formula);
            } else {
                return formula;
            }
        }

        /**
         *
         * @param frame the outermost method-frame used in the formula.
         * @return the self term.
         */
        private Term extractSelf(final MethodFrame frame) {
            if (frame == null) {
                return null;
            }
            return MiscTools.getSelfTerm(frame, services);
        }

        /**
         *
         * @param frame the outermost method-frame used in the formula.
         * @return the execution context.
         */
        private static ExecutionContext extractExecutionContext(final MethodFrame frame) {
            if (frame == null) {
                return null;
            }
            return (ExecutionContext) frame.getExecutionContext();
        }

        /**
         * @param modality the contract's modality.
         * @param goal the current goal.
         * @return the first block in the java block's prefix with at least one applicable contract.
         */
        private JavaStatement getFirstStatementInPrefixWithAtLeastOneApplicableContract(
                final Modality modality, final Goal goal) {
            SourceElement element = modality.program().program().getFirstElement();
            while ((element instanceof ProgramPrefix || element instanceof CatchAllStatement)
                    && !(element instanceof StatementBlock
                            && ((StatementBlock) element).isEmpty())) {
                if (element instanceof StatementBlock && hasApplicableContracts(services,
                    (StatementBlock) element, modality.kind(), goal)) {
                    return (StatementBlock) element;
                } else if (element instanceof StatementContainer) {
                    element = ((StatementContainer) element).getStatementAt(0);
                } else {
                    element = element.getFirstElement();
                }
            }

            if (element instanceof LoopStatement) {
                if (hasApplicableContracts(services, (LoopStatement) element, modality.kind(),
                    goal)) {
                    return (LoopStatement) element;
                }
            }

            return null;
        }

        /**
         * @param services services.
         * @param element a block or loop.
         * @param modalityKind the current goal's modality kind.
         * @param goal the current goal.
         * @return {@code true} iff the block has applicable contracts.
         */
        protected abstract boolean hasApplicableContracts(final Services services,
                final JavaStatement element, final Modality.JavaModalityKind modalityKind,
                Goal goal);
    }

}
