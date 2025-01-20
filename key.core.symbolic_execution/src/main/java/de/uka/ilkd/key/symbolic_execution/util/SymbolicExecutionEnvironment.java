/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.util;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionGoalChooser;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;

/**
 * Instances of this class are used to collect and access all relevant information for symbolic
 * execution tree extraction of {@link Proof}s via an {@link SymbolicExecutionTreeBuilder}.
 *
 * @author Martin Hentschel
 */
public class SymbolicExecutionEnvironment<U extends UserInterfaceControl>
        extends KeYEnvironment<U> {
    /**
     * The {@link SymbolicExecutionTreeBuilder} for execution tree extraction.
     */
    private final SymbolicExecutionTreeBuilder builder;

    /**
     * Constructor.
     *
     * @param environment The parent {@link KeYEnvironment}.
     * @param builder The {@link SymbolicExecutionTreeBuilder} for execution tree extraction.
     */
    public SymbolicExecutionEnvironment(KeYEnvironment<U> environment,
            SymbolicExecutionTreeBuilder builder) {
        this(environment.getUi(), environment.getInitConfig(), builder);
    }

    /**
     * Constructor.
     *
     * @param ui The {@link UserInterfaceControl} in which the {@link Proof} is loaded.
     * @param initConfig The loaded project.
     * @param builder The {@link SymbolicExecutionTreeBuilder} for execution tree extraction.
     */
    public SymbolicExecutionEnvironment(U ui, InitConfig initConfig,
            SymbolicExecutionTreeBuilder builder) {
        super(ui, initConfig);
        this.builder = builder;
    }

    /**
     * Returns the {@link SymbolicExecutionTreeBuilder} for execution tree extraction.
     *
     * @return The {@link SymbolicExecutionTreeBuilder} for execution tree extraction.
     */
    public SymbolicExecutionTreeBuilder getBuilder() {
        return builder;
    }

    /**
     * Returns the {@link Proof} of {@link #getBuilder()}.
     *
     * @return The {@link Proof} of {@link #getBuilder()}.
     */
    public Proof getProof() {
        return getBuilder().getProof();
    }

    /**
     * Configures the given {@link Proof} to use the symbolic execution strategy by reusing the
     * default {@link StrategyProperties}.
     *
     * @param proof The {@link Proof} to configure.
     * @param maximalNumberOfNodesPerBranch The maximal number of nodes per branch.
     */
    public static void configureProofForSymbolicExecution(Proof proof,
            int maximalNumberOfNodesPerBranch) {
        StrategyProperties sp =
            ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getActiveStrategyProperties();
        boolean methodTreatmentContract = StrategyProperties.METHOD_CONTRACT
                .equals(sp.get(StrategyProperties.METHOD_OPTIONS_KEY));
        boolean loopTreatmentInvariant =
            StrategyProperties.LOOP_INVARIANT.equals(sp.get(StrategyProperties.LOOP_OPTIONS_KEY));
        boolean blockTreatmentContract = StrategyProperties.BLOCK_CONTRACT_INTERNAL
                .equals(sp.get(StrategyProperties.BLOCK_OPTIONS_KEY));
        boolean aliasChecks = StrategyProperties.SYMBOLIC_EXECUTION_ALIAS_CHECK_IMMEDIATELY
                .equals(sp.get(StrategyProperties.SYMBOLIC_EXECUTION_ALIAS_CHECK_OPTIONS_KEY));
        boolean nonExecutionBranchHidingSideProofs =
            StrategyProperties.SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_SIDE_PROOF.equals(
                sp.get(
                    StrategyProperties.SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OPTIONS_KEY));
        configureProofForSymbolicExecution(proof, maximalNumberOfNodesPerBranch,
            methodTreatmentContract, loopTreatmentInvariant, blockTreatmentContract,
            nonExecutionBranchHidingSideProofs, aliasChecks);
    }

    /**
     * Configures the given {@link Proof} to use the symbolic execution strategy.
     *
     * @param proof The {@link Proof} to configure.
     * @param maximalNumberOfNodesPerBranch The maximal number of nodes per branch.
     * @param methodTreatmentContract {@code true} use operation contracts, {@code false} expand
     *        methods.
     * @param loopTreatmentInvariant {@code true} use invariants, {@code false} expand loops.
     * @param blockTreatmentContract Block contracts or expand otherwise?
     * @param nonExecutionBranchHidingSideProofs {@code true} hide non execution branch labels by
     *        side proofs, {@code false} do not hide execution branch labels.
     * @param aliasChecks Do alias checks?
     */
    public static void configureProofForSymbolicExecution(Proof proof,
            int maximalNumberOfNodesPerBranch, boolean methodTreatmentContract,
            boolean loopTreatmentInvariant, boolean blockTreatmentContract,
            boolean nonExecutionBranchHidingSideProofs, boolean aliasChecks) {
        if (proof != null) {
            StrategyProperties strategyProperties =
                SymbolicExecutionStrategy.getSymbolicExecutionStrategyProperties(true,
                    methodTreatmentContract, loopTreatmentInvariant, blockTreatmentContract,
                    nonExecutionBranchHidingSideProofs, aliasChecks);
            proof.setActiveStrategy(
                proof.getActiveStrategyFactory().create(proof, strategyProperties));
            proof.getSettings().getStrategySettings()
                    .setCustomApplyStrategyGoalChooser(new SymbolicExecutionGoalChooser());
            proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(
                new ExecutedSymbolicExecutionTreeNodesStopCondition(maximalNumberOfNodesPerBranch));
            SymbolicExecutionUtil.updateStrategySettings(proof, strategyProperties);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void dispose() {
        Proof proof = getProof();
        if (builder != null) {
            builder.dispose();
        }
        if (proof != null && !proof.isDisposed() && proof != getLoadedProof()) {
            proof.dispose();
        }
        super.dispose();
    }
}
