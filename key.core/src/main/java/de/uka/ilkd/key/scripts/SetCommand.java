/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;


import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.scripts.meta.Option;
import de.uka.ilkd.key.scripts.meta.OptionalVarargs;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;

import org.checkerframework.checker.nullness.qual.Nullable;

public class SetCommand extends AbstractCommand {
    public SetCommand() {
        super(Parameters.class);
    }

    @Override
    public void execute(ScriptCommandAst arguments) throws ScriptException, InterruptedException {
        var args = state.getValueInjector().inject(new Parameters(), arguments);

        args.settings.remove("oss");
        args.settings.remove("steps");

        final Proof proof = state.getProof();

        final StrategyProperties newProps =
            proof.getSettings().getStrategySettings().getActiveStrategyProperties();

        if (args.oneStepSimplification != null) {
            newProps.setProperty(StrategyProperties.OSS_OPTIONS_KEY,
                args.oneStepSimplification ? StrategyProperties.OSS_ON
                        : StrategyProperties.OSS_OFF);
            Strategy.updateStrategySettings(proof, newProps);
            OneStepSimplifier.refreshOSS(proof);
        }
        if (args.proofSteps != null) {
            state.setMaxAutomaticSteps(args.proofSteps);
        }

        for (var entry : args.settings.entrySet()) {
            var key = entry.getKey();
            var value = entry.getValue();

            if (!newProps.containsKey(key)) {
                throw new ScriptException("Unknown setting key: " + key);
            }
            newProps.setProperty(key, value);
        }

        updateStrategySettings(state, newProps);
    }

    /*
     * NOTE (DS, 2020-04-08): You have to update most importantly the strategy's strategy
     * properties. It does not suffice to update the proof's properties. Otherwise, changes are
     * displayed, but have no effect after a proof has already been started. For this, the following
     * quite complicated implementation, which is inspired by StrategySelectionView.
     */

    public static void updateStrategySettings(EngineState state, StrategyProperties p) {
        final Proof proof = state.getProof();
        final Strategy<Goal> strategy = getStrategy(state, p);

        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setStrategy(strategy.name());
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(p);

        proof.getSettings().getStrategySettings().setStrategy(strategy.name());
        proof.getSettings().getStrategySettings().setActiveStrategyProperties(p);

        proof.setActiveStrategy(strategy);
    }

    private static Strategy getStrategy(EngineState state, StrategyProperties properties) {
        final Profile profile = state.getProof().getServices().getProfile();
        final Proof proof = state.getProof();

        //
        for (StrategyFactory s : profile.supportedStrategies()) {
            if (state.getProof().getActiveStrategy().name().equals(s.name())) {
                return s.create(proof, properties);
            }
        }

        // (DS, 2020-04-08) This should not happen -- we already have a proof with that
        // strategy, there should be a factory for it.
        assert false;
        return null;
    }

    @Override
    public String getName() {
        return "set";
    }

    public static class Parameters {
        /**
         * One Step Simplification parameter
         */
        @Option(value = "oss")
        public @Nullable Boolean oneStepSimplification;

        /**
         * Maximum number of proof steps parameter
         */
        @Option(value = "steps")
        public @Nullable Integer proofSteps;

        /***/
        @OptionalVarargs
        public Map<String, String> settings = HashMap.newHashMap(0);
    }
}
