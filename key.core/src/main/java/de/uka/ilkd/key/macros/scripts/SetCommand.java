/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;

public class SetCommand extends AbstractCommand<SetCommand.Parameters> {

    public SetCommand() {
        super(Parameters.class);
    }

    @Override
    public Parameters evaluateArguments(EngineState state, Map<String, String> arguments)
            throws Exception {
        return state.getValueInjector().inject(this, new Parameters(), arguments);
    }

    @Override
    public void execute(Parameters args) throws ScriptException, InterruptedException {
        if (args.key == null ^ args.value == null) {
            throw new IllegalArgumentException(
                "When using key or value in a set command, you have to use both.");
        }

        final Proof proof = state.getProof();

        final StrategyProperties newProps =
            proof.getSettings().getStrategySettings().getActiveStrategyProperties();

        if (args.oneStepSimplification != null) {
            newProps.setProperty(StrategyProperties.OSS_OPTIONS_KEY,
                args.oneStepSimplification ? StrategyProperties.OSS_ON
                        : StrategyProperties.OSS_OFF);
            Strategy.updateStrategySettings(proof, newProps);
            OneStepSimplifier.refreshOSS(proof);
        } else if (args.proofSteps != null) {
            state.setMaxAutomaticSteps(args.proofSteps);
        } else if (args.key != null) {
            newProps.setProperty(args.key, args.value);
            updateStrategySettings(newProps);
        } else {
            throw new IllegalArgumentException("You have to set oss, steps, or key and value.");
        }
    }

    /*
     * NOTE (DS, 2020-04-08): You have to update most importantly the strategy's strategy
     * properties. It does not suffice to update the proof's properties. Otherwise, changes are
     * displayed, but have no effect after a proof has already been started. For this, the following
     * quite complicated implementation, which is inspired by StrategySelectionView.
     */

    private void updateStrategySettings(StrategyProperties p) {
        final Proof proof = state.getProof();
        final Strategy strategy = getStrategy(p);

        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setStrategy(strategy.name());
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(p);

        proof.getSettings().getStrategySettings().setStrategy(strategy.name());
        proof.getSettings().getStrategySettings().setActiveStrategyProperties(p);

        proof.setActiveStrategy(strategy);
    }

    private Strategy getStrategy(StrategyProperties properties) {
        final Profile profile = state.getProof().getServices().getProfile();

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
        /** One Step Simplification parameter */
        @Option(value = "oss", required = false)
        public Boolean oneStepSimplification;

        /** Maximum number of proof steps parameter */
        @Option(value = "steps", required = false)
        public Integer proofSteps;

        /** Normal key-value setting -- key */
        @Option(value = "key", required = false)
        public String key;

        /** Normal key-value setting -- value */
        @Option(value = "value", required = false)
        public String value;
    }
}
