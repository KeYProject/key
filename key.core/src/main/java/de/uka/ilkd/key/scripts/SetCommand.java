/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;


import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.scripts.meta.Documentation;
import de.uka.ilkd.key.scripts.meta.Option;
import de.uka.ilkd.key.scripts.meta.OptionalVarargs;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;

import org.jspecify.annotations.Nullable;

public class SetCommand extends AbstractCommand {
    public SetCommand() {
        super(Parameters.class);
    }

    @Override
    public void execute(ScriptCommandAst arguments) throws ScriptException, InterruptedException {
        var args = state.getValueInjector().inject(new Parameters(), arguments);

        if (args.settings.isEmpty()) {
            throw new IllegalArgumentException(
                "You have to set oss, steps, stack, or key(s) and value(s).");
        }

        args.settings.remove("oss");
        args.settings.remove("steps");
        args.settings.remove("stack");

        final Proof proof = state.getProof();

        StrategyProperties newProps =
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

        if (args.stackAction != null) {
            Stack<StrategyProperties> stack =
                (Stack<StrategyProperties>) state.getUserData("settingsStack");
            if (stack == null) {
                stack = new Stack<>();
                state.putUserData("settingsStack", stack);
            }
            switch (args.stackAction) {
                case "push":
                    stack.push(newProps.clone());
                    break;
                case "pop":
                    // TODO sensible error if empty
                    var resetProps = stack.pop();
                    updateStrategySettings(state, resetProps);
                    break;
                default:
                    throw new IllegalArgumentException("stack must be either push or pop.");
            }
        } else if (args.userKey != null) {
            String[] kv = args.userKey.split(":", 2);
            if (kv.length != 2) {
                throw new IllegalArgumentException(
                    "userData must be of the form key:value. Use userData:\"myKey:myValue\".");
            }
            state.putUserData("user." + kv[0], kv[1]);
        } else {
            throw new IllegalArgumentException(
                "You have to set oss, steps, stack, or key(s) and value(s).");
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

    protected static void updateStrategySettings(EngineState state, StrategyProperties p) {
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

        @Documentation("Enable/disable one-step simplification")
        @Option(value = "oss")
        public @Nullable Boolean oneStepSimplification;

        @Documentation("Maximum number of proof steps")
        @Option(value = "steps")
        public @Nullable Integer proofSteps;

        @Documentation("key-value pairs to set")
        @OptionalVarargs
        public Map<String, String> settings = HashMap.newHashMap(0);

        @Documentation("Push or pop the current settings to/from a stack of settings (mostly used internally)")
        @Option(value = "stack")
        public @Nullable String stackAction;

        @Documentation("Set user-defined key-value pair (Syntax: userData:\"key:value\")")
        @Option(value = "userData")
        public @Nullable String userKey;

    }
}
