/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.Arrays;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.scripts.meta.*;

import org.key_project.prover.sequent.SequentFormula;

import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (9/8/25)
 */
public class IntegerSplitCommand implements ProofScriptCommand {
    public static final ScriptBlock DEFAULT_BLOCK = new ScriptBlock(
        List.of(new ScriptCommandAst("macro", Map.of(), List.of("auto"), null)),
        null);

    @Override
    public List<ProofScriptArgument> getArguments() {
        return ArgumentsLifter.inferScriptArguments(Parameters.class);
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl,
            ScriptCommandAst args, EngineState stateMap)
            throws ScriptException, InterruptedException {
        var params = stateMap.getValueInjector().inject(new Parameters(), args);

        var splitModes = Arrays.stream(SplitModes.values())
                .filter(it -> it.isPossible(params))
                .toList();

        if (splitModes.size() != 1) {
            throw new IllegalArgumentException("The given constellation of parameters " +
                "are not inclusive to decide which whether you want a three- or two-way integer split: "
                +
                "Identified modes are: " + splitModes);
        }

        var splitMode = splitModes.getFirst();

        var tb = stateMap.getProof().getServices().getTermBuilder();
        var intLdt = stateMap.getProof().getServices().getTypeConverter().getIntegerLDT();
        if (params.on.sort() != intLdt.targetSort()) {
            throw new IllegalStateException("The given term `arg0:(" + params.on
                + ")` should be of type " + intLdt.targetSort() + " " +
                "but was of type: " + params.on.sort());
        }

        splitMode.apply(uiControl, params, stateMap);
    }

    @Override
    public String getName() {
        return "integer-split";
    }

    @Override
    public List<String> getAliases() {
        return List.of(
            "isplit", "integerSplit");
    }

    @Override
    public String getDocumentation() {
        return "";
    }

    public static class Parameters {
        @Option("<0")
        @Nullable
        ScriptBlock lessThan0;

        @Option("=0")
        @Nullable
        ScriptBlock equals0;

        @Option(">0")
        @Nullable
        ScriptBlock greaterThan0;

        @Option("<=0")
        @Nullable
        ScriptBlock lessThanEq0;

        @Option(">=0")
        @Nullable
        ScriptBlock greaterThanEq0;

        @Argument
        @Documentation("The variable to make the case distinction on")
        @MonotonicNonNull
        JTerm on;
    }

    /**
     * Different split for integers modes.
     */
    private enum SplitModes {
        /// 0: <0, =0, >0
        TRIPLE(
                constellation(0, 0, 1, 1, 1), // <0, =0, >0
                constellation(0, 0, 0, 1, 1), // =0, >0
                constellation(0, 0, 1, 0, 1), // <0, >0
                constellation(0, 0, 1, 1, 0), // <0, =0
                constellation(0, 0, 0, 1, 0) // =0
        ) {
            @Override
            public void apply(AbstractUserInterfaceControl uiControl, Parameters params,
                    EngineState stateMap) throws ScriptException, InterruptedException {
                var tb = stateMap.getProof().getServices().getTermBuilder();
                var intLdt = stateMap.getProof().getServices().getTypeConverter().getIntegerLDT();

                var goals = stateMap.getFirstOpenAutomaticGoal().split(3);
                var lt = goals.get(0);
                var eq = goals.get(1);
                var gt = goals.get(2);

                var opLT = intLdt.getLessThan();
                var opGT = intLdt.getGreaterThan();

                lt.addFormula(new SequentFormula(tb.func(opLT, params.on, intLdt.zero())), true,
                    true);
                eq.addFormula(new SequentFormula(tb.equals(params.on, intLdt.zero())), true, true);
                gt.addFormula(new SequentFormula(tb.func(opGT, params.on, intLdt.zero())), true,
                    true);

                var engine = stateMap.getEngine();
                applyBlock(params.lessThan0, lt, uiControl, stateMap);
                applyBlock(params.equals0, eq, uiControl, stateMap);
                applyBlock(params.greaterThan0, gt, uiControl, stateMap);

                // TODO select which goal after execution?

            }
        },
        /// 1: <=0, >0
        LT_EQ(
                constellation(1, 0, 1, 0, 0), // <=0, >0
                constellation(1, 0, 0, 0, 0), // <=0, >0
                constellation(0, 0, 1, 0, 0) // <=0, >0
        ) {
            @Override
            void apply(AbstractUserInterfaceControl uiControl, Parameters params,
                    EngineState stateMap) throws ScriptException, InterruptedException {
                var tb = stateMap.getProof().getServices().getTermBuilder();
                var intLdt = stateMap.getProof().getServices().getTypeConverter().getIntegerLDT();

                var goals = stateMap.getFirstOpenAutomaticGoal().split(3);
                var ltEq = goals.get(0);
                var gt = goals.get(1);

                var opLT = intLdt.getLessOrEquals();
                var opGT = intLdt.getGreaterThan();

                ltEq.addFormula(new SequentFormula(tb.func(opLT, params.on, intLdt.zero())), true,
                    true);
                gt.addFormula(new SequentFormula(tb.func(opGT, params.on, intLdt.zero())), true,
                    true);

                applyBlock(params.lessThan0, ltEq, uiControl, stateMap);
                applyBlock(params.greaterThan0, gt, uiControl, stateMap);
                // TODO select which goal after execution?
            }
        },

        /// 2: <0, >=0
        GT_EQ(
                constellation(0, 1, 0, 1, 0), // >=0, <0
                constellation(0, 1, 0, 0, 0), // >=0
                constellation(0, 0, 0, 1, 0) // <0
        ) {
            @Override
            void apply(AbstractUserInterfaceControl uiControl, Parameters params,
                    EngineState stateMap) throws ScriptException, InterruptedException {
                var tb = stateMap.getProof().getServices().getTermBuilder();
                var intLdt = stateMap.getProof().getServices().getTypeConverter().getIntegerLDT();

                var goals = stateMap.getFirstOpenAutomaticGoal().split(3);
                var lt = goals.get(0);
                var gtEq = goals.get(1);

                var opLT = intLdt.getLessThan();
                var opGT = intLdt.getGreaterOrEquals();

                lt.addFormula(new SequentFormula(tb.func(opLT, params.on, intLdt.zero())), true,
                    true);
                gtEq.addFormula(new SequentFormula(tb.func(opGT, params.on, intLdt.zero())), true,
                    true);

                applyBlock(params.lessThan0, lt, uiControl, stateMap);
                applyBlock(params.greaterThan0, gtEq, uiControl, stateMap);
                // TODO select which goal after execution?
            }
        };

        private static void applyBlock(@Nullable ScriptBlock block, Goal goal,
                AbstractUserInterfaceControl uiControl, EngineState stateMap)
                throws ScriptException, InterruptedException {
            var block0 = block != null ? DEFAULT_BLOCK : block;
            stateMap.setGoal(goal);
            stateMap.getEngine().execute(uiControl, block0);
        }

        private final int[] allowedConstellations;

        SplitModes(int... allowedConstellations) {
            this.allowedConstellations = allowedConstellations;
            Arrays.sort(this.allowedConstellations);
        }

        /// Applies the three-way or two-way split.
        abstract void apply(AbstractUserInterfaceControl uiControl, Parameters params,
                EngineState stateMap) throws ScriptException, InterruptedException;

        /// Receives an integer encoding the nullness of the script block fields in [Parameters].
        /// Bits are as follows:
        /// 1. <=0
        /// 2. >=0
        /// 3. >0
        /// 4. <0
        /// 5. =0
        private boolean isPossible(int bits) {
            return allowedConstellations[Arrays.binarySearch(allowedConstellations, bits)] == bits;
        }

        public boolean isPossible(Parameters p) {
            var bits = new boolean[] {
                p.equals0 != null,
                p.lessThan0 != null,
                p.greaterThan0 != null,
                p.greaterThanEq0 != null,
                p.lessThanEq0 != null,
            };
            return isPossible(bitsAsInteger(bits));
        }

        private static int constellation(int... bits) {
            var i = 0;
            for (var b : bits) {
                i = (i << 1) | (b & 1);
            }
            return i;
        }

        private static int bitsAsInteger(boolean... bits) {
            var i = 0;
            for (boolean b : bits) {
                i = (i << 1) | (b ? 1 : 0);
            }
            return i;
        }
    }
}
