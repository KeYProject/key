/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.strategy.Strategy;

/**
 * The macro {@link AutoMacro} is a customizable {@link ProofMacro} for use in proof scripts. It is
 * possible to
 *
 * <ul>
 * <li>set a breakpoint statement which makes the macro stop when the breakpoint is reached (option
 * "breakpoint", default is no breakpoint),</li>
 * <li>prevent the proof from splitting (option "splits", default is true, i.e., splitting
 * allowed),</li>
 * <li>whitelist certain rule names which will always be allowed, even after a breakpoint (option
 * "whitelist", default is none, supply a comma-separated list of rule names),</li>
 * <li>limit the rule applications to those working on formulas with a modality (parameter
 * "symbex-only", default is true),</li>
 * <li>prevent the application of rules that are tagged as not "human-readable" (parameter
 * "human-readable-only", default is true).</li>
 * </ul>
 *
 * All parameters are optional, the default configuration works like the
 * {@link FinishSymbolicExecutionMacro}. The parameters mentioned above have to be prefixed with
 * "arg_" in proof scripts. From proof scripts, it is also possible (for all macros, and so also for
 * this one) to start the macro on one particular formula (via parameter "occ") and thus to realize
 * focussed applications.
 *
 * @author Dominic Steinhoefel
 */
public class AutoMacro extends StrategyProofMacro {
    /** argument name */
    private static final String BREAKPOINT_PARAM_NAME = "breakpoint";
    /** argument name */
    private static final String ALLOW_SPLITS_PARAM_NAME = "splits";
    /** argument name */
    private static final String WHITELIST_PARAM_NAME = "whitelist";
    /** argument name */
    private static final String SYMBEX_ONLY_PARAM_NAME = "symbex-only";
    /** argument name */
    private static final String ONLY_HUMAN_PARAM_NAME = "human-readable-only";

    /**
     * All names of currently implemented parameters belong here.
     */
    //@formatter:off
    private static final String[] PARAMS = { BREAKPOINT_PARAM_NAME,
        ALLOW_SPLITS_PARAM_NAME, WHITELIST_PARAM_NAME,
        SYMBEX_ONLY_PARAM_NAME, ONLY_HUMAN_PARAM_NAME, };
    //@formatter:off

    /** The breakpoint parameter: String repr. of the statements */
    private Optional<String> breakpoint = Optional.empty();
    /** True iff splits allowed. */
    private boolean allowSplits = true;
    /** Rules which never should be suppressed */
    private List<String> whitelist = new ArrayList<>();
    /** Set to true to suppress all non-symbex rules */
    private boolean symbexOnly = true;
    /** Set to true to suppress all rules tagged as "non-human readable" */
    private boolean onlyHumanReadable = true;

    @Override
    public String getCategory() {
        // This is only meant for proof scripting
        return null;
    }

    @Override
    public String getName() {
        return "Flexible Scripting Automation Macro";
    }

    @Override
    public String getScriptCommandName() {
        return "auto-macro";
    }

    @Override
    public String getDescription() {
        return "Macro with multiple options for flexible automation. "
                + "Default works as FinishSymbolicExecutionMacro.";
    }

    @Override
    public void resetParams() {
        breakpoint = Optional.empty();
        allowSplits = true;
        whitelist = new ArrayList<>();
        symbexOnly = true;
        onlyHumanReadable = true;

        super.resetParams();
    }

    @Override
    public boolean hasParameter(String paramName) {
        return Arrays.asList(PARAMS).contains(paramName);
    }

    @Override
    public void setParameter(String paramName, String paramValue)
            throws IllegalArgumentException {
        if (paramName.equals(BREAKPOINT_PARAM_NAME)) {
            breakpoint = Optional.ofNullable(paramValue);
        } else if (paramName.equals(ALLOW_SPLITS_PARAM_NAME)) {
            allowSplits = checkBoolean(ALLOW_SPLITS_PARAM_NAME, paramValue);
        } else if (paramName.equals(SYMBEX_ONLY_PARAM_NAME)) {
            symbexOnly = checkBoolean(SYMBEX_ONLY_PARAM_NAME, paramValue);
        } else if (paramName.equals(ONLY_HUMAN_PARAM_NAME)) {
            onlyHumanReadable = checkBoolean(ONLY_HUMAN_PARAM_NAME, paramValue);
        } else if (paramName.equals(WHITELIST_PARAM_NAME)) {
            whitelist = StreamSupport
                    .stream(Arrays.spliterator(paramValue.split(",")), true)
                    .collect(Collectors.toList());
        } else {
            super.setParameter(paramName, paramValue);
        }
    }

    private boolean checkBoolean(String paramName, String paramValue) {
        if (paramValue.equalsIgnoreCase("true")) {
            return true;
        } else if (paramValue.equalsIgnoreCase("false")) {
            return false;
        } else {
            throw new IllegalArgumentException(String.format(
                    "Illegal argument for boolean parameter %s: %s", paramName,
                    paramValue));
        }
    }

    @Override
    protected Strategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
        return new AutoMacroFilterStrategy(proof.getActiveStrategy(), breakpoint,
                allowSplits, whitelist, symbexOnly, onlyHumanReadable);
    }

    private static boolean isSplittingTaclet(Rule taclet) {
        return taclet instanceof Taclet
                && ((Taclet) taclet).goalTemplates().size() > 1;
    }

    /**
     * The Class FilterAppManager is a special strategy assigning to any rule
     * infinite costs if the goal has no modality
     */
    private static class AutoMacroFilterStrategy extends FilterStrategy {
        /** Name of that strategy */
        private static final Name NAME = new Name(
                AutoMacroFilterStrategy.class.getSimpleName());
        /** See in outer class. */
        private final Optional<String> breakpoint;
        /** See in outer class. */
        private final boolean allowSplits;
        /** See in outer class. */
        private final List<String> whitelist;
        /** See in outer class. */
        private final boolean symbexOnly;
        /** See in outer class. */
        private final boolean onlyHumanReadable;
        /** the modality cache used by this strategy */
        private final ModalityCache modalityCache = new ModalityCache();

        /** Signals that we already reached the breakpoint(s) */
        private boolean breakpointReached = false;

        public AutoMacroFilterStrategy(Strategy delegate,
                Optional<String> breakpoint, boolean allowSplits,
                List<String> whitelist, boolean symbexOnly,
                boolean onlyHumanReadable) {
            super(delegate);
            this.breakpoint = breakpoint;
            this.allowSplits = allowSplits;
            this.whitelist = whitelist;
            this.symbexOnly = symbexOnly;
            this.onlyHumanReadable = onlyHumanReadable;
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio,
                Goal goal) {
            if (whitelist.contains(app.rule().displayName())
                    || whitelist.contains(app.rule().name().toString())) {
                return true;
            }

            if (breakpointReached && isJavaPIO(pio)) {
                return false;
            }

            if (symbexOnly
                    && !modalityCache.hasModality(goal.node().sequent())) {
                return false;
            }

            if (onlyHumanReadable && FinishSymbolicExecutionMacro
                    .isForbiddenRule(app.rule())) {
                return false;
            }

            if (!allowSplits && isSplittingTaclet(app.rule())) {
                return false;
            }

            if (isJavaPIO(pio)) {
                final SourceElement activeStmt = //
                        JavaTools.getActiveStatement(pio.subTerm().javaBlock());
                final String currStmtString = activeStmt.toString();

                if (currStmtString != null && //
                        breakpoint.map(currStmtString::equals)
                                .orElse(false)) {
                    breakpointReached = true;
                    return false;
                }
            }

            return super.isApprovedApp(app, pio, goal);
        }

        private boolean isJavaPIO(PosInOccurrence pio) {
            return pio != null
                    && pio.subTerm().javaBlock() != JavaBlock.EMPTY_JAVABLOCK;
        }

        @Override
        public boolean isStopAtFirstNonCloseableGoal() {
            return false;
        }
    }
}