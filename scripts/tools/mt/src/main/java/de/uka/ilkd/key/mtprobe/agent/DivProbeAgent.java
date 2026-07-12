/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.mtprobe.agent;

import java.lang.instrument.Instrumentation;

import de.uka.ilkd.key.mtprobe.ProbeSink;

import net.bytebuddy.agent.builder.AgentBuilder;
import net.bytebuddy.asm.Advice;
import net.bytebuddy.matcher.ElementMatchers;

/**
 * The Java agent. It weaves the diagnostic for the selected sites into the prover's classes when
 * they are loaded, so no prover source is changed and no rebuild of KeY is needed.
 * <p>
 * The JVM calls {@link #premain} before {@code main} runs, passing the text after {@code =} on the
 * {@code -javaagent} option (for example {@code sites=choice-point,rule-cost}). Each enabled site
 * transforms one prover method by inlining a small piece of code (an {@link Advice}) that reports
 * to {@link ProbeSink}. Because the code is inlined into the target class, it reads that class's
 * private fields directly -- no reflection.
 */
public final class DivProbeAgent {

    /** The choice-point guard (this session's OneOfCP bug tripped it). */
    private static final String BACKTRACKING_MANAGER =
        "org.key_project.prover.strategy.costbased.feature.instantiator.BackTrackingManager";
    /** The rule-application ordering (a non-total tie-break lets insertion order leak in). */
    private static final String RULE_APP_CONTAINER =
        "de.uka.ilkd.key.strategy.RuleAppContainer";

    private DivProbeAgent() {
    }

    public static void premain(String argument, Instrumentation instrumentation) {
        ProbeSink.enableSites(parseSites(argument));

        AgentBuilder builder = new AgentBuilder.Default()
                // we only add code, never change the class shape, so this stays fast and safe
                .disableClassFormatChanges()
                .with(AgentBuilder.RedefinitionStrategy.RETRANSFORMATION);

        if (ProbeSink.isEnabled("choice-point")) {
            builder = builder.type(ElementMatchers.named(BACKTRACKING_MANAGER))
                    .transform((b, type, cl, module, pd) -> b.visit(
                        Advice.to(ChoicePointAdvice.class)
                                .on(ElementMatchers.named("assertValidTicket"))));
        }
        if (ProbeSink.isEnabled("rule-cost")) {
            builder = builder.type(ElementMatchers.named(RULE_APP_CONTAINER))
                    .transform((b, type, cl, module, pd) -> b.visit(
                        Advice.to(RuleCostAdvice.class)
                                .on(ElementMatchers.named("compareTo"))));
        }

        builder.installOn(instrumentation);
        System.err.println("[mt-probe] agent installed for sites: " + ProbeSink.enabledSites());
    }

    /** Accepts either the bare list or {@code sites=<list>}. */
    private static String parseSites(String argument) {
        if (argument == null) {
            return "";
        }
        return argument.startsWith("sites=") ? argument.substring("sites=".length()) : argument;
    }
}
