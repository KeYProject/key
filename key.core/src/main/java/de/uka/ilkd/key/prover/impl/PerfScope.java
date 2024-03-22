/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.impl;

import java.text.DecimalFormat;
import java.text.DecimalFormatSymbols;
import java.util.Locale;
import java.util.concurrent.atomic.AtomicLong;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.SemisequentTacletAppIndex;
import de.uka.ilkd.key.proof.TacletAppIndex;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.executor.javadl.FindTacletExecutor;
import de.uka.ilkd.key.rule.executor.javadl.NoFindTacletExecutor;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;
import de.uka.ilkd.key.strategy.QueueRuleApplicationManager;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class PerfScope {
    private static final Logger LOGGER = LoggerFactory.getLogger(PerfScope.class);

    private record PerfCounter(String first, AtomicLong second) {}

    private static final PerfCounter[] PERF_COUNTERS = new PerfCounter[] {
        new PerfCounter("JavaCardDLStrategy approve", JavaCardDLStrategy.PERF_APPROVE),
        new PerfCounter("JavaCardDLStrategy instantiate", JavaCardDLStrategy.PERF_INSTANTIATE),
        new PerfCounter("JavaCardDLStrategy compute", JavaCardDLStrategy.PERF_COMPUTE),
        new PerfCounter("QueueRuleApplicationManager peek", QueueRuleApplicationManager.PERF_PEEK),
        new PerfCounter("QueueRuleApplicationManager queue ops",
            QueueRuleApplicationManager.PERF_QUEUE_OPS),
        new PerfCounter("QueueRuleApplicationManager create container",
            QueueRuleApplicationManager.PERF_CREATE_CONTAINER),
        new PerfCounter("Goal apply", ApplyStrategy.PERF_GOAL_APPLY),
        new PerfCounter("RuleApp execute", Goal.PERF_APP_EXECUTE),
        new PerfCounter("Goal setSequent", Goal.PERF_SET_SEQUENT),
        new PerfCounter("Goal update tag manager", Goal.PERF_UPDATE_TAG_MANAGER),
        new PerfCounter("Goal update rule app index", Goal.PERF_UPDATE_RULE_APP_INDEX),
        new PerfCounter("Taclet app index update", TacletAppIndex.PERF_UPDATE),
        new PerfCounter("Semi Taclet app index update remove",
            SemisequentTacletAppIndex.PERF_REMOVE),
        new PerfCounter("Semi Taclet app index update add", SemisequentTacletAppIndex.PERF_ADD),
        new PerfCounter("Semi Taclet app index update update",
            SemisequentTacletAppIndex.PERF_UPDATE),
        new PerfCounter("Taclet app index create all", TacletAppIndex.PERF_CREATE_ALL),
        new PerfCounter("Goal update listeners", Goal.PERF_UPDATE_LISTENERS),
        new PerfCounter("TacletApp execute", TacletApp.PERF_EXECUTE),
        new PerfCounter("TacletApp pre", TacletApp.PERF_PRE),
        new PerfCounter("TacletApp Goal setSequent", TacletApp.PERF_SET_SEQUENT),
        new PerfCounter("NoFindTacletExecutor apply", NoFindTacletExecutor.PERF_APPLY),
        new PerfCounter("NoFindTacletExecutor setSequent", NoFindTacletExecutor.PERF_SET_SEQUENT),
        new PerfCounter("NoFindTacletExecutor term labels", NoFindTacletExecutor.PERF_TERM_LABELS),
        new PerfCounter("FindTacletExecutor apply", FindTacletExecutor.PERF_APPLY),
        new PerfCounter("FindTacletExecutor setSequent", FindTacletExecutor.PERF_SET_SEQUENT),
        new PerfCounter("FindTacletExecutor term labels", FindTacletExecutor.PERF_TERM_LABELS),
        new PerfCounter("AbstractBuiltInRuleApp execute", AbstractBuiltInRuleApp.PERF_EXECUTE),
        new PerfCounter("AbstractBuiltInRuleApp Goal setSequent",
            AbstractBuiltInRuleApp.PERF_SET_SEQUENT),
    };
    private static final DecimalFormat DECIMAL_FORMAT =
        new DecimalFormat("#.##", DecimalFormatSymbols.getInstance(Locale.ENGLISH));

    private final long timeNs = System.nanoTime();
    private final long[] timesBefore = new long[PERF_COUNTERS.length];

    public PerfScope() {
        for (int i = 0; i < PERF_COUNTERS.length; i++) {
            timesBefore[i] = PERF_COUNTERS[i].second.get();
        }
    }

    public static String formatTime(long dt) {
        String unit;
        double time;
        if (dt < 1000000) {
            time = dt / 1e3;
            unit = "ns";
        } else if (dt < 1000000000) {
            time = dt / 1e6;
            unit = "ms";
        } else {
            time = dt / 1e9;
            unit = "s";
        }

        return DECIMAL_FORMAT.format(time) + unit;
    }

    private static void displayTime(String name, long dt) {
        LOGGER.trace(name + ": " + formatTime(dt));
    }

    public void report() {
        displayTime("Total", System.nanoTime() - timeNs);

        for (int i = 0; i < PERF_COUNTERS.length; i++) {
            var perf = PERF_COUNTERS[i];
            long timeBefore = timesBefore[i];
            var dt = perf.second.getAndSet(0) - timeBefore;
            displayTime(perf.first, dt);
        }
    }
}
