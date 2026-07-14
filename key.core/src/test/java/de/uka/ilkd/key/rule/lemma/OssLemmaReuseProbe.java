/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.OutputStreamProofSaver;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.taclettranslation.lemma.AutomaticProver;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Measurement probe (not a regression test) for the lemma reuse hypothesis: the
 * {@link GeneratedLemmaRegistry} acts as a result cache that the stock
 * {@link OneStepSimplifier} does not have, so one-step-simplifications whose content (formula
 * plus used context formulas) recurs within a proof would be computed once and replayed from the
 * registry afterwards.
 *
 * <p>
 * The probe runs bounded automode with the stock simplifier on a selection of example problems,
 * then keys every OSS application by the printed find formula and used context formulas — the
 * same content key the lemma registry would use — and reports total vs. distinct applications,
 * restricted to the lemma-eligible (modality-free) subset, together with the number of aggregated
 * micro steps (protocol lengths) that a cache hit would have skipped.
 *
 * <p>
 * Run with: {@code ./gradlew :key.core:runOssReuseProbe}
 */
@Tag("performance")
public class OssLemmaReuseProbe {

    private static final String[] PROBLEMS = {
        "standard_key/java_dl/arrayMax.key",
        "standard_key/java_dl/arrayUpdateSimp.key",
        "standard_key/arith/binomial1.key",
        "standard_key/arith/computation.key",
        "standard_key/arith/check_jdiv.key",
        "firstTouch/05-ReverseArray/ReverseArray.key",
        "heap/Map/existenceInfiniteMaps.key",
    };

    private static final int MAX_RULES = 20000;
    private static final long TIMEOUT_MILLIS = 120000;

    private record Row(String problem, int nodes, boolean closed, int ossApps, int eligible,
            int distinctEligible, long stepsTotal, long stepsSavable) {
    }

    @Test
    public void measureReusePotential() {
        final Path examples = FindResources.getExampleDirectory();
        assertNotNull(examples, "example directory not found");

        final List<Row> rows = new ArrayList<>();
        for (final String problem : PROBLEMS) {
            final Path file = examples.resolve(problem);
            if (!Files.exists(file)) {
                System.out.println("SKIP (not found): " + problem);
                continue;
            }
            try {
                rows.add(measure(problem, file));
            } catch (Exception e) {
                System.out.println("SKIP (failed): " + problem + " -- " + e);
            }
        }

        System.out.println();
        System.out.printf("%-45s %7s %6s %8s %9s %9s %8s %10s %10s%n", "problem", "nodes",
            "closed", "ossApps", "eligible", "distinct", "hitRate", "microSteps", "savable");
        long ossApps = 0, eligible = 0, distinct = 0, steps = 0, savable = 0;
        for (final Row r : rows) {
            System.out.printf("%-45s %7d %6s %8d %9d %9d %7.1f%% %10d %10d%n", r.problem, r.nodes,
                r.closed, r.ossApps, r.eligible, r.distinctEligible, hitRate(r), r.stepsTotal,
                r.stepsSavable);
            ossApps += r.ossApps;
            eligible += r.eligible;
            distinct += r.distinctEligible;
            steps += r.stepsTotal;
            savable += r.stepsSavable;
        }
        System.out.printf("%-45s %7s %6s %8d %9d %9d %7.1f%% %10d %10d%n", "TOTAL", "", "",
            ossApps, eligible, distinct,
            eligible == 0 ? 0.0 : 100.0 * (eligible - distinct) / eligible, steps, savable);
    }

    private static double hitRate(Row r) {
        return r.eligible == 0 ? 0.0 : 100.0 * (r.eligible - r.distinctEligible) / r.eligible;
    }

    private static Row measure(String problem, Path file) throws Exception {
        final KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(file);
        try {
            final Proof proof = env.getLoadedProof();
            assertNotNull(proof);

            final StrategyProperties sp =
                proof.getSettings().getStrategySettings().getActiveStrategyProperties();
            sp.setProperty(StrategyProperties.OSS_OPTIONS_KEY, StrategyProperties.OSS_ON);
            proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
            OneStepSimplifier.refreshOSS(proof);

            try {
                new AutomaticProver().start(proof, MAX_RULES, TIMEOUT_MILLIS);
            } catch (InterruptedException e) {
                // partial proofs are fine for the statistics
            }

            final Map<String, Integer> eligibleKeyCounts = new LinkedHashMap<>();
            final Map<String, Long> keySteps = new LinkedHashMap<>();
            int ossApps = 0;
            int eligible = 0;
            long stepsTotal = 0;

            final var nodes = proof.root().subtreeIterator();
            while (nodes.hasNext()) {
                final Node node = nodes.next();
                if (!(node.getAppliedRuleApp() instanceof OneStepSimplifierRuleApp app)) {
                    continue;
                }
                ossApps++;
                final long protocolSize = app.getProtocol() == null ? 0 : app.getProtocol().size();
                stepsTotal += protocolSize;

                final JTerm find = (JTerm) app.posInOccurrence().sequentFormula().formula();
                if (OssLemmaGenerator.containsModality(find)) {
                    continue;
                }
                eligible++;
                final String key = contentKey(proof, find, app.assumesInsts());
                eligibleKeyCounts.merge(key, 1, Integer::sum);
                keySteps.merge(key, protocolSize, Long::sum);
            }

            // micro steps that a result cache would have skipped: all but the first
            // aggregation per distinct key
            long stepsSavable = 0;
            for (final Map.Entry<String, Integer> entry : eligibleKeyCounts.entrySet()) {
                final int count = entry.getValue();
                if (count > 1) {
                    stepsSavable += keySteps.get(entry.getKey()) / count * (count - 1);
                }
            }

            return new Row(problem, proof.countNodes(), proof.closed(), ossApps, eligible,
                eligibleKeyCounts.size(), stepsTotal, stepsSavable);
        } finally {
            env.dispose();
        }
    }

    /**
     * The content key mirroring the lemma registry's reuse key: printed find formula plus the
     * used context formulas with polarity (canonically ordered).
     */
    private static String contentKey(Proof proof, JTerm find,
            Iterable<PosInOccurrence> assumesInsts) {
        final StringBuilder key = new StringBuilder();
        key.append(OutputStreamProofSaver.printTerm(find, proof.getServices()));
        if (assumesInsts != null) {
            final TreeSet<String> assumed = new TreeSet<>();
            for (final PosInOccurrence context : assumesInsts) {
                assumed.add((context.isInAntec() ? "A:" : "S:") + OutputStreamProofSaver
                        .printTerm((JTerm) context.sequentFormula().formula(),
                            proof.getServices()));
            }
            for (final String s : assumed) {
                key.append('\n').append(s);
            }
        }
        return key.toString();
    }
}
