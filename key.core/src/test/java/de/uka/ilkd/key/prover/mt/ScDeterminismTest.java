/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Proves real example problems twice in one JVM with the single-core prover and requires the two
 * proof trees to be identical.
 * <p>
 * Proof search is meant to be reproducible: same problem, same settings, same proof. When this
 * gate fails, some part of rule selection has started to depend on an accidental order -- most
 * often the iteration order of a {@code HashMap}/{@code HashSet}, which Java does not guarantee
 * and which in practice changes with memory addresses from run to run. Such a change breaks the
 * single-core prover's reproducibility and, by the same mechanism, makes multi-core proof runs
 * diverge much more visibly. This gate catches the mistake without any threading, so its failures
 * are exactly reproducible (unlike a race).
 * <p>
 * The corpus is the affordable slice of the multi-core smoke corpus (see
 * {@code ProofCollections#smallMultiThreaded()}), favouring proofs with many branches: rule
 * selection order matters most where many rule applications compete.
 */
@Tag("slow") // ~1.5 min of proving: runs in the testMt2w CI job (see build.gradle), not in the
             // default unit suite
public class ScDeterminismTest {

    /**
     * Loading example problems mutates the global {@link ProofSettings#DEFAULT_SETTINGS} (KeY
     * applies a problem's embedded settings on load). Snapshot before, restore after, so this
     * gate does not leak settings into later tests sharing the JVM.
     */
    private static String settingsSnapshot;

    @BeforeAll
    static void snapshotSettings() {
        settingsSnapshot = ProofSettings.DEFAULT_SETTINGS.settingsToString();
    }

    @AfterAll
    static void restoreSettings() {
        ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(settingsSnapshot);
    }

    /** Paths relative to {@code key.ui/examples}; all provable, all cheap (&le; ~2s each). */
    @ParameterizedTest(name = "reproducible: {0}")
    @ValueSource(strings = {
        // quantifier / first-order rows (many competing instantiations)
        "standard_key/pred_log/tptp/SYN/SYN036p2.key",
        "standard_key/pred_log/tptp/PUZ/PUZ001p1.key",
        "standard_key/pred_log/steam1.key",
        // arithmetic / inequality simplification
        "standard_key/inEqSimp/quadraticInEq.key",
        "standard_key/inEqSimp/division.key",
        // heap and loops
        "standard_key/java_dl/arrayMax.key",
        "heap/simple/selection_sort.key",
        // contracts
        "heap/simple/dependency_contracts.key",
        "heap/list/ArrayList_get_dep.key",
        // sequences / strings
        "heap/comprehensions/sum1.key",
        "standard_key/strings/stringCompileTimeConstant2.key",
        // wide splitting (most rule-selection decisions per proof)
        "heap/list/ArrayList_add.key",
        "standard_key/java_dl/switch/large_switch.key",
        "standard_key/java_dl/polishFlagSort.key",
    })
    void singleCoreProofIsReproducible(String relPath) throws Exception {
        // This gate claims that the SINGLE-THREADED prover is reproducible, so it has to know that
        // it really proved single-threaded. The suite is pinned to it (see the root build file),
        // but the pin is a system property that the multi-core tests overwrite for their own runs;
        // one of them failing to put it back would leave this gate proving multi-core and claiming
        // the result for single-threaded. Checking here makes that a failure instead, whatever
        // order the tests run in.
        MtSwitch.assertSingleThreaded();

        final Path examples = FindResources.getExampleDirectory();
        Assumptions.assumeTrue(examples != null, "examples directory not found");
        final Path keyFile = examples.resolve(relPath);
        Assumptions.assumeTrue(Files.exists(keyFile), () -> "missing example: " + keyFile);

        final ProofFingerprint first = prove(keyFile);
        final ProofFingerprint second = prove(keyFile);

        assertTrue(first.closed, () -> relPath + " did not close (first run): " + first);
        assertTrue(second.closed, () -> relPath + " did not close (second run): " + second);
        // strict equality including the insertion-ordered digest: two single-core runs must
        // produce bit-for-bit the same proof tree
        assertEquals(first, second,
            () -> "Two single-core runs proved " + relPath + " DIFFERENTLY:\n  run1=" + first
                + "\n  run2=" + second + MtFailureAdvice.scDeterminism());
    }

    private static ProofFingerprint prove(Path keyFile) throws Exception {
        final KeYEnvironment<?> env = KeYEnvironment.load(keyFile);
        try {
            final Proof proof = env.getLoadedProof();
            assertNotNull(proof, () -> "no proof loaded for " + keyFile);
            final ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            starter.start();
            return ProofFingerprint.of(proof);
        } finally {
            env.dispose();
        }
    }
}
