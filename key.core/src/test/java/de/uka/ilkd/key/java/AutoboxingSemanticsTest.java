/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java;

import java.io.IOException;
import java.io.InputStream;
import java.net.URISyntaxException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ProofStarter;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * Runs the autoboxing semantic corpus through KeY and compares the recorded
 * verdict with the expectations shared with
 * {@code script/autoboxing/check_java_semantics.sh} (which runs the same cases
 * under javac/java 21).
 * <p>
 * Cases are recorded in {@code corpus/cases.tsv} as
 * {@code id<TAB>kind<TAB>class<TAB>method}, where {@code kind} is
 * {@link #PROVABLE} or {@link #SPLIT}.
 */
class AutoboxingSemanticsTest {
    private static final String CORPUS = "/de/uka/ilkd/key/java/autoboxing/corpus/";
    private static final String PROVABLE = "PROVABLE";
    private static final String SPLIT = "SPLIT";

    @BeforeAll
    static void enableJml() {
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings()
                .setActiveStrategyProperties(new StrategyProperties());
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setUseJML(true);
    }

    @TestFactory
    Stream<DynamicTest> corpus() throws IOException {
        List<String[]> cases = readCases();
        return cases.stream()
                .map(row -> DynamicTest.dynamicTest(row[0], () -> runCase(row)));
    }

    private static List<String[]> readCases() throws IOException {
        InputStream in = AutoboxingSemanticsTest.class.getResourceAsStream(CORPUS + "cases.tsv");
        if (in == null) {
            throw new IOException("corpus cases.tsv not found on the test classpath");
        }
        List<String[]> rows = new ArrayList<>();
        try (in) {
            String content = new String(in.readAllBytes(), StandardCharsets.UTF_8);
            for (String line : content.split("\\R")) {
                if (line.isBlank() || line.startsWith("#")) {
                    continue;
                }
                rows.add(line.split("\t"));
            }
        }
        return rows;
    }

    private static void runCase(String[] row) throws Exception {
        assertTrue(row.length >= 4,
            "cases.tsv row must have four columns: " + String.join("|", row));
        String id = row[0];
        String kind = row[1];
        String className = row[2];
        String method = row[3];

        Path source = sourcePath(id, className);
        KeYEnvironment<?> env = KeYEnvironment.load(source);
        try {
            Contract contract = env.getProofContracts().stream()
                    .filter(c -> c.getTarget() instanceof IProgramMethod pm
                            && pm.getMethodDeclaration().getName().equals(method))
                    .findFirst()
                    .orElseThrow(() -> new AssertionError(
                        "no contract for method " + method + " in " + id));
            Proof proof = env.createProof(contract.createProofObl(env.getInitConfig()));
            ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            starter.start();

            switch (kind) {
                case PROVABLE -> assertTrue(proof.closed(),
                    () -> id + " must be provable, open goals: " + proof.openGoals());
                case SPLIT -> {
                    assertFalse(proof.closed(), () -> id + " must split, but closed");
                    assertTrue(anyOpenGoalMentionsNull(proof),
                        () -> id + " must leave a null obligation, open goals: "
                            + proof.openGoals());
                }
                default -> fail("unknown corpus kind: " + kind);
            }
        } finally {
            env.dispose();
        }
    }

    private static boolean anyOpenGoalMentionsNull(Proof proof) {
        for (var goal : proof.openGoals()) {
            String label = goal.node().getNodeInfo().getBranchLabel();
            if (label != null && label.contains("Null")) {
                return true;
            }
            if (goal.sequent().succedent().isEmpty()
                    || goal.sequent().toString().contains("null")) {
                return true;
            }
        }
        return false;
    }

    private static Path sourcePath(String id, String className) throws URISyntaxException {
        var url = AutoboxingSemanticsTest.class
                .getResource(CORPUS + id + "/" + className + ".java");
        if (url == null) {
            throw new AssertionError("corpus source not found: " + id + "/" + className);
        }
        return Paths.get(url.toURI());
    }
}
