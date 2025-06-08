/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.proverules;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Stream;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.mgt.LemmaJustification;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.util.HelperClassForTests;
import de.uka.ilkd.key.util.LinkedHashMap;

import org.key_project.util.helper.FindResources;

import org.jspecify.annotations.Nullable;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.TestFactory;

import static org.junit.jupiter.api.Assertions.*;

/**
 * JUnit test class for re-running taclet proofs (formerly implemented as Perl script
 * proveRules.pl). The following procedure is executed during test run:
 * <p>
 * 1) Retrieve names of all taclets that have annotation "\lemma" in their declaration. <br>
 * 2) Retrieve all names of taclets for which there is a taclet proof available. Expected file name
 * pattern is as follows: Taclet_$TACLETNAME.proof<br>
 * 3) Create a test case for each registered taclet name.<br>
 * 4) Run the test cases. Each test case will check that its corresponding taclet is annotated with
 * "\lemma" and then attempt to load the proof of the taclet.
 *
 * @author Kai Wallisch
 */
@Tag("slow")
@Tag("owntest")
public class ProveRulesTest {
    /*
     * File object pointing to directory key/key.core.test
     */
    private static final Path PROOF_DIRECTORY =
        Objects.requireNonNull(FindResources.getTacletProofsDirectory());


    public void loadTacletProof(String tacletName, Taclet taclet, @Nullable Path proofFile)
            throws Exception {
        assertNotNull(proofFile,
            "Taclet " + tacletName + " was annoted with \\lemma but no taclet proof was found.");
        assertNotNull(taclet, "Proof file " + proofFile
            + " claims that it contains a proof for taclet " + tacletName
            + " but corresponding taclet seems to be unavailable (maybe it is not annotated with \\lemma?).");
        assertInstanceOf(LemmaJustification.class, taclet.getRuleJustification(),
            "Found a taclet proof for taclet " + tacletName
                + " but the taclet is not registered as a lemma. It can be registered as a lemma by "
                + "adding annotation \\lemma to the declaration of the taclet.");
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(proofFile);
        Proof proof = env.getLoadedProof();

        KeyAst.ProofScript script = env.getProofScript();
        if (script != null) {
            ProofScriptEngine pse = new ProofScriptEngine(script);
            pse.execute(env.getUi(), proof);
        }

        assertTrue(proof.closed(), "Taclet proof of taclet " + tacletName + " did not close.");
        proof.dispose();
        env.dispose();
    }

    private static List<Path> getFilesRecursive(Path directory) throws IOException {
        assert Files.isDirectory(directory)
                : "Expecting a directory as input parameter but found: " + directory;
        List<Path> list = new LinkedList<>();
        for (Path file : Files.walk(directory).toList()) {
            if (Files.isRegularFile(file)) {
                String fileName = file.getFileName().toString();
                if (fileName.startsWith("Taclet_") && fileName.endsWith(".proof")) {
                    list.add(file);
                }
            }
        }
        return list;
    }

    @TestFactory
    public Stream<DynamicTest> data() throws ProblemLoaderException, IOException {
        assertTrue(Files.exists(PROOF_DIRECTORY),
            "Directory containing taclet proofs cannot be found at location: " + PROOF_DIRECTORY);

        /*
         * Create a set containing names of taclets that shall be proven.
         */
        Set<String> tacletNames = new LinkedHashSet<>();

        /*
         * Add all annotated taclets to set of taclet names. Corresponding JUnit test case of a
         * taclet will fail if no proof file containg a taclet proof for it can be found.
         */
        KeYEnvironment<DefaultUserInterfaceControl> env =
            HelperClassForTests.createKeYEnvironment();
        Profile p = env.getProfile();
        Map<String, Taclet> tacletObjectByTacletName = new LinkedHashMap<>();
        for (Taclet taclet : env.getInitConfig().getTaclets()) {
            if (p.getJustification(taclet) == LemmaJustification.INSTANCE) {
                String tacletName = taclet.name().toString();
                tacletNames.add(tacletName);
                tacletObjectByTacletName.put(tacletName, taclet);
            }
        }

        /*
         * Traverse proof directory and add all taclets for which a proof file can be found (proof
         * of taclet "bsum_empty" is expected to be located in a file named
         * "Taclet_bsum_empty.proof"). Corresponding JUnit test will fail if a proof for a taclet is
         * present but taclet was not annotated with "\lemma".
         */
        Map<String, Path> proofFileByTacletName = new LinkedHashMap<>();
        List<Path> proofFiles = getFilesRecursive(PROOF_DIRECTORY);
        for (Path proofFile : proofFiles) {
            String fileName = proofFile.getFileName().toString();
            // Remove Taclet_* beginning and *.proof ending from fileName.
            String tacletName = fileName.substring(7, fileName.length() - 6);
            proofFileByTacletName.put(tacletName, proofFile);
            tacletNames.add(tacletName);
        }

        /*
         * Create list of constructor parameters containig one entry for each taclet name. (that
         * means there will be one test case for each taclet)
         */
        return tacletNames.stream()
                .map(tacletName -> DynamicTest.dynamicTest(tacletName,
                    () -> loadTacletProof(tacletName,
                        tacletObjectByTacletName.get(tacletName),
                        proofFileByTacletName.get(tacletName))));
    }

}
