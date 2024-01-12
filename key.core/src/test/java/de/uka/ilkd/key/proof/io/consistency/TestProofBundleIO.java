/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io.consistency;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.ProofBundleSaver;
import de.uka.ilkd.key.proof.runallproofs.ProveTest;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.util.java.IOUtil;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.*;

/**
 * This class contains test cases for loading and saving proof bundles.
 *
 * @author Wolfram Pfeifer
 */
public class TestProofBundleIO {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProveTest.class);
    /** the resources path for this test */
    private static Path testDir;

    /** to reset the setting after the tests (usually should be false if not in GUI mode) */
    private static boolean ensureConsistency = false;

    /**
     * Set up the test path and store the current allowBundleSaving setting.
     */
    @BeforeAll
    public static void prepare() {
        testDir =
            Paths.get(HelperClassForTests.TESTCASE_DIRECTORY.getAbsolutePath(), "proofBundle");

        // remember settings to be able to reset after the test
        ensureConsistency = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                .isEnsureSourceConsistency();
    }

    /**
     * Reset settings to value before tests.
     */
    @AfterAll
    public static void cleanUp() {
        // reset the settings to value before test
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                .setEnsureSourceConsistency(ensureConsistency);
    }

    /**
     * Tests loading a *.key file, closing the proof by auto mode, and saving a bundle from it.
     * Afterwards checks that the generated bundle is loadable again. The *.key file includes
     * bootclasspath and multiple classpath statements with *.java, *.class, and *.zip files.
     *
     * @throws Exception on errors (should not happen)
     */
    @Test
    public void testComplexBundleGeneration() throws Exception {
        /*
         * size of file should be about 22 kb, to be robust against small changes (or different
         * compression), we check only for 10 kb -> not empty
         */
        Path zip = testBundleGeneration("complexBundleGeneration", 10000);

        // test that bundle is loadable again and proof is closed
        Proof proof = loadBundle(zip);
        assertNotNull(proof);
        assertTrue(proof.closed());

        // clean up
        Files.delete(zip);
    }

    /**
     * Tests loading a *.key file, closing the proof by auto mode, and saving a bundle from it.
     * Afterwards checks that the generated bundle is loadable again and that it does not contain
     * unnecessary files (no classpath, no bootclasspath). The *.key file only includes javaSource.
     *
     * @throws Exception on errors (should not happen)
     */
    @Test
    public void testSimpleBundleGeneration() throws Exception {
        /*
         * size of file should be about 2.5 kb, to be robust against small changes (or different
         * compression), we check only for 1 kb -> not empty
         */
        Path zip = testBundleGeneration("simpleBundleGeneration", 1000);

        // test that bundle is loadable again and proof is closed
        Proof proof = loadBundle(zip);
        assertNotNull(proof);
        assertTrue(proof.closed());

        Path unzip = zip.getParent().resolve("unzip");
        IOUtil.extractZip(zip, unzip);

        // test: classpath/bootclasspath empty (no such subdirectories exists)
        assertFalse(Files.exists(unzip.resolve("classpath")));
        assertFalse(Files.exists(unzip.resolve("bootclasspath")));
        assertTrue(Files.exists(unzip.resolve("src")));

        // clean up
        Files.delete(zip);
        IOUtil.delete(unzip.toFile());
    }

    /**
     * Tests that the SimpleFileRepo is able to save a proof as bundle (without consistency).
     *
     * @throws IOException on I/O errors
     */
    @Test
    public void testSimpleFileRepo() throws IOException {
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                .setEnsureSourceConsistency(false);

        AbstractFileRepo simple = new SimpleFileRepo();
        Path base = testDir.resolve("simpleBundleGeneration");

        simple.setBaseDir(base);
        simple.setJavaPath(base.resolve("src").toString());

        Path src = base.resolve("src");
        InputStream is1 = simple.getInputStream(base.resolve("test.key"));
        InputStream is2 = simple.getInputStream(src.resolve("Client.java"));
        InputStream is3 = simple.getInputStream(src.resolve("Test.java"));

        Path zip = base.resolve("test.zproof");
        simple.saveProof(zip);

        assertNotNull(is1);
        assertNotNull(is2);
        assertNotNull(is3);
        assertTrue(Files.exists(zip));

        // clean up
        is1.close();
        is2.close();
        is3.close();
        Files.delete(zip);
    }

    /**
     * Loads a proof from a bundle.
     *
     * @param p the path of the bundle
     * @return the loaded proof (currently, only a single proof is supported)
     * @throws ProblemLoaderException if loading fails
     */
    private Proof loadBundle(Path p) throws ProblemLoaderException {
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(p.toFile());
        AbstractProblemLoader.ReplayResult replayResult = env.getReplayResult();
        if (replayResult.hasErrors()) {
            LOGGER.debug("Error(s) while loading");
            for (Throwable error : replayResult.getErrorList()) {
                LOGGER.debug("Error ", error);
            }
        }
        assertNotNull(env);

        Proof proof = env.getLoadedProof();
        assertNotNull(proof);
        return proof;
    }

    /**
     * Helper method for tests. Does the following:
     * <ul>
     * <li>loads a *.key file
     * <li>tries to close the proof with auto mode
     * <li>saves proof as a bundle.
     * </ul>
     * The saved bundle is deleted afterwards.
     *
     * @param dirName the name of the directory with test resources (expects a file test.key here)
     * @param expectedSize the minimal size (in bytes) the generated bundle should have
     * @throws Exception on errors (should not happen)
     */
    private Path testBundleGeneration(String dirName, long expectedSize) throws Exception {
        // we test DiskFileRepo here!
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                .setEnsureSourceConsistency(true);

        Path path = testDir.resolve(dirName).resolve("test.key");

        // load *.key file
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(path.toFile());
        assertNotNull(env);

        Proof proof = env.getLoadedProof();
        assertNotNull(proof);

        // start auto mode (proof is closable by auto mode)
        ProofControl control = env.getProofControl();
        control.startAndWaitForAutoMode(proof);
        assertTrue(proof.closed());

        // save (closed) proof as a bundle
        Path target = testDir.resolve(dirName).resolve("test.zproof");
        ProofBundleSaver saver = new ProofBundleSaver(proof, target.toFile());
        saver.save();

        // check if target file exists and has minimum size
        assertTrue(Files.exists(target));
        assertTrue(Files.size(target) >= expectedSize);

        return target;
    }
}
