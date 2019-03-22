package de.uka.ilkd.key.proof.io.consistency;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.nio.file.Files;
import java.nio.file.Path;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.ProofBundleSaver;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

/**
 * This class contains test cases for loading and saving proof bundles.
 *
 * @author Wolfram Pfeifer
 */
public class TestProofBundleIO {
    /** the resources path for this test */
    private static Path testDir;

    /** to reset the setting after the tests (usually should be false if not in GUI mode) */
    private static boolean allowBundleSaving = false;

    /**
     * Set up the test path and store the current allowBundleSaving setting.
     */
    @BeforeClass
    public static void prepare() {
        Path projectRoot = IOUtil.getProjectRoot(TestProofBundleIO.class).toPath();
        testDir = projectRoot.resolve("resources").resolve("testcase").resolve("proofBundle");

        // remember setting to be able to reset after the test
        allowBundleSaving = ProofIndependentSettings.DEFAULT_INSTANCE
                                                    .getGeneralSettings()
                                                    .isAllowBundleSaving();

        // ensure that allowBundleSaving is true to enable repo
        ProofIndependentSettings.DEFAULT_INSTANCE
                                .getGeneralSettings()
                                .setAllowBundleSaving(true);
    }

    /**
     * Reset allowBundleSaving setting to value before tests.
     */
    @AfterClass
    public static void cleanUp() {
        // reset the setting to value before test
        ProofIndependentSettings.DEFAULT_INSTANCE
                                .getGeneralSettings()
                                .setAllowBundleSaving(allowBundleSaving);
    }

    /**
     * Tests if:
     * <ul>
     *  <li> an existing bundle is loadable
     *  <li> the containing proof is closed
     * </ul>
     * @throws Exception on errors (should not happen)
     */
    @Test
    public void testBundleLoading() throws Exception {
        // load a bundle and test if proof is closed
        Path file = testDir.resolve("bundleLoading").resolve("loadingTest.zproof");
        Proof proof = loadBundle(file);
        assertTrue(proof.closed());
    }

    /**
     * Tests loading a *.key file, closing the proof by auto mode, and saving a bundle from it.
     * Afterwards checks that the generated bundle is loadable again.
     * The *.key file includes bootclasspath and multiple classpath statements with *.java, *.class,
     * and *.zip files.
     * @throws Exception on errors (should not happen)
     */
    @Test
    public void testComplexBundleGeneration() throws Exception {
        /* size of file should be about 22 kb,
         * to be robust against small changes (or different compression),
         * we check only for 10 kb -> not empty */
        Path zip = testBundleGeneration("complexBundleGeneration", 10000);

        // test if bundle is loadable again
        assertNotNull(loadBundle(zip));

        // clean up
        Files.delete(zip);
    }

    /**
     * Tests loading a *.key file, closing the proof by auto mode, and saving a bundle from it.
     * Afterwards checks that the generated bundle is loadable again and that it does not
     * contain unnecessary files (no classpath, no bootclasspath).
     * The *.key file only includes javaSource.
     * @throws Exception on errors (should not happen)
     */
    @Test
    public void testSimpleBundleGeneration() throws Exception {
        /* size of file should be about 2.5 kb,
         * to be robust against small changes (or different compression),
         * we check only for 1 kb -> not empty */
        Path zip = testBundleGeneration("simpleBundleGeneration", 1000);

        // test if bundle is loadable again
        assertNotNull(loadBundle(zip));

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
     * Loads a proof from a bundle.
     * @param p the path of the bundle
     * @return the loaded proof (currently, only a single proof is supported)
     * @throws ProblemLoaderException if loading fails
     */
    private Proof loadBundle(Path p) throws ProblemLoaderException {
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(p.toFile());
        assertNotNull(env);

        Proof proof = env.getLoadedProof();
        assertNotNull(proof);
        return proof;
    }

    /**
     * Helper method for tests. Does the following:
     * <ul>
     *   <li> loads a *.key file
     *   <li> tries to close the proof with auto mode
     *   <li> saves proof as a bundle.
     * </ul>
     * The saved bundle is deleted afterwards.
     * @param dirName the name of the directory with test resources (expects a file test.key here)
     * @param expectedSize the minimal size (in bytes) the generated bundle should have
     * @throws Exception on errors (should not happen)
     */
    private Path testBundleGeneration(String dirName, long expectedSize) throws Exception {
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
