package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertFalse;

import java.io.File;
import java.io.IOException;
import java.io.Serializable;
import java.util.List;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader.ReplayResult;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsDirectories;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest;
import de.uka.ilkd.key.proof.runallproofs.TestResult;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.util.Pair;

/**
 * Data structure for .key-files that will be tested during
 * {@link RunAllProofsTest} execution. It consists of a {@link #testProperty}
 * and a {@link #path} String for the file location. Method
 * {@link #runKey(ProofCollectionSettings)} will verify {@link #testProperty}
 * for the given file.
 * 
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class TestFile<Directories extends RunAllProofsDirectories> implements Serializable {

   private static final long serialVersionUID = 7779439078807127045L;

   private final TestProperty testProperty;
   private final String path;
   private final ProofCollectionSettings settings;
   
   public final Directories directories;

   /**
    * In order to ensure that the implementation is independent of working
    * directory, this method can be used to return an absolute {@link File}
    * object.
    * 
    * @param baseDirectory
    *           Base directory that will be used as start location in case given
    *           path name is a relative path.
    * @param pathName
    *           Path whose associated {@link File} object will be returned.
    * @return {@link File} object pointing to given path name relative to given
    *         base directory.
    */
   static File getAbsoluteFile(File baseDirectory, String pathName) {

      /*
       * Caller of this method must provide an absolute path as base directory.
       */
      if (!baseDirectory.isAbsolute()) {
         throw new RuntimeException("Expecting an absolute path but found: "
               + baseDirectory);
      }

      if (!baseDirectory.isDirectory()) {
         throw new RuntimeException(
               "Given file system location is not a directory: "
                     + baseDirectory);
      }

      /*
       * Initial directory is ignored in case provided path name is absolute.
       */
      File tmp = new File(pathName);
      File ret = tmp.isAbsolute() ? tmp : new File(baseDirectory, pathName);

      /*
       * Resulting file object should be absolute. This is just a safety check.
       */
      assert ret.isAbsolute() : "Expecting an absolute path but found: " + ret;

      return ret;
   }

    protected TestFile(TestProperty testProperty, String path,
            ProofCollectionSettings settings, Directories directories) {
        this.path = path;
        this.testProperty = testProperty;
        this.settings = settings;
        this.directories = directories;
    }

    public static TestFile<RunAllProofsDirectories> createInstance(
            TestProperty testProperty, String path,
            ProofCollectionSettings settings) {
        return new TestFile<>(testProperty, path,
                settings, new RunAllProofsDirectories(settings.runStart));
    }

   /**
    * Returns a {@link File} object that points to the .key file that will be
    * tested.
    * 
    * @throws IOException
    *            Is thrown in case given .key-file is not a directory or does
    *            not exist.
    */
   public File getKeYFile() throws IOException {
      File baseDirectory = settings.getGroupDirectory();
      File keyFile = getAbsoluteFile(baseDirectory, path);

      if (keyFile.isDirectory()) {
         String exceptionMessage = "Expecting a file, but found a directory: "
               + keyFile.getAbsolutePath();
         throw new IOException(exceptionMessage);
      }

      if (!keyFile.exists()) {
         String exceptionMessage = "The given file does not exist: "
               + keyFile.getAbsolutePath();
         throw new IOException(exceptionMessage);
      }

      return keyFile;
   }

   private TestResult getRunAllProofsTestResult(boolean success,
         ProofCollectionSettings settings) throws IOException {
      String message = (success ? "pass: " : "FAIL: ")
            + "Verifying property \"" + testProperty.toString().toLowerCase()
            + "\"" + (success ? " was successful " : " failed ") + "for file: "
            + getKeYFile().toString();
      return new TestResult(message, success);
   }

   /**
    * Use KeY to verify that given {@link #testProperty} holds for KeY file that
    * is at file system location specified by {@link #path} string.
    * 
    * @param settings
    *           {@link ProofCollectionSettings} object that specifies settings
    *           which will be used for the test run.
    * @return Returns a {@link TestResult} object, which consists of a boolean
    *         value indicating whether test run was successful and a message
    *         string that can be printed out on command line to inform the user
    *         about the test result.
    * @throws Exception
    *            Any exception that may occur during KeY execution will be
    *            converted into an {@link Exception} object with original
    *            exception as cause.
    */
   public TestResult runKey() throws Exception {

      boolean verbose = "true".equals(settings.get(RunAllProofsTest.VERBOSE_OUTPUT_KEY));

      // Initialize KeY settings.
      String gks = settings.getGlobalKeYSettings();
      ProofSettings.DEFAULT_SETTINGS.loadSettingsFromString(gks);
      String lks = settings.getLocalKeYSettings();
      ProofSettings.DEFAULT_SETTINGS.loadSettingsFromString(lks);

      // Name resolution for the available KeY file.
      File keyFile = getKeYFile();
      if(verbose) {
          System.err.println("Now processing file " + keyFile);
      }
      // File that the created proof will be saved to.
      File proofFile = new File(keyFile.getAbsolutePath() + ".proof");

      KeYEnvironment<DefaultUserInterfaceControl> env = null;
      Proof loadedProof = null;
      boolean success;
      try {
         // Initialize KeY environment and load proof.
         Pair<KeYEnvironment<DefaultUserInterfaceControl>, Pair<String, Location>> pair = load(keyFile);
         env = pair.first;
         Pair<String, Location> script = pair.second;
         loadedProof = env.getLoadedProof();

         ReplayResult replayResult = env.getReplayResult();
         if(replayResult.hasErrors() && verbose) {
             System.err.println("... error(s) while loading");
             for (Throwable error : replayResult.getErrorList()) {
                 error.printStackTrace();
             }
         }

         assertFalse("Loading problem file failed", replayResult.hasErrors());

         // For a reload test we are done at this point. Loading was successful.
         if (testProperty == TestProperty.LOADABLE) {
            if(verbose) {
               System.err.println("... success: loaded");
            }
            return getRunAllProofsTestResult(true, settings);
         }

         autoMode(env, loadedProof, script);

         success = (testProperty == TestProperty.PROVABLE) == loadedProof
               .closed();
         if(verbose) {
            System.err.println("... finished proof: " + (success ? "closed.":"open goal(s)"));
         }

         // Write statistics.
         StatisticsFile statisticsFile = settings.getStatisticsFile();
         if (statisticsFile != null) {
            statisticsFile.appendStatistics(loadedProof, keyFile);
         }

         /*
          * Testing proof reloading now. Saving and reloading proof only in case
          * it was closed and test property is PROVABLE.
          */
         reload(verbose, proofFile, loadedProof, success);
      }
      catch (Throwable t) {
         if(verbose) {
            t.printStackTrace(System.err);
         }
         throw t;
      }
      finally {
         if (loadedProof != null) {
            loadedProof.dispose();
         }
         if (env != null) {
            env.dispose();
         }
      }

      return getRunAllProofsTestResult(success, settings);
   }

    /**
     * Override this method in order to change reload behaviour.
     */
    protected void reload(boolean verbose, File proofFile, Proof loadedProof, boolean success)
            throws IOException, Exception {
        if (settings.reloadEnabled() && (testProperty == TestProperty.PROVABLE) && success) {
            // Save the available proof to a temporary file.
            loadedProof.saveToFile(proofFile);
            reloadProof(proofFile);
            if (verbose) {
                System.err.println("... success: reloaded.");
            }
        }
    }

    /**
     * By overriding this method we can change the way how we invoke automode,
     * for instance if we want to use a different strategy.
     */
    protected void autoMode(KeYEnvironment<DefaultUserInterfaceControl> env, Proof loadedProof,
            Pair<String, Location> script) throws Exception {
        // Run KeY prover.
        if (script == null) {
            // auto mode
            env.getProofControl().startAndWaitForAutoMode(loadedProof);
        } else {
            // ... script
            ProofScriptEngine pse = new ProofScriptEngine(script.first, script.second);
            pse.execute(env.getUi(), env.getLoadedProof());
        }
    }

   /*
    * has resemblances with KeYEnvironment.load ...
    */
   private Pair<KeYEnvironment<DefaultUserInterfaceControl>, Pair<String, Location>> load(File keyFile) throws ProblemLoaderException, ProofInputException {
	   KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(keyFile);
       return new Pair<>(env, env.getProofScript());
   }

   /**
    * 
    * Reload proof that was previously saved at the location corresponding to
    * the given {@link File} object.
    * 
    * @param proofFile
    *           File that contains the proof that will be (re-)loaded.
    */
   private void reloadProof(File proofFile) throws Exception {
      /*
       * Reload proof and dispose corresponding KeY environment immediately
       * afterwards. If no exception is thrown it is assumed that loading works
       * properly.
       */
      KeYEnvironment<DefaultUserInterfaceControl> proofLoadEnvironment = null;
      Proof reloadedProof = null;
      try {
         proofLoadEnvironment = KeYEnvironment.load(proofFile);

         ReplayResult result = proofLoadEnvironment.getReplayResult();
         if(result.hasErrors()) {
             List<Throwable> errorList = result.getErrorList();
             for (Throwable ex : errorList) {
                ex.printStackTrace();
             }
             throw errorList.get(0);
         }

         reloadedProof = proofLoadEnvironment.getLoadedProof();
         assertTrue("Reloaded proof did not close: " + proofFile, reloadedProof.closed());
      }
      catch (Throwable t) {
         throw new Exception(
               "Exception while loading proof (see cause for details): "
                     + proofFile, t);
      }
      finally {
         if (reloadedProof != null) {
            reloadedProof.dispose();
         }
         if (proofLoadEnvironment != null) {
            proofLoadEnvironment.dispose();
         }
      }
   }
   
   public ProofCollectionSettings getSettings() {
      return settings;
   }

}
