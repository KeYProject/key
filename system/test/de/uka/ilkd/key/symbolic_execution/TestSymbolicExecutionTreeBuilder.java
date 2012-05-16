package de.uka.ilkd.key.symbolic_execution;

import java.io.File;
import java.io.FileReader;
import java.io.Reader;
import java.util.Properties;

import junit.framework.TestCase;

public class TestSymbolicExecutionTreeBuilder extends TestCase {
   /**
    * The directory which contains the KeY repository.
    */
   private File keyRepDirectory;
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void setUp() throws Exception {
      super.setUp();
      // Detect the KeY repository.
      if (keyRepDirectory == null) {
         // By default the repository should be the current path.
         keyRepDirectory = new File(".");
         // But in Eclipse development like for the symbolic execution debugger it is the eclipse plug-in.
         File customTargets = new File(keyRepDirectory, "customTargets.properties"); 
         if (customTargets.isFile()) {
            // Extract repository directory from properties.
            Properties properties = new Properties();
            Reader reader = new FileReader(customTargets);
            try {
               properties.load(reader);
            }
            finally {
               reader.close();
            }
            final String KEY_REP_KEY = "key.rep";
            assertTrue("Value \"" + KEY_REP_KEY + "\" is not defined in \"" + customTargets.getAbsolutePath() + "\".", properties.containsKey(KEY_REP_KEY));
            keyRepDirectory = new File(properties.getProperty(KEY_REP_KEY));
         }
      }
      // Make sure that the KeY repository was found.
      assertNotNull("Unable to compute KeY repository directory.", keyRepDirectory);
      assertTrue("KeY repository directgory \"" + keyRepDirectory.getAbsolutePath() + "\" does not exist.", keyRepDirectory.isDirectory());
   }

   public void testFlatSteps() {
      File problemFile = new File(keyRepDirectory, "examples/set/statements/test/FlatSteps.java");
      doTest(problemFile);
   }
   
   protected void doTest(File problemFile) {
      // Make sure that parameter are valid.
      assertNotNull(problemFile);
      assertTrue(problemFile.exists());
      // Start batch mode
   }
}
