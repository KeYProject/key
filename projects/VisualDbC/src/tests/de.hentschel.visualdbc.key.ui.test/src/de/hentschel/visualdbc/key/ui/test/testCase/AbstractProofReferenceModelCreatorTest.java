package de.hentschel.visualdbc.key.ui.test.testCase;

import java.io.File;
import java.io.IOException;
import java.util.Collections;

import junit.framework.TestCase;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;

import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.key.ui.test.Activator;
import de.hentschel.visualdbc.key.ui.test.util.TestKeYUIUtil;

/**
 * Provides the basic functionality for proof reference tests.
 * @author Martin Hentschel
 */
public class AbstractProofReferenceModelCreatorTest extends TestCase {
   /**
    * <p>
    * If this constant is {@code true} a temporary directory is created with
    * new oracle files. The developer has than to copy the new required files
    * into the plug-in so that they are used during next test execution.
    * </p>
    * <p>
    * <b>Attention: </b> It is strongly required that new test scenarios
    * are verified with the SED application. If everything is fine a new test
    * method can be added to this class and the first test execution can be
    * used to generate the required oracle file. Existing oracle files should
    * only be replaced if the functionality of the Symbolic Execution Debugger
    * has changed so that they are outdated.
    * </p>
    */
   public static final boolean CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY = false;
   
   /**
    * The used temporary oracle directory.
    */
   protected static final File oracleDirectory;

   /**
    * Creates the temporary oracle directory if required.
    */
   static {
      File directory = null;
      try {
         if (CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
            directory = IOUtil.createTempDirectory("ORACLE_DIRECTORY", StringUtil.EMPTY_STRING);
         }
      }
      catch (IOException e) {
      }
      oracleDirectory = directory;
   }
   
   /**
    * Compares the given {@link DbcModel} with the oracle file. 
    * @param oracleDirectory The oracle directory to create file in.
    * @param model The given {@link DbcModel} to save as oracle file.
    * @param expectedModelPathInBundle The path in the bundle under that the created oracle file will be later available. It is used to create sub directories in temp directory.
    * @throws IOException Occurred Exception.
    */
   protected static void compareWithOracle(File oracledirectory, 
                                           DbcModel dbcModel, 
                                           String oracleFileInBundle) throws IOException {
      // Test parameter
      assertNotNull(dbcModel);
      assertNotNull(oracleFileInBundle);
      if (CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
         // Create new oracle file if requested
         createOracleFile(oracleDirectory, dbcModel, oracleFileInBundle);
      }
      else {
         // Load expected DbcModel from oracle file
         ResourceSet rst = new ResourceSetImpl();
         Resource resource = rst.getResource(URI.createPlatformPluginURI(Activator.PLUGIN_ID + "/" + oracleFileInBundle, true), true);
         assertEquals(1, resource.getContents().size());
         assertTrue(resource.getContents().get(0) instanceof DbcModel);
         // Compare models
         DbcModel expectedModel = (DbcModel)resource.getContents().get(0);
         TestKeYUIUtil.compareModels(expectedModel, dbcModel);
      }
   }

   /**
    * Creates a new oracle file for the given {@link DbcModel}.
    * @param oracleDirectory The oracle directory to create file in.
    * @param model The given {@link DbcModel} to save as oracle file.
    * @param expectedModelPathInBundle The path in the bundle under that the created oracle file will be later available. It is used to create sub directories in temp directory.
    * @throws IOException Occurred Exception.
    */
   protected static void createOracleFile(File oracleDirectory,
                                          DbcModel model, 
                                          String expectedModelPathInBundle) throws IOException {
      // Create sub folder structure
      File oracleFile = new File(oracleDirectory, expectedModelPathInBundle);
      oracleFile.getParentFile().mkdirs();
      // Create oracle file
      ResourceSet rst = new ResourceSetImpl();
      Resource resource = rst.createResource(URI.createFileURI(oracleFile.getAbsolutePath()));
      resource.getContents().add(model);
      resource.save(Collections.EMPTY_MAP);
      // Print message to the user.
      printOracleDirectory();
   }
   
   /**
    * Prints {@link #oracleDirectory} to the user via {@link System#out}.
    */
   protected static void printOracleDirectory() {
      if (oracleDirectory != null) {
         final String HEADER_LINE = "Oracle Directory is:";
         final String PREFIX = "### ";
         final String SUFFIX = " ###";
         String path = oracleDirectory.toString();
         int length = Math.max(path.length(), HEADER_LINE.length());
         String borderLines = StringUtil.createLine("#", PREFIX.length() + length + SUFFIX.length());
         System.out.println(borderLines);
         System.out.println(PREFIX + HEADER_LINE + StringUtil.createLine(" ", length - HEADER_LINE.length()) + SUFFIX);
         System.out.println(PREFIX + path + StringUtil.createLine(" ", length - path.length()) + SUFFIX);
         System.out.println(borderLines);
      }
   }
}
