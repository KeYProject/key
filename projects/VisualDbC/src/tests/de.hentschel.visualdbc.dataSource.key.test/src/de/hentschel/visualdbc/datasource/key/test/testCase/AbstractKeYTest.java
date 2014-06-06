/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package de.hentschel.visualdbc.datasource.key.test.testCase;

import java.io.File;
import java.io.IOException;
import java.util.Collections;

import junit.framework.TestCase;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Path;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil;

import de.hentschel.visualdbc.datasource.key.model.KeyConnection;
import de.hentschel.visualdbc.datasource.key.test.Activator;
import de.hentschel.visualdbc.datasource.key.test.util.TestKeyUtil;
import de.hentschel.visualdbc.datasource.model.DSPackageManagement;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.test.util.ConnectionLogger;
import de.hentschel.visualdbc.datasource.test.util.TestDataSourceUtil;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
import de.hentschel.visualdbc.generation.operation.CreateOperation;
import de.hentschel.visualdbc.generation.test.util.TestGenerationUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Provides the basic functionality for tests testing a {@link KeyConnection}.
 * @author Martin Hentschel
 */
public class AbstractKeYTest extends AbstractSetupTestCase {
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
   
   /**
    * Executes a KeY connection test by extracting the test data in the 
    * new created project. After that the connection is opened to the
    * startContainerPath and compared with the expected connection.
    * Also a diagram is created from the opened key connection 
    * and compared with the expected connection.
    * @param projectName The name of the project to create.
    * @param testDataInBundle The path in the bundle to the test data.
    * @param startContainerPath The path to the container to connect to.
    * @param packageManagement The package management to use in the KeY connection
    * @param bundleId The ID of the plug-in which provides the oracle file.
    * @param oracleDataInBundle The path to the oracle file in the plug-in.
    * @throws Exception Occurred Exception.
    */
   protected void testKeyConnection(String projectName,
                                    String testDataInBundle,
                                    String startContainerPath,
                                    DSPackageManagement packageManagement,
                                    String bundleId,
                                    String oracleDataInBundle) throws Exception {
      IDSConnection currentConnection = null;
      IDSConnection expectedConnection = null;
      ConnectionLogger logger = new ConnectionLogger();
      boolean usePrettyPrinting = SymbolicExecutionUtil.isUsePrettyPrinting();
      try {
         // Disable pretty printing to make tests more robust against different term representations
         SymbolicExecutionUtil.setUsePrettyPrinting(false);
         // Create project and fill it with test data
         IProject project = TestUtilsUtil.createProject(projectName);
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, testDataInBundle, project);
         IContainer paycardFolder;
         if (startContainerPath != null) {
            paycardFolder = project.getFolder(startContainerPath);
         }
         else {
            paycardFolder = project;
         }
         TestCase.assertNotNull(paycardFolder);
         TestCase.assertTrue(paycardFolder.exists());
         // Open connection
         File location = ResourceUtil.getLocation(paycardFolder); 
         TestCase.assertNotNull(location);
         TestCase.assertTrue(location.exists() && location.isDirectory());
         currentConnection = TestKeyUtil.createKeyConnection(location, packageManagement, logger);
         if (currentConnection != null) {
            TestCase.assertTrue(currentConnection.isConnected());
         }
         else {
            TestCase.fail("Current IDSConnection is null.");
         }
         TestDataSourceUtil.compareConnectionEvents(currentConnection, logger, true, false, false);
         // Create diagram files
         IFile modelFile = paycardFolder.getFile(new Path("default.proof"));
         IFile diagramFile = paycardFolder.getFile(new Path("default.proof_diagram"));
         // Open model
         if (CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
            // Create model
            CreateOperation co = new CreateOperation(currentConnection, modelFile, diagramFile);
            co.execute(null, false);
            DbcModel model = TestGenerationUtil.openDbcModel(modelFile);
            createOracleFile(oracleDirectory, model, oracleDataInBundle);
         }
         // Load expected connection
         expectedConnection = createConnectionFromOracleFile(bundleId, oracleDataInBundle);
         // Compare connection with expected one and created diagram
         TestKeyUtil.compareModels(expectedConnection, currentConnection, modelFile, diagramFile);
      }
      finally {
         SymbolicExecutionUtil.setUsePrettyPrinting(usePrettyPrinting);
         try {
            if (currentConnection != null) {
               TestGenerationUtil.closeConnection(currentConnection);
               TestDataSourceUtil.compareConnectionEvents(currentConnection, logger, false, false, true);
               if (currentConnection != null) {
                  currentConnection.removeConnectionListener(logger);
                  TestCase.assertEquals(0, currentConnection.getConnectionListeners().length);
               }
            }
            if (expectedConnection != null) {
               TestGenerationUtil.closeConnection(expectedConnection);
            }
         }
         catch (DSException e) {
            e.printStackTrace();
            fail(e.getMessage());
         }
      }
   }

   /**
    * Creates an {@link IDSConnection} to the given oracle file.
    * @param bundleId The ID of the plug-in which provides the oracle file.
    * @param oracleDataInBundle The path to the oracle file in the plug-in.
    * @return The opened {@link IDSConnection}.
    */
   protected IDSConnection createConnectionFromOracleFile(String bundleId,
                                                          String oracleDataInBundle) {
      // Ensure that DbC Model is available in EMF
      DbcmodelPackage.eINSTANCE.getName();
      // Load EMF model
      ResourceSet rst = new ResourceSetImpl();
      Resource resource = rst.getResource(URI.createPlatformPluginURI(bundleId + "/" + oracleDataInBundle, true), true);
      assertTrue(resource.getContents().size() == 1);
      assertTrue(resource.getContents().get(0) instanceof DbcModel);
      DbcModel model = (DbcModel)resource.getContents().get(0);
      // Convert model into connection
      return TestKeyUtil.convertModelToConnection(model);
   }
}