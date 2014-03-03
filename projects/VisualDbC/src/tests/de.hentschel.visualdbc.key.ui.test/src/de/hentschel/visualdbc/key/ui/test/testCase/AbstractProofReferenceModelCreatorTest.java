package de.hentschel.visualdbc.key.ui.test.testCase;

import java.io.File;
import java.io.IOException;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;

import de.hentschel.visualdbc.datasource.key.test.testCase.AbstractKeYTest;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.key.ui.test.util.TestKeYUIUtil;

public class AbstractProofReferenceModelCreatorTest extends AbstractKeYTest {
   /**
    * Compares the given {@link DbcModel} with the oracle file. 
    * @param oracleDirectory The oracle directory to create file in.
    * @param model The given {@link DbcModel} to save as oracle file.
    * @param bundleId The ID of the plug-in which contains the expected oracle file.
    * @param expectedModelPathInBundle The path in the bundle under that the created oracle file will be later available. It is used to create sub directories in temp directory.
    * @throws IOException Occurred Exception.
    */
   protected static void compareWithOracle(File oracledirectory, 
                                           DbcModel dbcModel, 
                                           String bundleId,
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
         Resource resource = rst.getResource(URI.createPlatformPluginURI(bundleId + "/" + oracleFileInBundle, true), true);
         assertEquals(1, resource.getContents().size());
         assertTrue(resource.getContents().get(0) instanceof DbcModel);
         // Compare models
         DbcModel expectedModel = (DbcModel)resource.getContents().get(0);
         TestKeYUIUtil.compareModels(expectedModel, dbcModel);
      }
   }
}
