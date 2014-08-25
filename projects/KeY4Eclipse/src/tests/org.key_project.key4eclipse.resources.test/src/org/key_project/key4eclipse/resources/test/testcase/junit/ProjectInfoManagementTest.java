package org.key_project.key4eclipse.resources.test.testcase.junit;

import java.io.File;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.junit.Test;
import org.key_project.key4eclipse.resources.builder.ProofManager;
import org.key_project.key4eclipse.resources.projectinfo.AbstractContractContainer;
import org.key_project.key4eclipse.resources.projectinfo.AbstractTypeContainer;
import org.key_project.key4eclipse.resources.projectinfo.ContractInfo;
import org.key_project.key4eclipse.resources.projectinfo.MethodInfo;
import org.key_project.key4eclipse.resources.projectinfo.ObserverFunctionInfo;
import org.key_project.key4eclipse.resources.projectinfo.PackageInfo;
import org.key_project.key4eclipse.resources.projectinfo.ProjectInfo;
import org.key_project.key4eclipse.resources.projectinfo.ProjectInfoManager;
import org.key_project.key4eclipse.resources.projectinfo.TypeInfo;
import org.key_project.key4eclipse.resources.test.Activator;
import org.key_project.key4eclipse.resources.test.util.KeY4EclipseResourcesTestUtil;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests the full management of {@link ProjectInfo}s using the
 * {@link ProjectInfoManager}. This includes the update of a {@link ProjectInfo}
 * during build ({@link ProofManager}), the accessibility via the {@link ProjectInfoManager}
 * as well as loading and saving of {@link ProjectInfo}s by the {@link ProjectInfoManager}.
 * @author Martin Hentschel
 */
public class ProjectInfoManagementTest extends AbstractResourceTest {
   /**
    * Tests in particular declaring types of methods.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testDeclaringTypes() throws Exception {
      // Test empty project (step 0)
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("ProjectInfoManagementTest_testDeclaringTypes", true, true, false, 1, true, true);
      assertProjectInfo(project, "data/ProjectInfoManagementTest/delaringType/step0/oracle/step0.xml");
      IFolder srcFolder = project.getFolder("src");
      assertTrue(srcFolder.exists());
      // Add classes (step 1)
      doStep(project, srcFolder, "data/ProjectInfoManagementTest/delaringType/step1/test", "data/ProjectInfoManagementTest/delaringType/step1/oracle/step1.xml");
      // Overwrite methods to force declaring type changes (step 2)
      doStep(project, srcFolder, "data/ProjectInfoManagementTest/delaringType/step2/test", "data/ProjectInfoManagementTest/delaringType/step2/oracle/step2.xml");
   }
   
   /**
    * Tests in particular packages and types.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testPackagesAndTypes() throws Exception {
      // Test empty project (step 0)
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("ProjectInfoManagementTest_testPackagesAndTypes", true, true, false, 1, true, true);
      assertProjectInfo(project, "data/ProjectInfoManagementTest/packagesAndTypes/step0/oracle/step0.xml");
      IFolder srcFolder = project.getFolder("src");
      assertTrue(srcFolder.exists());
      // Add first class (step 1)
      doStep(project, srcFolder, "data/ProjectInfoManagementTest/packagesAndTypes/step1/test", "data/ProjectInfoManagementTest/packagesAndTypes/step1/oracle/step1.xml");
      // Add more classes on different packages (step 2)
      doStep(project, srcFolder, "data/ProjectInfoManagementTest/packagesAndTypes/step2/test", "data/ProjectInfoManagementTest/packagesAndTypes/step2/oracle/step2.xml");
      // Add more classes to existing packages (step 3)
      doStep(project, srcFolder, "data/ProjectInfoManagementTest/packagesAndTypes/step3/test", "data/ProjectInfoManagementTest/packagesAndTypes/step3/oracle/step3.xml");
      // Add remove types and packages and add new once (step 4)
      srcFolder.getFile("A.java").delete(true, null);
      srcFolder.getFile("ClassWithoutPackage.java").delete(true, null);
      srcFolder.getFile("Z.java").delete(true, null);
      srcFolder.getFolder("hello").getFile("A.java").delete(true, null);
      srcFolder.getFolder("hello").getFile("ClassInHello.java").delete(true, null);
      srcFolder.getFolder("hello").getFile("Z.java").delete(true, null);
      srcFolder.getFolder("hello").getFolder("world").getFile("ClassInHelloWorld.java").delete(true, null);
      doStep(project, srcFolder, "data/ProjectInfoManagementTest/packagesAndTypes/step4/test", "data/ProjectInfoManagementTest/packagesAndTypes/step4/oracle/step4.xml");
   }

   /**
    * Tests in particular methods.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testMethods() throws Exception {
      // Test empty project (step 0)
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("ProjectInfoManagementTest_testMethods", true, true, false, 1, true, true);
      assertProjectInfo(project, "data/ProjectInfoManagementTest/methods/step0/oracle/step0.xml");
      IFolder srcFolder = project.getFolder("src");
      assertTrue(srcFolder.exists());
      // Add empty classes in different packages (step 1)
      doStep(project, srcFolder, "data/ProjectInfoManagementTest/methods/step1/test", "data/ProjectInfoManagementTest/methods/step1/oracle/step1.xml");
      // Add first method (step 2)
      doStep(project, srcFolder, "data/ProjectInfoManagementTest/methods/step2/test", "data/ProjectInfoManagementTest/methods/step2/oracle/step2.xml");
      // Add more methods (step 3)
      doStep(project, srcFolder, "data/ProjectInfoManagementTest/methods/step3/test", "data/ProjectInfoManagementTest/methods/step3/oracle/step3.xml");
      // Add remove methods and add new once (step 4)
      doStep(project, srcFolder, "data/ProjectInfoManagementTest/methods/step4/test", "data/ProjectInfoManagementTest/methods/step4/oracle/step4.xml");
   }

   /**
    * Tests in particular method contracts.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testMethodContracts() throws Exception {
      // Test empty project (step 0)
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("ProjectInfoManagementTest_testMethodContracts", true, true, false, 1, true, true);
      assertProjectInfo(project, "data/ProjectInfoManagementTest/methodContracts/step0/oracle/step0.xml");
      IFolder srcFolder = project.getFolder("src");
      assertTrue(srcFolder.exists());
      // Add empty classes in different packages (step 1)
      doStep(project, srcFolder, "data/ProjectInfoManagementTest/methodContracts/step1/test", "data/ProjectInfoManagementTest/methodContracts/step1/oracle/step1.xml");
      // Add first contracts (step 2)
      doStep(project, srcFolder, "data/ProjectInfoManagementTest/methodContracts/step2/test", "data/ProjectInfoManagementTest/methodContracts/step2/oracle/step2.xml");
      // Add more contracts (step 3)
      doStep(project, srcFolder, "data/ProjectInfoManagementTest/methodContracts/step3/test", "data/ProjectInfoManagementTest/methodContracts/step3/oracle/step3.xml");
      // Add remove contracts and add new once (step 4)
      doStep(project, srcFolder, "data/ProjectInfoManagementTest/methodContracts/step4/test", "data/ProjectInfoManagementTest/methodContracts/step4/oracle/step4.xml");
   }

   /**
    * Tests in particular observer functions and contracts.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testObserverFunctionsAndContracts() throws Exception {
      // Test empty project (step 0)
      IProject project = KeY4EclipseResourcesTestUtil.initializeTest("ProjectInfoManagementTest_testObserverFunctionsAndContracts", true, true, false, 1, true, true);
      assertProjectInfo(project, "data/ProjectInfoManagementTest/observerFunctionsAndContracts/step0/oracle/step0.xml");
      IFolder srcFolder = project.getFolder("src");
      assertTrue(srcFolder.exists());
      // Add empty classes in different packages (step 1)
      doStep(project, srcFolder, "data/ProjectInfoManagementTest/observerFunctionsAndContracts/step1/test", "data/ProjectInfoManagementTest/observerFunctionsAndContracts/step1/oracle/step1.xml");
      // Add first observer functions and contracts (step 2)
      doStep(project, srcFolder, "data/ProjectInfoManagementTest/observerFunctionsAndContracts/step2/test", "data/ProjectInfoManagementTest/observerFunctionsAndContracts/step2/oracle/step2.xml");
      // Add more observer functions and contracts (step 3)
      doStep(project, srcFolder, "data/ProjectInfoManagementTest/observerFunctionsAndContracts/step3/test", "data/ProjectInfoManagementTest/observerFunctionsAndContracts/step3/oracle/step3.xml");
      // Add remove observer functions and contracts and add new once (step 4)
      doStep(project, srcFolder, "data/ProjectInfoManagementTest/observerFunctionsAndContracts/step4/test", "data/ProjectInfoManagementTest/observerFunctionsAndContracts/step4/oracle/step4.xml");
   }
   
   /**
    * Performs a single step.
    * @param project The {@link IProject} which contains the test data.
    * @param srcFolder The source folder within the {@link IProject}.
    * @param testDataInBundle The test data in the bundle.
    * @param oracleDataInBundle The oracle data in the bundle to compare with.
    * @throws Exception Occurred Exception.
    */
   protected static void doStep(IProject project, 
                                IFolder srcFolder, 
                                String testDataInBundle,
                                String oracleDataInBundle) throws Exception {
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, testDataInBundle, srcFolder, true);
      KeY4EclipseResourcesTestUtil.build(project);
      assertProjectInfo(project, oracleDataInBundle);
   }

   /**
    * Ensures that the {@link ProjectInfo} of the given {@link IProject}
    * is equal to the oracle file.
    * @param project The {@link IProject} to test.
    * @param expectedPathInBundle The oracle file in the bundle to compare with.
    * @throws Exception Occurred Exception.
    */
   protected static void assertProjectInfo(IProject project, 
                                           String expectedPathInBundle) throws Exception {
      // Ensure that info file exists
      IFolder proofFolder = project.getFolder(KeYResourcesUtil.PROOF_FOLDER_NAME);
      assertTrue(proofFolder.exists());
      IFile infoFile = proofFolder.getFile(ProjectInfoManager.PROJECT_INFO_FILE);
      assertTrue(infoFile.exists());
      // Test loaded info file
      ProjectInfo currentLoadedInfo = ProjectInfoManager.load(infoFile);
      ProjectInfo currentMemoryInfo = ProjectInfoManager.getInstance().getProjectInfo(project);
      if (oracleDirectory != null) {
         createOracleFile(oracleDirectory, expectedPathInBundle, infoFile);
      }
      else {
         ProjectInfo expectedInfo = ProjectInfoManager.load(BundleUtil.openInputStream(Activator.PLUGIN_ID, expectedPathInBundle));
         assertNotSame(currentLoadedInfo, currentMemoryInfo);
         assertProjectInfo(expectedInfo, currentMemoryInfo);
         assertProjectInfo(expectedInfo, currentLoadedInfo);
      }
   }
   
   /**
    * Ensures that the given {@link ProjectInfo}s are equal.
    * @param expected The expected {@link ProjectInfo}.
    * @param current The current {@link ProjectInfo}.
    */
   protected static void assertProjectInfo(ProjectInfo expected, 
                                           ProjectInfo current) {
      if (expected != null) {
         // Test project
         assertNotNull(current);
         assertNotSame(expected, current);
         // Test contained packages
         assertEquals(expected.countPackages(), current.countPackages());
         PackageInfo[] expectedPackages = expected.getPackages();
         PackageInfo[] currentPackages = current.getPackages();
         assertEquals(expectedPackages.length, currentPackages.length);
         for (int i = 0; i < expectedPackages.length; i++) {
            // Compare elements
            assertPackageInfo(expected, current, expectedPackages[i], currentPackages[i]);
            // Test other model functionality
            assertSame(expectedPackages[i], expected.getPackage(i));
            assertSame(currentPackages[i], current.getPackage(i));
            assertSame(expectedPackages[i], expected.getPackage(expectedPackages[i].getName()));
            assertSame(currentPackages[i], current.getPackage(currentPackages[i].getName()));
            assertSame(i, expected.indexOfPackage(expectedPackages[i]));
            assertSame(i, current.indexOfPackage(currentPackages[i]));
         }
      }
      else {
         assertNull(current);
      }
   }

   /**
    * Ensures that the given {@link PackageInfo}s are equal.
    * @param expectedParentProjectInfo The expected parent {@link ProjectInfo}.
    * @param currentParentProjectInfo The expected parent {@link ProjectInfo}.
    * @param expected The expected {@link PackageInfo}.
    * @param current The current {@link PackageInfo}.
    */
   protected static void assertPackageInfo(ProjectInfo expectedParentProjectInfo, 
                                           ProjectInfo currentParentProjectInfo, 
                                           PackageInfo expected, 
                                           PackageInfo current) {
      if (expected != null) {
         // Test package
         assertNotNull(current);
         assertNotSame(expected, current);
         assertSame(expectedParentProjectInfo, expected.getProjectInfo());
         assertSame(currentParentProjectInfo, current.getProjectInfo());
         assertEquals(expected.getName(), current.getName());
         assertEquals(expected.getContainer(), current.getContainer());
         // Test contained types
         assertEquals(expected.countTypes(), current.countTypes());
         TypeInfo[] expectedTypes = expected.getTypes();
         TypeInfo[] currentTypes = current.getTypes();
         assertEquals(expectedTypes.length, currentTypes.length);
         for (int i = 0; i < expectedTypes.length; i++) {
            // Compare elements
            assertTypeInfo(expectedParentProjectInfo, currentParentProjectInfo, expected, current, expectedTypes[i], currentTypes[i]);
            // Test other model functionality
            assertSame(expectedTypes[i], expected.getType(i));
            assertSame(currentTypes[i], current.getType(i));
            assertSame(expectedTypes[i], expected.getType(expectedTypes[i].getName()));
            assertSame(currentTypes[i], current.getType(currentTypes[i].getName()));
            assertSame(i, expected.indexOfType(expectedTypes[i]));
            assertSame(i, current.indexOfType(currentTypes[i]));
         }
      }
      else {
         assertNull(current);
      }
   }

   /**
    * Ensures that the given {@link TypeInfo}s are equal.
    * @param expectedParentProjectInfo The expected parent {@link ProjectInfo}.
    * @param currentParentProjectInfo The expected parent {@link ProjectInfo}.
    * @param expectedParent The expected parent {@link AbstractTypeContainer}.
    * @param currentParent The current parent {@link AbstractTypeContainer}.
    * @param expected The expected {@link TypeInfo}.
    * @param current The current {@link TypeInfo}.
    */
   protected static void assertTypeInfo(ProjectInfo expectedParentProjectInfo, 
                                        ProjectInfo currentParentProjectInfo, 
                                        AbstractTypeContainer expectedParent,
                                        AbstractTypeContainer currentParent,
                                        TypeInfo expected, 
                                        TypeInfo current) {
      if (expected != null) {
         // Test type
         assertNotNull(current);
         assertNotSame(expected, current);
         assertSame(expectedParentProjectInfo, expected.getProjectInfo());
         assertSame(currentParentProjectInfo, current.getProjectInfo());
         assertSame(expectedParent, expected.getParent());
         assertSame(currentParent, current.getParent());
         assertEquals(expected.getName(), current.getName());
         assertEquals(expected.getFile(), current.getFile());
         // Test contained types
         assertEquals(expected.countTypes(), current.countTypes());
         TypeInfo[] expectedInnerTypes = expected.getTypes();
         TypeInfo[] currentInnerTypes = current.getTypes();
         assertEquals(expectedInnerTypes.length, currentInnerTypes.length);
         for (int i = 0; i < expectedInnerTypes.length; i++) {
            // Compare elements
            assertTypeInfo(expectedParentProjectInfo, currentParentProjectInfo, expected, current, expectedInnerTypes[i], currentInnerTypes[i]);
            // Test other model functionality
            assertSame(expectedInnerTypes[i], expected.getType(i));
            assertSame(currentInnerTypes[i], current.getType(i));
            assertSame(expectedInnerTypes[i], expected.getType(expectedInnerTypes[i].getName()));
            assertSame(currentInnerTypes[i], current.getType(currentInnerTypes[i].getName()));
            assertSame(i, expected.indexOfType(expectedInnerTypes[i]));
            assertSame(i, current.indexOfType(currentInnerTypes[i]));
         }
         // Test contained methods
         assertEquals(expected.countMethods(), current.countMethods());
         MethodInfo[] expectedMethods = expected.getMethods();
         MethodInfo[] currentMethods = current.getMethods();
         assertEquals(expectedMethods.length, currentMethods.length);
         for (int i = 0; i < expectedMethods.length; i++) {
            // Compare elements
            assertMethodInfo(expectedParentProjectInfo, currentParentProjectInfo, expected, current, expectedMethods[i], currentMethods[i]);
            // Test other model functionality
            assertSame(expectedMethods[i], expected.getMethod(i));
            assertSame(currentMethods[i], current.getMethod(i));
            assertSame(expectedMethods[i], expected.getMethod(expectedMethods[i].getDisplayName()));
            assertSame(currentMethods[i], current.getMethod(currentMethods[i].getDisplayName()));
            assertSame(i, expected.indexOfMethod(expectedMethods[i]));
            assertSame(i, current.indexOfMethod(currentMethods[i]));
         }
         // Test contained observer functions
         assertEquals(expected.countObserverFunctions(), current.countObserverFunctions());
         ObserverFunctionInfo[] expectedObserverFunctions = expected.getObserverFunctions();
         ObserverFunctionInfo[] currentObserverFunctions = current.getObserverFunctions();
         assertEquals(expectedObserverFunctions.length, currentObserverFunctions.length);
         for (int i = 0; i < expectedObserverFunctions.length; i++) {
            // Compare elements
            assertObserverFunctionInfo(expectedParentProjectInfo, currentParentProjectInfo, expected, current, expectedObserverFunctions[i], currentObserverFunctions[i]);
            // Test other model functionality
            assertSame(expectedObserverFunctions[i], expected.getObserverFunction(i));
            assertSame(currentObserverFunctions[i], current.getObserverFunction(i));
            assertSame(expectedObserverFunctions[i], expected.getObserverFunction(expectedObserverFunctions[i].getDisplayName()));
            assertSame(currentObserverFunctions[i], current.getObserverFunction(currentObserverFunctions[i].getDisplayName()));
            assertSame(i, expected.indexOfObserverFunction(expectedObserverFunctions[i]));
            assertSame(i, current.indexOfObserverFunction(currentObserverFunctions[i]));
         }
      }
      else {
         assertNull(current);
      }
   }

   /**
    * Ensures that the given {@link MethodInfo}s are equal.
    * @param expectedParentProjectInfo The expected parent {@link ProjectInfo}.
    * @param currentParentProjectInfo The expected parent {@link ProjectInfo}.
    * @param expectedParent The expected parent {@link TypeInfo}.
    * @param currentParent The current parent {@link TypeInfo}.
    * @param expected The expected {@link MethodInfo}.
    * @param current The current {@link MethodInfo}.
    */
   protected static void assertMethodInfo(ProjectInfo expectedParentProjectInfo, 
                                          ProjectInfo currentParentProjectInfo, 
                                          TypeInfo expectedParent,
                                          TypeInfo currentParent,
                                          MethodInfo expected, 
                                          MethodInfo current) {
      if (expected != null) {
         // Test type
         assertNotNull(current);
         assertNotSame(expected, current);
         assertSame(expectedParentProjectInfo, expected.getProjectInfo());
         assertSame(currentParentProjectInfo, current.getProjectInfo());
         assertSame(expectedParent, expected.getParent());
         assertSame(currentParent, current.getParent());
         assertEquals(expected.getDisplayName(), current.getDisplayName());
         assertEquals(expected.getName(), current.getName());
         TestUtilsUtil.assertArrayEquals(expected.getParameterTypes(), current.getParameterTypes());
         // Test contained contracts
         assertEquals(expected.countContracts(), current.countContracts());
         ContractInfo[] expectedContacts = expected.getContracts();
         ContractInfo[] currentContracts = current.getContracts();
         assertEquals(expectedContacts.length, currentContracts.length);
         for (int i = 0; i < expectedContacts.length; i++) {
            // Compare elements
            assertContractInfo(expected, current, expectedContacts[i], currentContracts[i]);
            // Test other model functionality
            assertSame(expectedContacts[i], expected.getContract(i));
            assertSame(currentContracts[i], current.getContract(i));
            assertSame(expectedContacts[i], expected.getContract(expectedContacts[i].getName()));
            assertSame(currentContracts[i], current.getContract(currentContracts[i].getName()));
            assertSame(i, expected.indexOfContract(expectedContacts[i]));
            assertSame(i, current.indexOfContract(currentContracts[i]));
         }
      }
      else {
         assertNull(current);
      }
   }

   /**
    * Ensures that the given {@link ObserverFunctionInfo}s are equal.
    * @param expectedParentProjectInfo The expected parent {@link ProjectInfo}.
    * @param currentParentProjectInfo The expected parent {@link ProjectInfo}.
    * @param expectedParent The expected parent {@link TypeInfo}.
    * @param currentParent The current parent {@link TypeInfo}.
    * @param expected The expected {@link ObserverFunctionInfo}.
    * @param current The current {@link ObserverFunctionInfo}.
    */
   protected static void assertObserverFunctionInfo(ProjectInfo expectedParentProjectInfo, 
                                                    ProjectInfo currentParentProjectInfo, 
                                                    TypeInfo expectedParent,
                                                    TypeInfo currentParent,
                                                    ObserverFunctionInfo expected, 
                                                    ObserverFunctionInfo current) {
      if (expected != null) {
         // Test type
         assertNotNull(current);
         assertNotSame(expected, current);
         assertSame(expectedParentProjectInfo, expected.getProjectInfo());
         assertSame(currentParentProjectInfo, current.getProjectInfo());
         assertSame(expectedParent, expected.getParent());
         assertSame(currentParent, current.getParent());
         assertEquals(expected.getDisplayName(), current.getDisplayName());
         // Test contained contracts
         assertEquals(expected.countContracts(), current.countContracts());
         ContractInfo[] expectedContacts = expected.getContracts();
         ContractInfo[] currentContracts = current.getContracts();
         assertEquals(expectedContacts.length, currentContracts.length);
         for (int i = 0; i < expectedContacts.length; i++) {
            // Compare elements
            assertContractInfo(expected, current, expectedContacts[i], currentContracts[i]);
            // Test other model functionality
            assertSame(expectedContacts[i], expected.getContract(i));
            assertSame(currentContracts[i], current.getContract(i));
            assertSame(expectedContacts[i], expected.getContract(expectedContacts[i].getName()));
            assertSame(currentContracts[i], current.getContract(currentContracts[i].getName()));
            assertSame(i, expected.indexOfContract(expectedContacts[i]));
            assertSame(i, current.indexOfContract(currentContracts[i]));
         }
      }
      else {
         assertNull(current);
      }
   }

   /**
    * Ensures that the given {@link ContractInfo}s are equal.
    * @param expectedParent The expected parent {@link AbstractContractContainer}.
    * @param currentParent The current parent {@link AbstractContractContainer}.
    * @param expected The expected {@link ContractInfo}.
    * @param current The current {@link ContractInfo}.
    */
   protected static void assertContractInfo(AbstractContractContainer expectedParent,
                                            AbstractContractContainer currentParent, 
                                            ContractInfo expected,
                                            ContractInfo current) {
      if (expected != null) {
         // Test type
         assertNotNull(current);
         assertNotSame(expected, current);
         assertSame(expectedParent, expected.getParent());
         assertSame(currentParent, current.getParent());
         assertEquals(expected.getName(), current.getName());
         assertEquals(expected.getModality(), current.getModality());
         assertEquals(expected.getProofFile(), current.getProofFile());
         assertEquals(expected.getMetaFile(), current.getMetaFile());
      }
      else {
         assertNull(current);
      }
   }

   /**
    * Creates a new oracle file.
    * @param oracleDirectory The oracle directory.
    * @param expectedModelPathInBundle The expected path in bundle.
    * @param infoFile The new oracle file.
    * @throws Exception Occurred Exception
    */
   protected static void createOracleFile(File oracleDirectory,
                                          String expectedModelPathInBundle, 
                                          IFile infoFile) throws Exception {
      // Create sub folder structure
      File oracleFile = new File(oracleDirectory, expectedModelPathInBundle);
      oracleFile.getParentFile().mkdirs();
      // Create oracle file
      ResourceUtil.copyIntoFileSystem(infoFile, oracleFile);
      // Print message to the user.
      printOracleDirectory();
   }
}
