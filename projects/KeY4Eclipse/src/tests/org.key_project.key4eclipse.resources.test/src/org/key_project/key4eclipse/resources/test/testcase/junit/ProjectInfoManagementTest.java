package org.key_project.key4eclipse.resources.test.testcase.junit;

import java.io.File;
import java.io.IOException;
import java.util.Iterator;

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
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;
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
   private static final File oracleDirectory;

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
         Iterator<PackageInfo> expectedIter = expected.getPackages().iterator();
         Iterator<PackageInfo> currentIter = current.getPackages().iterator();
         int index = 0;
         while (expectedIter.hasNext() && currentIter.hasNext()) {
            // Compare elements
            PackageInfo expectedPackage = expectedIter.next();
            PackageInfo currentPackage = currentIter.next();
            assertPackageInfo(expected, current, expectedPackage, currentPackage);
            // Test other model functionality
            assertSame(expectedPackage, expected.getPackage(index));
            assertSame(currentPackage, current.getPackage(index));
            assertSame(expectedPackage, expected.getPackage(expectedPackage.getName()));
            assertSame(currentPackage, current.getPackage(currentPackage.getName()));
            assertSame(index, expected.indexOfPackage(expectedPackage));
            assertSame(index, current.indexOfPackage(currentPackage));
            index++;
         }
         assertFalse(expectedIter.hasNext());
         assertFalse(currentIter.hasNext());
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
         Iterator<TypeInfo> expectedIter = expected.getTypes().iterator();
         Iterator<TypeInfo> currentIter = current.getTypes().iterator();
         int index = 0;
         while (expectedIter.hasNext() && currentIter.hasNext()) {
            // Compare elements
            TypeInfo expectedType = expectedIter.next();
            TypeInfo currentType = currentIter.next();
            assertTypeInfo(expectedParentProjectInfo, currentParentProjectInfo, expected, current, expectedType, currentType);
            // Test other model functionality
            assertSame(expectedType, expected.getType(index));
            assertSame(currentType, current.getType(index));
            assertSame(expectedType, expected.getType(expectedType.getName()));
            assertSame(currentType, current.getType(currentType.getName()));
            assertSame(index, expected.indexOfType(expectedType));
            assertSame(index, current.indexOfType(currentType));
            index++;
         }
         assertFalse(expectedIter.hasNext());
         assertFalse(currentIter.hasNext());
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
         Iterator<TypeInfo> expectedTypeIter = expected.getTypes().iterator();
         Iterator<TypeInfo> currentTypeIter = current.getTypes().iterator();
         int index = 0;
         while (expectedTypeIter.hasNext() && currentTypeIter.hasNext()) {
            // Compare elements
            TypeInfo expectedInnerType = expectedTypeIter.next();
            TypeInfo currentInnerType = currentTypeIter.next();
            assertTypeInfo(expectedParentProjectInfo, currentParentProjectInfo, expected, current, expectedInnerType, currentInnerType);
            // Test other model functionality
            assertSame(expectedInnerType, expected.getType(index));
            assertSame(currentInnerType, current.getType(index));
            assertSame(expectedInnerType, expected.getType(expectedInnerType.getName()));
            assertSame(currentInnerType, current.getType(currentInnerType.getName()));
            assertSame(index, expected.indexOfType(expectedInnerType));
            assertSame(index, current.indexOfType(currentInnerType));
            index++;
         }
         assertFalse(expectedTypeIter.hasNext());
         assertFalse(currentTypeIter.hasNext());
         // Test contained methods
         assertEquals(expected.countMethods(), current.countMethods());
         Iterator<MethodInfo> expectedMethodIter = expected.getMethods().iterator();
         Iterator<MethodInfo> currentMethodIter = current.getMethods().iterator();
         index = 0;
         while (expectedMethodIter.hasNext() && currentMethodIter.hasNext()) {
            // Compare elements
            MethodInfo expectedMethod = expectedMethodIter.next();
            MethodInfo currentMethod = currentMethodIter.next();
            assertMethodInfo(expectedParentProjectInfo, currentParentProjectInfo, expected, current, expectedMethod, currentMethod);
            // Test other model functionality
            assertSame(expectedMethod, expected.getMethod(index));
            assertSame(currentMethod, current.getMethod(index));
            assertSame(expectedMethod, expected.getMethod(expectedMethod.getDisplayName()));
            assertSame(currentMethod, current.getMethod(currentMethod.getDisplayName()));
            assertSame(index, expected.indexOfMethod(expectedMethod));
            assertSame(index, current.indexOfMethod(currentMethod));
            index++;
         }
         assertFalse(expectedMethodIter.hasNext());
         assertFalse(currentMethodIter.hasNext());
         // Test contained observer functions
         assertEquals(expected.countObserverFunctions(), current.countObserverFunctions());
         Iterator<ObserverFunctionInfo> expectedObserverFunctionIter = expected.getObserverFunctions().iterator();
         Iterator<ObserverFunctionInfo> currentObserverFunctionIter = current.getObserverFunctions().iterator();
         index = 0;
         while (expectedObserverFunctionIter.hasNext() && currentObserverFunctionIter.hasNext()) {
            // Compare elements
            ObserverFunctionInfo expectedObserverFunction = expectedObserverFunctionIter.next();
            ObserverFunctionInfo currentObserverFunction = currentObserverFunctionIter.next();
            assertObserverFunctionInfo(expectedParentProjectInfo, currentParentProjectInfo, expected, current, expectedObserverFunction, currentObserverFunction);
            // Test other model functionality
            assertSame(expectedObserverFunction, expected.getObserverFunction(index));
            assertSame(currentObserverFunction, current.getObserverFunction(index));
            assertSame(expectedObserverFunction, expected.getObserverFunction(expectedObserverFunction.getDisplayName()));
            assertSame(currentObserverFunction, current.getObserverFunction(currentObserverFunction.getDisplayName()));
            assertSame(index, expected.indexOfObserverFunction(expectedObserverFunction));
            assertSame(index, current.indexOfObserverFunction(currentObserverFunction));
            index++;
         }
         assertFalse(expectedObserverFunctionIter.hasNext());
         assertFalse(currentObserverFunctionIter.hasNext());
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
         Iterator<ContractInfo> expectedIter = expected.getContracts().iterator();
         Iterator<ContractInfo> currentIter = current.getContracts().iterator();
         int index = 0;
         while (expectedIter.hasNext() && currentIter.hasNext()) {
            // Compare elements
            ContractInfo expectedContact = expectedIter.next();
            ContractInfo currentContract = currentIter.next();
            assertContractInfo(expected, current, expectedContact, currentContract);
            // Test other model functionality
            assertSame(expectedContact, expected.getContract(index));
            assertSame(currentContract, current.getContract(index));
            assertSame(expectedContact, expected.getContract(expectedContact.getName()));
            assertSame(currentContract, current.getContract(currentContract.getName()));
            assertSame(index, expected.indexOfContract(expectedContact));
            assertSame(index, current.indexOfContract(currentContract));
            index++;
         }
         assertFalse(expectedIter.hasNext());
         assertFalse(currentIter.hasNext());
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
         Iterator<ContractInfo> expectedIter = expected.getContracts().iterator();
         Iterator<ContractInfo> currentIter = current.getContracts().iterator();
         int index = 0;
         while (expectedIter.hasNext() && currentIter.hasNext()) {
            // Compare elements
            ContractInfo expectedContact = expectedIter.next();
            ContractInfo currentContract = currentIter.next();
            assertContractInfo(expected, current, expectedContact, currentContract);
            // Test other model functionality
            assertSame(expectedContact, expected.getContract(index));
            assertSame(currentContract, current.getContract(index));
            assertSame(expectedContact, expected.getContract(expectedContact.getName()));
            assertSame(currentContract, current.getContract(currentContract.getName()));
            assertSame(index, expected.indexOfContract(expectedContact));
            assertSame(index, current.indexOfContract(currentContract));
            index++;
         }
         assertFalse(expectedIter.hasNext());
         assertFalse(currentIter.hasNext());
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
