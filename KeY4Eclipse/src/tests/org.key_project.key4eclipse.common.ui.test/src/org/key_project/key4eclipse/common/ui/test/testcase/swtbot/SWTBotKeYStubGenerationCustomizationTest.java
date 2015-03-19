package org.key_project.key4eclipse.common.ui.test.testcase.swtbot;

import java.io.File;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotRadio;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTableItem;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotText;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.stubby.KeYGeneratorCustomization;
import org.key_project.key4eclipse.common.ui.stubby.KeYStubGenerationCustomization;
import org.key_project.key4eclipse.common.ui.test.Activator;
import org.key_project.key4eclipse.starter.core.property.KeYClassPathEntry;
import org.key_project.key4eclipse.starter.core.property.KeYClassPathEntry.KeYClassPathEntryKind;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties.UseBootClassPathKind;
import org.key_project.stubby.core.test.testcase.StubGeneratorUtilTest;
import org.key_project.stubby.core.util.StubGeneratorUtil;
import org.key_project.stubby.ui.test.testcase.swtbot.AbstractSWTBotGenerateStubsTest;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * SWTbot tests for {@link KeYStubGenerationCustomization} and {@link KeYGeneratorCustomization}.
 * @author Martin Hentschel
 */
public class SWTBotKeYStubGenerationCustomizationTest extends AbstractSWTBotGenerateStubsTest {
   /**
    * Tests the extraction of the boot class path content.
    * @throws Exception Occurred Exception
    */
   @Test
   public void testBootClassPath_StubFolderDoesNotExist() throws Exception {
      doGenerationTest("SWTBotKeYStubGenerationCustomizationTest_testBootClassPath_StubFolderDoesNotExist", 
                       Activator.PLUGIN_ID, 
                       null, 
                       new BootClassPathExtractionTestSteps(false, true));
   }
   /**
    * Tests the extraction of the boot class path content.
    * @throws Exception Occurred Exception
    */
   @Test
   public void testBootClassPath_StubFolderIsEmpty() throws Exception {
      doGenerationTest("SWTBotKeYStubGenerationCustomizationTest_testBootClassPath_StubFolderIsEmpty", 
                       Activator.PLUGIN_ID, 
                       null, 
                       new BootClassPathExtractionTestSteps(true, true));
   }
   /**
    * Tests the extraction of the boot class path content.
    * @throws Exception Occurred Exception
    */
   @Test
   public void testBootClassPath_StubFolderIsNotEmpty() throws Exception {
      doGenerationTest("SWTBotKeYStubGenerationCustomizationTest_testBootClassPath_StubFolderIsNotEmpty", 
                       Activator.PLUGIN_ID, 
                       null, 
                       new BootClassPathExtractionTestSteps(true, false));
   }
   
   /**
    * Test steps to test that the boot class path is correctly extracted.
    * @author Martin Hentschel
    */
   private static class BootClassPathExtractionTestSteps extends PathGeneratorTestSteps {
      /**
       * Does the stub folder already exist?
       */
      private final boolean stubFolderExists;
      
      /**
       * Is the stub folder empty?
       */
      private final boolean stubFolderIsEmpty;

      /**
       * Constructor.
       * @param stubFolderExists Does the stub folder already exist?
       * @param stubFolderIsEmpty Is the stub folder empty?
       */
      public BootClassPathExtractionTestSteps(boolean stubFolderExists, boolean stubFolderIsEmpty) {
         super(false, false, false, true);
         this.stubFolderExists = stubFolderExists;
         this.stubFolderIsEmpty = stubFolderIsEmpty;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void initProject(IJavaProject javaProject) throws Exception {
         super.initProject(javaProject);
         if (stubFolderExists) {
            IFolder stubFolder = javaProject.getProject().getFolder(new Path(StubGeneratorUtil.DEFAULT_STUB_FOLDER_PATH));
            ResourceUtil.ensureExists(stubFolder);
            if (!stubFolderIsEmpty) {
               TestUtilsUtil.createFile(stubFolder, "Readme.txt", "Folder is not empty!");
            }
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void testResults(IJavaProject javaProject) throws Exception {
         super.testResults(javaProject);
         IFolder stubFolder = javaProject.getProject().getFolder(new Path(StubGeneratorUtil.DEFAULT_STUB_FOLDER_PATH));
         if (!stubFolderExists || stubFolderIsEmpty) {
            assertEquals(1, stubFolder.members().length); // The Readme.txt file
            assertTrue(stubFolder.members()[0] instanceof IFolder);
            assertEquals("java", stubFolder.members()[0].getName());
         }
         else {
            assertEquals(1, stubFolder.members().length); // The Readme.txt file
            assertTrue(stubFolder.members()[0] instanceof IFile);
            assertEquals("Readme.txt", stubFolder.members()[0].getName());
         }
      }
   }
   
   /**
    * Tests ignored types when part of KeY's class path.
    * @throws Exception Occurred Exception
    */
   @Test
   public void testIgnoredClassPathTypes_DefaultBootClassPath() throws Exception {
      doGenerationTest("SWTBotKeYStubGenerationCustomizationTest_testIgnoredClassPathTypes_DefaultBootClassPath", 
                       Activator.PLUGIN_ID, 
                       "data/stubbyExample/src", 
                       new IgnoredClassPathTypesSteps(UseBootClassPathKind.KEY_DEFAULT));
   }
   
   /**
    * Tests ignored types when part of KeY's class path.
    * @throws Exception Occurred Exception
    */
   @Test
   public void testIgnoredClassPathTypes_FileSystemBootClassPath() throws Exception {
      doGenerationTest("SWTBotKeYStubGenerationCustomizationTest_testIgnoredClassPathTypes_DefaultBootClassPath", 
                       Activator.PLUGIN_ID, 
                       "data/stubbyExample/src", 
                       new IgnoredClassPathTypesSteps(UseBootClassPathKind.EXTERNAL_IN_FILE_SYSTEM));
   }
   
   /**
    * Tests ignored types when part of KeY's class path.
    * @throws Exception Occurred Exception
    */
   @Test
   public void testIgnoredClassPathTypes_WorkspaceBootClassPath() throws Exception {
      doGenerationTest("SWTBotKeYStubGenerationCustomizationTest_testIgnoredClassPathTypes_WorkspaceBootClassPath", 
                       Activator.PLUGIN_ID, 
                       "data/stubbyExample/src", 
                       new IgnoredClassPathTypesSteps(UseBootClassPathKind.WORKSPACE));
   }
   
   /**
    * Test steps to test ignored types.
    * @author Martin Hentschel
    */
   private static class IgnoredClassPathTypesSteps extends PathGeneratorTestSteps {
      /**
       * The {@link UseBootClassPathKind} to test.
       */
      private final UseBootClassPathKind kind;
      
      /**
       * The expected ignored types.
       */
      private final Set<String> expectedIgnoredTypes = new HashSet<String>();
      
      /**
       * Optionally, the external file boot class path.
       */
      private File externalBootClassPath;

      /**
       * Constructor.
       * @param kind The {@link UseBootClassPathKind} to test.
       */
      public IgnoredClassPathTypesSteps(UseBootClassPathKind kind) {
         super(true, true, false, false);
         this.kind = kind;
         expectedIgnoredTypes.add("java.lang.Object");
         expectedIgnoredTypes.add("java.io.Serializable");
         expectedIgnoredTypes.add("java.lang.Comparable");
         expectedIgnoredTypes.add("java.lang.String");
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void initProject(IJavaProject javaProject) throws Exception {
         IProject project = javaProject.getProject();
         if (UseBootClassPathKind.EXTERNAL_IN_FILE_SYSTEM.equals(kind)) {
            externalBootClassPath = IOUtil.createTempDirectory("Boot", "ClassPath");
            BundleUtil.extractFromBundleToFilesystem(Activator.PLUGIN_ID, "data/stubbyExample/boot", externalBootClassPath);
            KeYResourceProperties.setBootClassPath(project, kind, externalBootClassPath.getAbsolutePath());
         }
         else if (UseBootClassPathKind.WORKSPACE.equals(kind)) {
            IFolder folder = TestUtilsUtil.createFolder(javaProject.getProject(), "boot");
            BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/stubbyExample/boot", folder);
            KeYResourceProperties.setBootClassPath(project, kind, folder.getFullPath().toString());
         }
         super.initProject(javaProject);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void wizardFinished(SWTBotShell shell) {
         SWTBotShell informationShell = shell.bot().shell("Information");
         SWTBotTable table = informationShell.bot().table();
         assertEquals(expectedIgnoredTypes.size(), table.rowCount());
         for (int i = 0; i < table.rowCount(); i++) {
            table.select(i);
            SWTBotTableItem item = table.getTableItem(i);
            String type = item.getText(0);
            assertTrue(expectedIgnoredTypes.remove(type));
            String reason = item.getText(1);
            assertEquals("Type is part of KeY's boot class path.", reason);
         }
         informationShell.close();
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void testResults(IJavaProject javaProject) throws Exception {
         IOUtil.delete(externalBootClassPath);
         super.testResults(javaProject);
         // Extract oracle stubs into project
         IFolder oracleFolder = javaProject.getProject().getFolder("oracleStubs");
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/stubbyExample/classPathStubs", oracleFolder);
         // Compare generated stubs with oracle stubs
         IFolder stubFolder = javaProject.getProject().getFolder(new Path(StubGeneratorUtil.DEFAULT_STUB_FOLDER_PATH));
         StubGeneratorUtilTest.assertResources(oracleFolder.members(), stubFolder.members());
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      protected UseBootClassPathKind getDefaultUseBootClassPathKind(IJavaProject javaProject) {
         return kind;
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      protected String getDefaultBootClassPath(IJavaProject javaProject) {
         if (UseBootClassPathKind.WORKSPACE.equals(kind)) {
            return javaProject.getProject().getFolder("boot").getFullPath().toString();
         }
         else {
            return externalBootClassPath != null ? 
                   externalBootClassPath.getAbsolutePath() : 
                   null;
         }
      }
   }
   
   /**
    * Tests class path to class path.
    * @throws Exception Occurred Exception
    */
   @Test
   public void testClassPath_to_ClassPath() throws Exception {
      doGenerationTest("SWTBotKeYStubGenerationCustomizationTest_testClassPath_to_ClassPath", 
                       Activator.PLUGIN_ID, 
                       null, 
                       new PathGeneratorTestSteps(true, true, false, false));
   }

   /**
    * Tests class path to not class path.
    * @throws Exception Occurred Exception
    */
   @Test
   public void testClassPath_to_NotClassPath() throws Exception {
      doGenerationTest("SWTBotKeYStubGenerationCustomizationTest_testClassPath_to_NotClassPath", 
                       Activator.PLUGIN_ID, 
                       null, 
                       new PathGeneratorTestSteps(true, false, false, false));
   }

   /**
    * Tests not class path to class path.
    * @throws Exception Occurred Exception
    */
   @Test
   public void testNotClassPath_to_ClassPath() throws Exception {
      doGenerationTest("SWTBotKeYStubGenerationCustomizationTest_testNotClassPath_to_ClassPath", 
                       Activator.PLUGIN_ID, 
                       null, 
                       new PathGeneratorTestSteps(false, true, false, false));
   }

   /**
    * Tests not class path to not class path.
    * @throws Exception Occurred Exception
    */
   @Test
   public void testNotClassPath_to_NotClassPath() throws Exception {
      doGenerationTest("SWTBotKeYStubGenerationCustomizationTest_testNotClassPath_to_NotClassPath", 
                       Activator.PLUGIN_ID, 
                       null, 
                       new PathGeneratorTestSteps(false, false, false, false));
   }
   
   /**
    * Tests class path to class path.
    * @throws Exception Occurred Exception
    */
   @Test
   public void testBootClassPath_to_BootClassPath() throws Exception {
      doGenerationTest("SWTBotKeYStubGenerationCustomizationTest_testBootClassPath_to_BootClassPath", 
                       Activator.PLUGIN_ID, 
                       null, 
                       new PathGeneratorTestSteps(false, false, true, true));
   }

   /**
    * Tests class path to not class path.
    * @throws Exception Occurred Exception
    */
   @Test
   public void testClassPath_to_BootClassPath() throws Exception {
      doGenerationTest("SWTBotKeYStubGenerationCustomizationTest_testClassPath_to_BootClassPath", 
                       Activator.PLUGIN_ID, 
                       null, 
                       new PathGeneratorTestSteps(true, false, false, true));
   }

   /**
    * Tests not class path to class path.
    * @throws Exception Occurred Exception
    */
   @Test
   public void testNotClassPath_to_BootClassPath() throws Exception {
      doGenerationTest("SWTBotKeYStubGenerationCustomizationTest_testNotClassPath_to_BootClassPath", 
                       Activator.PLUGIN_ID, 
                       null, 
                       new PathGeneratorTestSteps(false, false, false, true));
   }

   /**
    * Tests not class path to not class path.
    * @throws Exception Occurred Exception
    */
   @Test
   public void testBootClassPath_to_NotClassPath() throws Exception {
      doGenerationTest("SWTBotKeYStubGenerationCustomizationTest_testBootClassPath_to_NotClassPath", 
                       Activator.PLUGIN_ID, 
                       null, 
                       new PathGeneratorTestSteps(false, false, true, false));
   }

   /**
    * Tests not class path to not class path.
    * @throws Exception Occurred Exception
    */
   @Test
   public void testBootClassPath_to_ClassPath() throws Exception {
      doGenerationTest("SWTBotKeYStubGenerationCustomizationTest_testBootClassPath_to_ClassPath", 
                       Activator.PLUGIN_ID, 
                       null, 
                       new PathGeneratorTestSteps(false, true, true, false));
   }
   
   /**
    * The {@link IGeneratorTestSteps} to test paths.
    * @author Martin Hentschel
    */
   private static class PathGeneratorTestSteps implements IGeneratorTestSteps {
      /**
       * Is before generation part of the class path?
       */
      private final boolean beforeClassPath;
      
      /**
       * Should be after generation part of the class path?
       */
      private final boolean afterClassPath;
      
      /**
       * Is before generation part of the boot class path?
       */
      private final boolean beforeBootClassPath;
      
      /**
       * Should be after generation part of the boot class path?
       */
      private final boolean afterBootClassPath;

      /**
       * Constructor
       * @param beforeClassPath Is before generation part of the class path?
       * @param afterClassPath Should be after generation part of the class path?
       * @param beforeBootClassPath Is before generation part of the boot class path?
       * @param afterBootClassPath Should be after generation part of the boot class path?
       */
      public PathGeneratorTestSteps(boolean beforeClassPath, 
                                    boolean afterClassPath,
                                    boolean beforeBootClassPath,
                                    boolean afterBootClassPath) {
         this.beforeClassPath = beforeClassPath;
         this.afterClassPath = afterClassPath;
         this.beforeBootClassPath = beforeBootClassPath;
         this.afterBootClassPath = afterBootClassPath;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void initProject(IJavaProject javaProject) throws Exception {
         IProject project = javaProject.getProject();
         String fullPath = KeYStubGenerationCustomization.computeFullPath(project, StubGeneratorUtil.DEFAULT_STUB_FOLDER_PATH);
         if (beforeClassPath) {
            List<KeYClassPathEntry> entries = KeYResourceProperties.getClassPathEntries(project);
            entries.add(new KeYClassPathEntry(KeYClassPathEntryKind.WORKSPACE, fullPath));
            KeYResourceProperties.setClassPathEntries(project, entries);
         }
         if (beforeBootClassPath) {
            KeYResourceProperties.setBootClassPath(project, UseBootClassPathKind.WORKSPACE, fullPath);
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void testAndSetSettings(SWTBotShell shell, SWTBotText stubFolderText) throws Exception {
         // Test initial values
         SWTBotRadio notUsed = shell.bot().radio("&Not considered");
         SWTBotRadio classPath = shell.bot().radio("&Class Path");
         SWTBotRadio bootClassPath = shell.bot().radio("&Boot Class Path");
         if (beforeBootClassPath) {
            assertFalse(notUsed.isSelected());
            assertFalse(classPath.isSelected());
            assertTrue(bootClassPath.isSelected());
         }
         else if (beforeClassPath) {
            assertFalse(notUsed.isSelected());
            assertTrue(classPath.isSelected());
            assertFalse(bootClassPath.isSelected());
         }
         else {
            assertTrue(notUsed.isSelected());
            assertFalse(classPath.isSelected());            
            assertFalse(bootClassPath.isSelected());
         }
         // Set values to test
         if (afterBootClassPath) {
            bootClassPath.click();
         }
         else if (afterClassPath) {
            classPath.click();
         }
         else {
            notUsed.click();
         }
      }

      @Override
      public void wizardFinished(SWTBotShell shell) {
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void testResults(IJavaProject javaProject) throws Exception {
         IProject project = javaProject.getProject();
         List<KeYClassPathEntry> entries = KeYResourceProperties.getClassPathEntries(project);
         String fullPath = KeYStubGenerationCustomization.computeFullPath(project, StubGeneratorUtil.DEFAULT_STUB_FOLDER_PATH);
         KeYClassPathEntry entry = KeYResourceProperties.searchClassPathEntry(entries, KeYClassPathEntryKind.WORKSPACE, fullPath);
         if (afterClassPath) {
            assertNotNull(entry);
         }
         else {
            assertNull(entry);
         }
         if (afterBootClassPath) {
            assertEquals(UseBootClassPathKind.WORKSPACE, KeYResourceProperties.getUseBootClassPathKind(project));
            assertEquals(fullPath, KeYResourceProperties.getBootClassPath(project));
         }
         else {
            assertEquals(getDefaultUseBootClassPathKind(javaProject), KeYResourceProperties.getUseBootClassPathKind(project));
            assertEquals(getDefaultBootClassPath(javaProject), KeYResourceProperties.getBootClassPath(project));
         }
      }
      
      /**
       * Returns the default {@link UseBootClassPathKind}.
       * @param javaProject The {@link IJavaProject} to test.
       * @return The default {@link UseBootClassPathKind}.
       */
      protected UseBootClassPathKind getDefaultUseBootClassPathKind(IJavaProject javaProject) {
         return UseBootClassPathKind.KEY_DEFAULT;
      }
      
      /**
       * Returns the default boot class path.
       * @param javaProject The {@link IJavaProject} to test.
       * @return The default boot class path.
       */
      protected String getDefaultBootClassPath(IJavaProject javaProject) {
         return null;
      }
   }
}
