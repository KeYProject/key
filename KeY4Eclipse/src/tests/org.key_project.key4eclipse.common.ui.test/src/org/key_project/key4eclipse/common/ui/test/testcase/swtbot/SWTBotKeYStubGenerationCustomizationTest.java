package org.key_project.key4eclipse.common.ui.test.testcase.swtbot;

import java.io.File;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

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
import org.key_project.util.java.IOUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * SWTbot tests for {@link KeYStubGenerationCustomization} and {@link KeYGeneratorCustomization}.
 * @author Martin Hentschel
 */
public class SWTBotKeYStubGenerationCustomizationTest extends AbstractSWTBotGenerateStubsTest {
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
    * Test steps to test ignored types
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
         super(true, true);
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
                       new PathGeneratorTestSteps(true, true));
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
                       new PathGeneratorTestSteps(true, false));
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
                       new PathGeneratorTestSteps(false, true));
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
                       new PathGeneratorTestSteps(false, false));
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
       * Constructor
       * @param beforeClassPath Is before generation part of the class path?
       * @param afterClassPath Should be after generation part of the class path?
       */
      public PathGeneratorTestSteps(boolean beforeClassPath, boolean afterClassPath) {
         this.beforeClassPath = beforeClassPath;
         this.afterClassPath = afterClassPath;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void initProject(IJavaProject javaProject) throws Exception {
         if (beforeClassPath) {
            IProject project = javaProject.getProject();
            String fullPath = KeYStubGenerationCustomization.computeFullPath(project, StubGeneratorUtil.DEFAULT_STUB_FOLDER_PATH);
            List<KeYClassPathEntry> entries = KeYResourceProperties.getClassPathEntries(project);
            entries.add(new KeYClassPathEntry(KeYClassPathEntryKind.WORKSPACE, fullPath));
            KeYResourceProperties.setClassPathEntries(project, entries);
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
         if (beforeClassPath) {
            assertFalse(notUsed.isSelected());
            assertTrue(classPath.isSelected());
         }
         else {
            assertTrue(notUsed.isSelected());
            assertFalse(classPath.isSelected());            
         }
         // Set values to test
         if (afterClassPath) {
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
      }
   }
}
