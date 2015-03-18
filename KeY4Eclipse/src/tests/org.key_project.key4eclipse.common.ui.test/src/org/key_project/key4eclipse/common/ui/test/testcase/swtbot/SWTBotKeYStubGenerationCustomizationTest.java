package org.key_project.key4eclipse.common.ui.test.testcase.swtbot;

import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotRadio;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotText;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.stubby.KeYGeneratorCustomization;
import org.key_project.key4eclipse.common.ui.stubby.KeYStubGenerationCustomization;
import org.key_project.key4eclipse.common.ui.test.Activator;
import org.key_project.key4eclipse.starter.core.property.KeYClassPathEntry;
import org.key_project.key4eclipse.starter.core.property.KeYClassPathEntry.KeYClassPathEntryKind;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.stubby.core.util.StubGeneratorUtil;
import org.key_project.stubby.ui.test.testcase.swtbot.AbstractSWTBotGenerateStubsTest;

/**
 * SWTbot tests for {@link KeYStubGenerationCustomization} and {@link KeYGeneratorCustomization}.
 * @author Martin Hentschel
 */
public class SWTBotKeYStubGenerationCustomizationTest extends AbstractSWTBotGenerateStubsTest {
   /**
    * Tests class path to class path.
    * @throws Exception Occurred Exception
    */
   @Test
   public void testClassPath_to_ClassPath() throws Exception {
      doGenerationTest("SWTBotKeYStubGenerationCustomizationTest_testClassPath_to_ClassPath", 
                       Activator.PLUGIN_ID, 
                       "data/stubbyExample/src", 
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
                       "data/stubbyExample/src", 
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
                       "data/stubbyExample/src", 
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
                       "data/stubbyExample/src", 
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
