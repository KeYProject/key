package org.key_project.sed.core.test.testcase.swtbot;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.util.List;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotPerspective;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.serialization.SEDXMLReader;
import org.key_project.sed.core.model.serialization.SEDXMLWriter;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.core.util.SEDPreferenceUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests {@link SEDXMLWriter} and {@link SEDXMLReader}.
 * @author Martin Hentschel
 */
public class SWTBotSerializationTest extends TestCase {
   /**
    * Tests the reading and writing process via
    * {@link SEDXMLWriter#toXML(IDebugTarget[], String)},
    * {@link SEDXMLWriter#toXML(ILaunch, String)},
    * {@link SEDXMLWriter#write(IDebugTarget[], String, org.eclipse.core.resources.IFile)},
    * {@link SEDXMLWriter#write(ILaunch, String, org.eclipse.core.resources.IFile)},
    * {@link SEDXMLWriter#write(ILaunch, String, java.io.OutputStream)},
    * {@link SEDXMLWriter#write(IDebugTarget[], String, java.io.OutputStream)}
    * {@link SEDXMLReader#read(java.io.InputStream)},
    * {@link SEDXMLReader#read(String)} and
    * {@link SEDXMLReader#read(IFile)}.
    */
   @Test
   public void testWritingAndReading() throws Exception {
      // Close welcome view
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotPerspective defaultPerspective = bot.activePerspective();
      // Disable compact view
      boolean originalCompactView = SEDPreferenceUtil.isShowCompactExecutionTree();
      SEDPreferenceUtil.setShowCompactExecutionTree(true);
      SWTBotTree debugTree = null;
      File tempFile = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Open symbolic debug perspective
         TestSedCoreUtil.openSymbolicDebugPerspective();
         // Launch fixed example
         TestSedCoreUtil.launchFixedExample();
         // Find the launched ILaunch in the debug view
         SWTBotView debugView = TestSedCoreUtil.getDebugView(bot);
         debugTree = debugView.bot().tree();
         bot.waitUntil(Conditions.treeHasRows(debugTree, 1));
         // Get the launch
         ISEDDebugTarget target = TestSedCoreUtil.waitUntilDebugTreeHasDebugTarget(bot, debugTree);
         assertNotNull(target);
         ILaunch launch = target.getLaunch();
         assertNotNull(launch);
         
         // Serialize launch to String
         SEDXMLWriter writer = new SEDXMLWriter();
         String xml = writer.toXML(launch, SEDXMLWriter.DEFAULT_ENCODING);
         // Read launch from String
         SEDXMLReader reader = new SEDXMLReader();
         List<ISEDDebugTarget> read = reader.read(xml);
         // Compare models
         assertNotNull(read);
         assertEquals(1, read.size());
         TestSedCoreUtil.compareDebugTarget(target, read.get(0), true);
         
         // Serialize targets to String
         xml = writer.toXML(launch.getDebugTargets(), SEDXMLWriter.DEFAULT_ENCODING);
         // Read launch from String
         read = reader.read(xml);
         // Compare models
         assertNotNull(read);
         assertEquals(1, read.size());
         TestSedCoreUtil.compareDebugTarget(target, read.get(0), true);
         
         // Serialize launch to File
         tempFile = File.createTempFile("SWTBotSerializationTest_testWritingAndReading", ".xml");
         writer.write(launch, SEDXMLWriter.DEFAULT_ENCODING, new FileOutputStream(tempFile));
         // Read launch from String
         read = reader.read(new FileInputStream(tempFile));
         // Compare models
         assertNotNull(read);
         assertEquals(1, read.size());
         TestSedCoreUtil.compareDebugTarget(target, read.get(0), true);
         
         // Serialize launch to File
         tempFile = File.createTempFile("SWTBotSerializationTest_testWritingAndReading", ".xml");
         writer.write(launch.getDebugTargets(), SEDXMLWriter.DEFAULT_ENCODING, new FileOutputStream(tempFile));
         // Read launch from String
         read = reader.read(new FileInputStream(tempFile));
         // Compare models
         assertNotNull(read);
         assertEquals(1, read.size());
         TestSedCoreUtil.compareDebugTarget(target, read.get(0), true);
         
         // Serialize launch to File
         IProject project = TestUtilsUtil.createProject("SWTBotSerializationTest_testWritingAndReading");
         IFile workspaceFile = project.getFile("Test.xml");
         writer.write(launch, SEDXMLWriter.DEFAULT_ENCODING, workspaceFile);
         // Read launch from String
         read = reader.read(workspaceFile);
         // Compare models
         assertNotNull(read);
         assertEquals(1, read.size());
         TestSedCoreUtil.compareDebugTarget(target, read.get(0), true);

         // Serialize launch to File
         writer.write(launch.getDebugTargets(), SEDXMLWriter.DEFAULT_ENCODING, workspaceFile);
         // Read launch from String
         read = reader.read(workspaceFile);
         // Compare models
         assertNotNull(read);
         assertEquals(1, read.size());
         TestSedCoreUtil.compareDebugTarget(target, read.get(0), true);
         
         // Serialize launch to String without encoding
         xml = writer.toXML(launch, null);
         // Read launch from String
         read = reader.read(xml);
         // Compare models
         assertNotNull(read);
         assertEquals(1, read.size());
         TestSedCoreUtil.compareDebugTarget(target, read.get(0), true);
         
         // Serialize launch to String without encoding
         xml = writer.toXML(launch.getDebugTargets(), null);
         // Read launch from String
         read = reader.read(xml);
         // Compare models
         assertNotNull(read);
         assertEquals(1, read.size());
         TestSedCoreUtil.compareDebugTarget(target, read.get(0), true);
         
         // Serialize launch to File without encoding
         writer.write(launch, null, new FileOutputStream(tempFile, false));
         // Read launch from String
         read = reader.read(new FileInputStream(tempFile));
         // Compare models
         assertNotNull(read);
         assertEquals(1, read.size());
         TestSedCoreUtil.compareDebugTarget(target, read.get(0), true);
         
         // Serialize launch to File without encoding
         writer.write(launch, null, workspaceFile);
         // Read launch from String
         read = reader.read(workspaceFile);
         // Compare models
         assertNotNull(read);
         assertEquals(1, read.size());
         TestSedCoreUtil.compareDebugTarget(target, read.get(0), true);

         // Serialize launch to File without encoding
         writer.write(launch.getDebugTargets(), null, workspaceFile);
         // Read launch from String
         read = reader.read(workspaceFile);
         // Compare models
         assertNotNull(read);
         assertEquals(1, read.size());
         TestSedCoreUtil.compareDebugTarget(target, read.get(0), true);
         
         // Serialize null to String
         xml = writer.toXML((ILaunch)null, SEDXMLWriter.DEFAULT_ENCODING);
         // Read launch from String
         try {
            read = reader.read(xml);
            fail("Reading an empty String should not be possible.");
         }
         catch (Exception e) {
         }
         
         // Serialize null to String
         xml = writer.toXML((IDebugTarget[])null, SEDXMLWriter.DEFAULT_ENCODING);
         // Read launch from String
         try {
            read = reader.read(xml);
            fail("Reading an empty String should not be possible.");
         }
         catch (Exception e) {
         }
         
         // Serialize null to File
         writer.write((ILaunch)null, SEDXMLWriter.DEFAULT_ENCODING, new FileOutputStream(tempFile, false));
         // Read launch from File
         try {
            read = reader.read(new FileInputStream(tempFile));
            fail("Reading an empty String should not be possible.");
         }
         catch (Exception e) {
         }
         
         // Serialize null to File
         writer.write((IDebugTarget[])null, SEDXMLWriter.DEFAULT_ENCODING, new FileOutputStream(tempFile, false));
         // Read launch from File
         try {
            read = reader.read(new FileInputStream(tempFile));
            fail("Reading an empty String should not be possible.");
         }
         catch (Exception e) {
         }
         
         // Serialize null to File
         writer.write((ILaunch)null, SEDXMLWriter.DEFAULT_ENCODING, workspaceFile);
         // Read launch from File
         try {
            read = reader.read(new FileInputStream(tempFile));
            fail("Reading an empty String should not be possible.");
         }
         catch (Exception e) {
         }
         
         // Serialize null to File
         writer.write((ISEDDebugTarget[])null, SEDXMLWriter.DEFAULT_ENCODING, workspaceFile);
         // Read launch from File
         try {
            read = reader.read(new FileInputStream(tempFile));
            fail("Reading an empty String should not be possible.");
         }
         catch (Exception e) {
         }
      }
      finally {
         defaultPerspective.activate();
         SEDPreferenceUtil.setShowCompactExecutionTree(originalCompactView);
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
         if (tempFile != null) {
            tempFile.delete();
         }
      }
   }
}
