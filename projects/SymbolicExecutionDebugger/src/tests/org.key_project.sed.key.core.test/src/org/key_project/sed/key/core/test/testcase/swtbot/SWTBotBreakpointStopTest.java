package org.key_project.sed.key.core.test.testcase.swtbot;

import org.eclipse.debug.core.ILaunch;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.test.util.TestSedCoreUtil;

public class SWTBotBreakpointStopTest extends AbstractKeYDebugTargetTestCase {

   @Test
   public void testDifferentValues() throws Exception {
      IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor(){

         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project,
               IMethod method, String targetName, SWTBotView debugView,
               SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch)
               throws Exception {
            try{
            // Get debug target TreeItem
               SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0); // Select thread
            // Test initial debug target
               String expectedModelPathInBundle = "data/lineBreakpointsWithHitcountTest/oracle/BreakpointStop";
               String expectedModelFileExtension = ".xml";
               int modelIndex = 0;
               assertResume(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension);
               assertResume(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension);
               assertResume(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension);
               assertResume(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension);
               assertResume(bot, item, target, expectedModelPathInBundle, ++modelIndex, expectedModelFileExtension);
            }
            finally{
               
            }
            
            
         }};   
         doKeYDebugTargetTest("SWTBotBreakpointStopTest_lineBreakpointsAndHitcount",
               "data/lineBreakpointsWithHitcountTest/test",
               true,
               true,
               createMethodSelector("BreakpointStopCallerAndLoop", "main"),
               null,
               null,
               Boolean.FALSE,
               Boolean.FALSE,
               Boolean.FALSE,
               Boolean.FALSE,
               8,
               executor);
   }
}
