package org.key_project.sed.key.core.test.testcase.swtbot;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.debug.core.model.IVariable;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.junit.Test;
import org.key_project.sed.core.annotation.impl.SliceAnnotation;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.slicing.ISESlicer;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.core.slicing.KeYThinBackwardSlicer;
import org.key_project.sed.key.core.test.Activator;
import org.key_project.util.java.StringUtil;

/**
 * SWTBot tests for {@link KeYThinBackwardSlicer}.
 * @author Martin Hentschel
 */
public class SWTBotKeYThinBackwardSlicerTest extends AbstractKeYDebugTargetTestCase {
   /**
    * Tests slicing on example {@code simpleLocalVariables}.
    */
   @Test
   public void testSimpleLocalVariables() throws Exception {
      IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDebugTarget target, ILaunch launch) throws Exception {
            // Resume
            SWTBotTreeItem launchTreeItem = TestSedCoreUtil.selectInDebugTree(debugView, 0, 0);
            resume(bot, launchTreeItem, target);
            assertDebugTargetViaOracle(target, Activator.PLUGIN_ID, "data/simpleLocalVariables/oracle/SimpleLocalVariables.xml", true, false, false);
            // Find seed
            ISENode thread = target.getSymbolicThreads()[0];
            ISENode call = thread.getChildren()[0];
            ISENode xDecl = call.getChildren()[0];
            ISENode yDecl = xDecl.getChildren()[0];
            ISENode zDecl = yDecl.getChildren()[0];
            ISENode resultComp = zDecl.getChildren()[0];
            ISENode resultReturn = resultComp.getChildren()[0];
            IVariable seedVariable = ((IStackFrame) resultReturn).getVariables()[1];
            // Perform slicing
            ISESlicer slicer = target.getSlicer(resultReturn, seedVariable, KeYThinBackwardSlicer.NAME);
            assertNotNull(slicer);
            SliceAnnotation annotation = slicer.slice(resultReturn, seedVariable, null, null, new NullProgressMonitor());
            // Check slicing result
            assertEquals(1, target.getRegisteredAnnotations().length);
            assertSame(annotation, target.getRegisteredAnnotations()[0]);
            assertTrue(!StringUtil.isEmpty(annotation.getSeed()));
            assertEquals(3, annotation.getLinks().length);
            assertEquals(resultComp, annotation.getLinks()[0].getTarget());
            assertEquals(yDecl, annotation.getLinks()[1].getTarget());
            assertEquals(xDecl, annotation.getLinks()[2].getTarget());
         }
         
         @Override
         public void configureDebugPerspective(SWTWorkbenchBot bot, IPerspectiveDescriptor debugPerspective) throws Exception {
         }
         
         @Override
         public void cleanupDebugPerspective(SWTWorkbenchBot bot, IPerspectiveDescriptor debugPerspective) throws Exception {
         }
      };
      doKeYDebugTargetTest("SWTBotKeYThinBackwardSlicerTest_testSimpleLocalVariables", 
                           "data/simpleLocalVariables/test", 
                           true,
                           true,
                           createMethodSelector("SimpleLocalVariables", "main"), 
                           null,
                           null,
                           Boolean.FALSE, 
                           Boolean.TRUE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE, 
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.TRUE,
                           Boolean.FALSE,
                           14, 
                           executor);
   }
}
