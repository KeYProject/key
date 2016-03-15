package org.key_project.sed.key.ui.test.testcase.swtbot;


import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotStyledText;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.eclipse.ui.IViewPart;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.decorator.ProofSourceViewerDecorator;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.core.test.testcase.swtbot.AbstractKeYDebugTargetTestCase;
import org.key_project.sed.key.ui.test.Activator;
import org.key_project.sed.key.ui.view.ManualView;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Tests the {@link ManualView}.
 * @author Seena Vellaramkalayil
 *
 */
public class SWTBotManualViewTest extends AbstractKeYDebugTargetTestCase {
   
   /**
    * tests the manual rule application feature of the {@link ManualView}
    * @throws Exception
    */
   @Test
   public void testRuleApplication() throws Exception {
      IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor() {
         
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method,
               String targetName, SWTBotView debugView, SWTBotTree debugTree,
               ISEDebugTarget target, ILaunch launch) throws Exception {
            //test if manual rule application functions before stepping into the proof
            SWTBotView manualView = getManualBotView(bot);
            int count = manualView.bot().tree().rowCount();
            manualView.bot().tree().select(count-1);
            final SWTBotStyledText styledText0 = manualView.bot().styledText();
            Point point0 = TestUtilsUtil.selectText(styledText0, "well");
            TestUtilsUtil.setCursorLocation(styledText0, ((int)(point0.x * 0.3)), point0.y);
            TestUtilsUtil.clickContextMenu(styledText0,  ((int)(point0.x * 0.3)), point0.y, "impRight");
            assertTrue((count + 1) == manualView.bot().tree().rowCount());
            //step into and check if the same proof is still loaded on both views
            performStep(debugView, bot, target, 0, 0, 0);
            ManualView view = getManualView(manualView);
            assertSameProof(target, view);
            //test if manual rule application is still working correctly
            count = manualView.bot().tree().rowCount();
            manualView.bot().tree().select(count-1);
            assertTrue(manualView.bot().tree().getTreeItem("10:OPEN GOAL") != null);
            final SWTBotStyledText styledText = manualView.bot().styledText();
            Point point = TestUtilsUtil.selectText(styledText, "{exc:=null}");
            TestUtilsUtil.setCursorLocation(styledText, point.x + 1, point.y + 15);
            TestUtilsUtil.clickContextMenu(styledText, point.x + 1, point.y + 15, "ifElseUnfold");
            assertTrue((count + 1)==manualView.bot().tree().rowCount());
            //close the bot view
            manualView.close();
            assertFalse(((KeYDebugTarget)target).getProof().isDisposed());
         }
         
         @Override
         public void configureDebugPerspective(SWTWorkbenchBot bot,
               IPerspectiveDescriptor debugPerspective) throws Exception {
            TestUtilsUtil.openView(ManualView.VIEW_ID);
         }
         
         @Override
         public void cleanupDebugPerspective(SWTWorkbenchBot bot,
               IPerspectiveDescriptor debugPerspective) throws Exception {
            TestUtilsUtil.closeView(ManualView.VIEW_ID);
         }
      };
      doKeYDebugTargetTest("SWTBotManualViewTest_testRuleApplication", 
                           Activator.PLUGIN_ID, 
                           "data/number/test", 
                           true, 
                           true, 
                           createMethodSelector("Number", "equals", "QNumber;"), 
                           null, 
                           null, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.FALSE, 
                           Boolean.TRUE, 
                           10, 
                           executor);
   }
   
   /**
    * tests the correct function of the {@link ManualView} when "step into" ans "resume" is performed.
    * @throws Exception
    */
   public void testViewSteps() throws Exception {
         IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor() {

            @Override
            public void configureDebugPerspective(SWTWorkbenchBot bot,
                  IPerspectiveDescriptor debugPerspective) throws Exception {
               TestUtilsUtil.openView(ManualView.VIEW_ID);
            }

            @Override
            public void test(SWTWorkbenchBot bot, IJavaProject project,
                  IMethod method, String targetName, SWTBotView debugView,
                  SWTBotTree debugTree, ISEDebugTarget target, ILaunch launch)
                  throws Exception {
               //step into the proof and check if loaded proof is the same on debugView and manualView
               performStep(debugView, bot, target, 0, 0, 0);
               SWTBotView manualView = getManualBotView(bot);
               ManualView view = getManualView(manualView);
               assertSameProof(target, view);
               performStep(debugView, bot, target, 0, 0, 0, 0);
               manualView = getManualBotView(bot);
               assertSameProof(target, view);
               manualView.close();
            }

            @Override
            public void cleanupDebugPerspective(SWTWorkbenchBot bot,
                  IPerspectiveDescriptor debugPerspective) throws Exception {
               if (TestUtilsUtil.findView(ManualView.VIEW_ID) != null) {
                  TestUtilsUtil.closeView(ManualView.VIEW_ID);
               }
            }
            
         };
         doKeYDebugTargetTest("SWTBotManualViewTest_testViewSteps", 
               Activator.PLUGIN_ID, 
               "data/number/test", 
               true, 
               true, 
               createMethodSelector("Number", "equals", "QNumber;"), 
               null, 
               null, 
               Boolean.FALSE, 
               Boolean.FALSE, 
               Boolean.FALSE, 
               Boolean.FALSE, 
               Boolean.FALSE, 
               Boolean.FALSE, 
               Boolean.FALSE, 
               Boolean.FALSE, 
               Boolean.FALSE, 
               Boolean.TRUE, 
               10, 
               executor);
   }
   
   /**
    * tests the correct display of the nodes in the {link {@link ManualView#getSourceViewer()}.
    * @throws Exception
    */
   public void testSourceViewer() throws Exception {
      IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor() {

         @Override
         public void configureDebugPerspective(SWTWorkbenchBot bot,
               IPerspectiveDescriptor debugPerspective) throws Exception {
            TestUtilsUtil.openView(ManualView.VIEW_ID);
         }

         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project,
               IMethod method, String targetName, SWTBotView debugView,
               SWTBotTree debugTree, ISEDebugTarget target, ILaunch launch)
               throws Exception {
            //step into the proof
            performStep(debugView, bot, target, 0, 0, 0);
            SWTBotView manualView = getManualBotView(bot);
            ManualView view = getManualView(manualView);
            int count = manualView.bot().tree().rowCount();
            manualView.bot().tree().select(count-1);
            assertTrue(manualView.bot().tree().getTreeItem("10:OPEN GOAL") != null);
            assertTrue(manualView.bot().tree().getTreeItem("10:OPEN GOAL").isSelected());
            //get the node that is selected
            Node goal = view.getProof().openGoals().head().node();
            IdentitySequentPrintFilter filter = new IdentitySequentPrintFilter(goal.sequent());
            LogicPrinter printer = new LogicPrinter(new ProgramPrinter(null), 
                                       SymbolicExecutionUtil.createNotationInfo(view.getProof()), 
                                       goal.proof().getServices());
            //check if source viewer is showing the content correctly
            assertEquals(manualView.bot().styledText().getText(), 
                         ProofSourceViewerDecorator.computeText(SymbolicExecutionUtil.createNotationInfo(view.getProof()), goal, filter, printer));
            manualView.close();
            
            
         }

         @Override
         public void cleanupDebugPerspective(SWTWorkbenchBot bot,
               IPerspectiveDescriptor debugPerspective) throws Exception {
            if (TestUtilsUtil.findView(ManualView.VIEW_ID) != null) {
               TestUtilsUtil.closeView(ManualView.VIEW_ID);
            }
         }
         
      };
      doKeYDebugTargetTest("SWTBotManualViewTest_testSourceViewer", 
            Activator.PLUGIN_ID, 
            "data/number/test", 
            true, 
            true, 
            createMethodSelector("Number", "equals", "QNumber;"), 
            null, 
            null, 
            Boolean.FALSE, 
            Boolean.FALSE, 
            Boolean.FALSE, 
            Boolean.FALSE, 
            Boolean.FALSE, 
            Boolean.FALSE, 
            Boolean.FALSE, 
            Boolean.FALSE, 
            Boolean.FALSE, 
            Boolean.TRUE, 
            10, 
            executor);
      
   }
   
   /**
    * tests of the loaded proof in the {@link ISEDebugTarget} is the same as the one in the {@link ManualView}.
    * @param target
    * @param view
    */
   private void assertSameProof(ISEDebugTarget target, ManualView view){
      assertTrue(target instanceof KeYDebugTarget);
      assertEquals(((KeYDebugTarget) target).getProof(), view.getProof());
   }
   
   /**
    * performs a step into the proof tree.
    * @param debugView
    * @param bot
    * @param target
    * @param indexPathToItem
    * @return 
    * @throws DebugException
    */
   private void performStep(SWTBotView debugView, SWTWorkbenchBot bot, ISEDebugTarget target, int... indexPathToItem) throws DebugException {
      SWTBotTreeItem debugItem = TestSedCoreUtil.selectInDebugTree(debugView, indexPathToItem);
      stepInto(bot, debugItem, target);
   }
   
   /**
    * returns the {@link SWTBotView} that belongs to the {@link ManualView}.
    * @param bot
    * @return
    */
   private SWTBotView getManualBotView(SWTWorkbenchBot bot) {
      SWTBotView manualView = bot.viewById(ManualView.VIEW_ID);
      return manualView;
   }
   /**
    * returns the {link ManualView} applicable to the given {@link SWTBotView}.
    * @param view
    * @return
    */
   private ManualView getManualView(SWTBotView view) {
      assertNotNull(view);
      IViewPart newView = view.getReference().getView(true);
      assertTrue(newView instanceof ManualView);
      return (ManualView)newView;
   }
   

}
