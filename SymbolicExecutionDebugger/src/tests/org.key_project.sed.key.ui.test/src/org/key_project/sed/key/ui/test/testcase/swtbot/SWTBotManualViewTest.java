package org.key_project.sed.key.ui.test.testcase.swtbot;


import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.State;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotStyledText;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.handlers.RegistryToggleState;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.decorator.ProofSourceViewerDecorator;
import org.key_project.keyide.ui.handlers.HideIntermediateProofstepsHandler;
import org.key_project.keyide.ui.handlers.ShowSymbolicExecutionTreeOnlyHandler;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.core.test.testcase.swtbot.AbstractKeYDebugTargetTestCase;
import org.key_project.sed.key.ui.test.Activator;
import org.key_project.sed.key.ui.view.ManualView;
import org.key_project.ui.test.util.TestKeYUIUtil;
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
    * tests the auto mode toolbar buttons in the view.
    * @throws Exception
    */
   public void testAutoMode() throws Exception {
	   
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
            SWTBotView view = getManualBotView(bot);
            ManualView manualView = getManualView(view);
            debugView.bot().tree().select(0);
            assertNotNull(manualView.getProof());
            assertTrue(!manualView.getProof().closed());
            //make sure that both buttons are visible and correctly enabled
            assertTrue(view.toolbarButton("Start Auto Mode").isVisible());
            assertTrue(view.toolbarButton("Start Auto Mode").isEnabled());
            assertTrue(view.toolbarButton("Stop Auto Mode").isVisible());
            assertFalse(view.toolbarButton("Stop Auto Mode").isEnabled());
            //start auto mode
            TestUtilsUtil.clickDirectly(view.toolbarButton("Start Auto Mode"));
            TestKeYUIUtil.waitWhileAutoMode(bot, manualView.getEnvironment().getUi());
            assertFalse(manualView.getProof().closed());
            bot.waitWhile(Conditions.widgetIsEnabled(view.toolbarButton("Stop Auto Mode")));
            bot.waitUntil(Conditions.widgetIsEnabled(view.toolbarButton("Start Auto Mode")));
            //make sure that auto mode can be started again
            assertTrue(view.toolbarButton("Start Auto Mode").isEnabled()); 
            assertFalse(view.toolbarButton("Stop Auto Mode").isEnabled());
            view.close();
         }

         @Override
         public void cleanupDebugPerspective(SWTWorkbenchBot bot,
               IPerspectiveDescriptor debugPerspective) throws Exception {
            if (TestUtilsUtil.findView(ManualView.VIEW_ID) != null) {
               TestUtilsUtil.closeView(ManualView.VIEW_ID);
            }
         }
         
      };
      doKeYDebugTargetTest("SWTBotManualViewTest_testAutoMode", 
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
	 * tests the filter features of the {@link ManualView}
	 * 
	 * @throws Exception
	 */
	@Test
	public void testFilters() throws Exception {
		IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor() {

			@Override
			public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDebugTarget target, ILaunch launch) throws Exception {
				SWTBotView manualView = getManualBotView(bot);
				TestUtilsUtil.waitForJobs();
				// activate show symbolic execution tree filter
				TestUtilsUtil.sleep(1000);
				TestUtilsUtil.selectInTree(manualView.bot().tree(), 0);
				TestUtilsUtil.clickContextMenu(manualView.bot().tree(), "Show Symbolic Execution Tree Only");
				// step into
				performStep(debugView, bot, target, 0, 0, 0);
				// check if show symbolic execution tree filter is working
				assertTrue(manualView.bot().tree().getTreeItem("0:One Step Simplification: 1 rule") != null);
				assertTrue(manualView.bot().tree().getTreeItem("8:result=self.equals(n)@Number;") != null);
				assertTrue(manualView.bot().tree().rowCount() == 2);
				// deactivate show symbolic execution tree filter
				TestUtilsUtil.clickContextMenu(manualView.bot().tree(), "Show Symbolic Execution Tree Only");
				// activate hide intermediate proof steps filter
				TestUtilsUtil.clickContextMenu(manualView.bot().tree(), "Hide Intermediate Proofsteps");
				// check if hide intermediate proof steps filter is working
				assertTrue(manualView.bot().tree().getTreeItem("10:OPEN GOAL") != null);
				assertTrue(manualView.bot().tree().rowCount() == 1);
				// select open goal and apply manual rule
				TestUtilsUtil.selectInTree(manualView.bot().tree(), "10:OPEN GOAL");
				final SWTBotStyledText styledText = manualView.bot().styledText();
				Point point = TestUtilsUtil.selectText(styledText, "{exc:=null}");
				TestUtilsUtil.setCursorLocation(styledText, point.x + 1, point.y + 15);
				TestUtilsUtil.clickContextMenu(styledText, point.x + 1, point.y + 15, "ifElseUnfold");
				// check if hide intermediate proof steps filter is still
				// working
				assertTrue(manualView.bot().tree().getTreeItem("11:OPEN GOAL") != null);
				assertTrue(manualView.bot().tree().rowCount() == 1);
				// deactivate hide intermediate proof steps filter
				TestUtilsUtil.clickContextMenu(manualView.bot().tree(), "Hide Intermediate Proofsteps");
				// activate show symbolic execution tree filter
				TestUtilsUtil.clickContextMenu(manualView.bot().tree(), "Show Symbolic Execution Tree Only");
				// check if show symbolic execution tree filter is working
				assertTrue(manualView.bot().tree().getTreeItem("0:One Step Simplification: 1 rule") != null);
				assertTrue(manualView.bot().tree().getTreeItem("8:result=self.equals(n)@Number;") != null);
				assertTrue(manualView.bot().tree().getTreeItem("10:if (this.content==n.content) {                         return  true; }                 else  {                         return  false; }") != null);
				assertTrue(manualView.bot().tree().rowCount() == 3);
				// deactivate show symbolic execution tree filter
				TestUtilsUtil.clickContextMenu(manualView.bot().tree(), "Show Symbolic Execution Tree Only");
				// close the bot view
				manualView.close();
			}

			@Override
			public void configureDebugPerspective(SWTWorkbenchBot bot, IPerspectiveDescriptor debugPerspective) throws Exception {
				TestUtilsUtil.openView(ManualView.VIEW_ID);
			}

			@Override
			public void cleanupDebugPerspective(SWTWorkbenchBot bot, IPerspectiveDescriptor debugPerspective) throws Exception {
				TestUtilsUtil.closeView(ManualView.VIEW_ID);
			}
		};
		doKeYDebugTargetTest("SWTBotManualViewTest_testFilters", 
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
    * tests the manual rule application feature of the {@link ManualView}.
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
            manualView.bot().tree().select(count - 1);
            final SWTBotStyledText styledText0 = manualView.bot().styledText();
            Point point0 = TestUtilsUtil.selectText(styledText0, "well");
            TestUtilsUtil.setCursorLocation(styledText0, ((int) (point0.x * 0.3)), point0.y);
            TestUtilsUtil.clickContextMenu(styledText0,  ((int) (point0.x * 0.3)), point0.y, "impRight");
            assertTrue((count + 1) == manualView.bot().tree().rowCount());
            //step into and check if the same proof is still loaded on both views
            performStep(debugView, bot, target, 0, 0, 0);
            ManualView view = getManualView(manualView);
            assertSameProof(target, view);
            //test if manual rule application is still working correctly
            count = manualView.bot().tree().rowCount();
            manualView.bot().tree().select(count - 1);
            assertTrue(manualView.bot().tree().getTreeItem("10:OPEN GOAL") != null);
            final SWTBotStyledText styledText = manualView.bot().styledText();
            Point point = TestUtilsUtil.selectText(styledText, "{exc:=null}");
            TestUtilsUtil.setCursorLocation(styledText, point.x + 1, point.y + 15);
            TestUtilsUtil.clickContextMenu(styledText, point.x + 1, point.y + 15, "ifElseUnfold");
            assertTrue((count + 1) == manualView.bot().tree().rowCount());
            //make sure that new node is loaded in debugView
            TestSedCoreUtil.waitForDebugTreeInterface();
            assertNotNull(TestSedCoreUtil.selectInDebugTree(debugView, 0, 0, 0, 1));
            //close the bot view
            manualView.close();
            assertFalse(((KeYDebugTarget) target).getProof().isDisposed());
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
            manualView.bot().tree().select(count - 1);
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
    * Tests whether enabling the subtree filter works as expected.
    * @throws Exception
    */
   @Test
   public void testSubTreeFilterEnabled() throws Exception {
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
            SWTBotView manualView = getManualBotView(bot);
            //start auto mode.
            TestUtilsUtil.clickDirectly(manualView.toolbarPushButton("Start Auto Mode"));
            TestKeYUIUtil.waitWhileAutoMode(bot, getManualView(manualView).getEnvironment().getUi());
            
            //navigate to some location
            SWTBotTreeItem subtree = manualView.bot().tree().getTreeItem("Normal Execution (n != null)").getNode("if x true").getNode("163:One Step Simplification: 7 rules");
            subtree.select();
            
            //filter out the rest of the tree
            TestUtilsUtil.clickDirectly(manualView.toolbarToggleButton("Show Subtree of Node"));
            //subtree length should be 11
            assert(manualView.bot().tree().getAllItems().length == 11);
            
            TestUtilsUtil.clickDirectly(manualView.toolbarToggleButton("Show Subtree of Node"));
            
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
    * Tests whether enabling and then disabling the subtree filter works as expected.
    * @throws Exception
    */
   @Test
   //TODO
   public void testSubTreeFilterDisabled() throws Exception{
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
            SWTBotView manualView = getManualBotView(bot);
            //start auto mode.
            TestUtilsUtil.clickDirectly(manualView.toolbarPushButton("Start Auto Mode"));
            TestKeYUIUtil.waitWhileAutoMode(bot, getManualView(manualView).getEnvironment().getUi());
            
            //navigate to some location
            SWTBotTreeItem subtree = manualView.bot().tree().getTreeItem("Normal Execution (n != null)").getNode("if x true").getNode("163:One Step Simplification: 7 rules");
            subtree.select();

            //subtree length should be 21 - only counting one level of the tree
            assert(manualView.bot().tree().getAllItems().length == 21);
            
            //briefly filter out the rest of the tree
            TestUtilsUtil.clickDirectly(manualView.toolbarToggleButton("Show Subtree of Node"));
            TestUtilsUtil.clickDirectly(manualView.toolbarToggleButton("Show Subtree of Node"));

            //subtree length should be 21 again
            assert(manualView.bot().tree().getAllItems().length == 21);
            
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
    * @param target the {@link ISEDebugTarget} to check
    * @param view the {@link ManualView} to check
    */
   private void assertSameProof(ISEDebugTarget target, ManualView view) {
      assertTrue(target instanceof KeYDebugTarget);
      assertEquals(((KeYDebugTarget) target).getProof(), view.getProof());
   }
   
   /**
    * performs a step into the proof tree.
    * @param debugView the view to get the item to step into
    * @param bot the{@link SWTWorkbenchBot} to use
    * @param target the {@link ISEDebugTarget} to use for the step
    * @param indexPathToItem the indices of the parents to select in debug tree
    * @return 
    * @throws DebugException
    */
   private void performStep(SWTBotView debugView, SWTWorkbenchBot bot, ISEDebugTarget target, int... indexPathToItem) throws DebugException {
      SWTBotTreeItem debugItem = TestSedCoreUtil.selectInDebugTree(debugView, indexPathToItem);
      stepInto(bot, debugItem, target);
   }
   
   /**
    * returns the {@link SWTBotView} of the {@link SWTWorkbenchBot} with ID {@link ManualView#VIEW_ID}.
    * @param bot the {@link SWTWorkbenchBot} to use
    * @return the {@link SWTBotView} with {@link ManualView#VIEW_ID}
    */
   private SWTBotView getManualBotView(SWTWorkbenchBot bot) {
      SWTBotView manualView = bot.viewById(ManualView.VIEW_ID);
      return manualView;
   }
   /**
    * returns the {link ManualView} applicable to the given {@link SWTBotView}.
    * @param view the {@link SWTBotView} to extract the {@link ManualView} from
    * @return the extracted {@link ManualView}
    */
   private ManualView getManualView(SWTBotView view) {
      assertNotNull(view);
      IViewPart newView = view.getReference().getView(true);
      assertTrue(newView instanceof ManualView);
      return (ManualView) newView;
   }
   

}
