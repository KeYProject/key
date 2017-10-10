package org.key_project.sed.key.ui.test.testcase.swtbot;

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
import org.eclipse.ui.IViewPart;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.decorator.ProofSourceViewerDecorator;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.core.test.testcase.swtbot.AbstractKeYDebugTargetTestCase;
import org.key_project.sed.key.ui.test.Activator;
import org.key_project.sed.key.ui.view.ProofView;
import org.key_project.ui.test.util.TestKeYUIUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Tests the {@link ProofView}.
 * @author Seena Vellaramkalayil
 */
public class SWTBotProofViewTest extends AbstractKeYDebugTargetTestCase {
   
   /**
    * tests the auto mode toolbar buttons in the view.
    * @throws Exception
    */
   public void testAutoMode() throws Exception {
	   
      IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor() {

         @Override
         public void configureDebugPerspective(SWTWorkbenchBot bot) throws Exception {
            TestUtilsUtil.openView(ProofView.VIEW_ID);
         }

         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project,
               IMethod method, String targetName, SWTBotView debugView,
               SWTBotTree debugTree, ISEDebugTarget target, ILaunch launch)
               throws Exception {
            SWTBotView view = getProofBotView(bot);
            ProofView proofView = getProofView(view);
            debugView.bot().tree().select(0);
            assertNotNull(proofView.getCurrentProof());
            assertTrue(!proofView.getCurrentProof().closed());
            //make sure that both buttons are visible and correctly enabled
            assertTrue(view.toolbarButton("Starts the proof auto mode with the current specification.").isVisible());
            assertTrue(view.toolbarButton("Starts the proof auto mode with the current specification.").isEnabled());
            assertTrue(view.toolbarButton("Stops the automode.").isVisible());
            assertFalse(view.toolbarButton("Stops the automode.").isEnabled());
            //start auto mode
            TestUtilsUtil.clickDirectly(view.toolbarButton("Starts the proof auto mode with the current specification."));
            TestKeYUIUtil.waitWhileAutoMode(bot, proofView.getEnvironment().getUi());
            assertFalse(proofView.getCurrentProof().closed());
            bot.waitWhile(Conditions.widgetIsEnabled(view.toolbarButton("Stops the automode.")));
            bot.waitUntil(Conditions.widgetIsEnabled(view.toolbarButton("Starts the proof auto mode with the current specification.")));
            //make sure that auto mode can be started again
            assertTrue(view.toolbarButton("Starts the proof auto mode with the current specification.").isEnabled()); 
            assertFalse(view.toolbarButton("Stops the automode.").isEnabled());
            view.close();
         }

         @Override
         public void cleanupDebugPerspective(SWTWorkbenchBot bot) throws Exception {
            IViewPart view = TestUtilsUtil.findView(ProofView.VIEW_ID);
            if (view != null) {
               TestUtilsUtil.closeView(view);
            }
         }
         
      };
      doKeYDebugTargetTest("SWTBotProofViewTest_testAutoMode", 
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
                           Boolean.FALSE,
                           10, 
                           executor);
   }
	
	/**
	 * tests the filter features of the {@link ProofView}
	 * 
	 * @throws Exception
	 */
	@Test
	public void testFilters() throws Exception {
		IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor() {

			@Override
			public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDebugTarget target, ILaunch launch) throws Exception {
				SWTBotView proofView = getProofBotView(bot);
				TestUtilsUtil.waitForJobs();
				// activate show symbolic execution tree filter
				TestUtilsUtil.sleep(1000);
				TestUtilsUtil.selectInTree(proofView.bot().tree(), 0);
				TestUtilsUtil.clickContextMenu(proofView.bot().tree(), "Show Symbolic Execution Tree Only");
				// step into
				performStep(debugView, bot, target, 0, 0, 0);
				// check if show symbolic execution tree filter is working
				assertTrue(proofView.bot().tree().getTreeItem("0:One Step Simplification: 1 rule") != null);
				assertTrue(proofView.bot().tree().getTreeItem("8:result=self.equals(n)@Number;") != null);
				assertTrue(proofView.bot().tree().rowCount() == 2);
				// deactivate show symbolic execution tree filter
				TestUtilsUtil.clickContextMenu(proofView.bot().tree(), "Show Symbolic Execution Tree Only");
				// activate hide intermediate proof steps filter
				TestUtilsUtil.clickContextMenu(proofView.bot().tree(), "Hide Intermediate Proofsteps");
				// check if hide intermediate proof steps filter is working
				assertTrue(proofView.bot().tree().getTreeItem("10:OPEN GOAL") != null);
				assertTrue(proofView.bot().tree().rowCount() == 1);
				// select open goal and apply manual rule
				TestUtilsUtil.selectInTree(proofView.bot().tree(), "10:OPEN GOAL");
            TestSedCoreUtil.waitForDebugTreeInterface();
				final SWTBotStyledText styledText = proofView.bot().styledText();
				Point point = TestUtilsUtil.selectText(styledText, "if (this.content==n.content)");
				TestUtilsUtil.setCursorLocation(styledText, point.x + 1, point.y + 15);
				TestUtilsUtil.clickContextMenu(styledText, point.x + 1, point.y + 15, "ifElseUnfold");
            TestSedCoreUtil.waitForDebugTreeInterface();
				// check if hide intermediate proof steps filter is still
				// working
				assertTrue(proofView.bot().tree().getTreeItem("11:OPEN GOAL") != null);
				assertTrue(proofView.bot().tree().rowCount() == 1);
				// deactivate hide intermediate proof steps filter
				TestUtilsUtil.clickContextMenu(proofView.bot().tree(), "Hide Intermediate Proofsteps");
				// activate show symbolic execution tree filter
				TestUtilsUtil.clickContextMenu(proofView.bot().tree(), "Show Symbolic Execution Tree Only");
				// check if show symbolic execution tree filter is working
				assertTrue(proofView.bot().tree().getTreeItem("0:One Step Simplification: 1 rule") != null);
				assertTrue(proofView.bot().tree().getTreeItem("8:result=self.equals(n)@Number;") != null);
				assertTrue(proofView.bot().tree().getTreeItem("10:if (this.content==n.content) {                         return  true; }                 else  {                         return  false; }") != null);
				assertTrue(proofView.bot().tree().rowCount() == 3);
				// deactivate show symbolic execution tree filter
				TestUtilsUtil.clickContextMenu(proofView.bot().tree(), "Show Symbolic Execution Tree Only");
				// close the bot view
				proofView.close();
			}

			@Override
			public void configureDebugPerspective(SWTWorkbenchBot bot) throws Exception {
				TestUtilsUtil.openView(ProofView.VIEW_ID);
			}

			@Override
			public void cleanupDebugPerspective(SWTWorkbenchBot bot) throws Exception {
				TestUtilsUtil.closeView(ProofView.VIEW_ID);
			}
		};
		doKeYDebugTargetTest("SWTBotProofViewTest_testFilters", 
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
                Boolean.FALSE,
                10, 
                executor);
	}
   
   /**
    * tests the manual rule application feature of the {@link ProofView}.
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
            TestSedCoreUtil.waitForDebugTreeInterface();
            SWTBotView proofView = getProofBotView(bot);
            int count = proofView.bot().tree().rowCount();
            assertEquals(1, count);
            proofView.bot().tree().select(count - 1);
            final SWTBotStyledText styledText0 = proofView.bot().styledText();
            Point point0 = TestUtilsUtil.selectText(styledText0, "well");
            TestUtilsUtil.setCursorLocation(styledText0, ((int) (point0.x * 0.3)), point0.y);
            TestUtilsUtil.clickContextMenu(styledText0,  ((int) (point0.x * 0.3)), point0.y, "impRight");
            TestSedCoreUtil.waitForDebugTreeInterface();
            assertEquals(count + 1, proofView.bot().tree().rowCount());
            //step into and check if the same proof is still loaded on both views
            performStep(debugView, bot, target, 0, 0, 0);
            ProofView view = getProofView(proofView);
            assertSameProof(target, view);
            //test if manual rule application is still working correctly
            count = proofView.bot().tree().rowCount();
            proofView.bot().tree().select(count - 1);
            assertTrue(proofView.bot().tree().getTreeItem("10:OPEN GOAL") != null);
            final SWTBotStyledText styledText = proofView.bot().styledText();
            Point point = TestUtilsUtil.selectText(styledText, "if (this.content==n.content)");
            TestUtilsUtil.setCursorLocation(styledText, point.x + 1, point.y + 15);
            TestUtilsUtil.clickContextMenu(styledText, point.x + 1, point.y + 15, "ifElseUnfold");
            TestSedCoreUtil.waitForDebugTreeInterface();
            assertEquals(count + 1, proofView.bot().tree().rowCount());
            //make sure that new node is loaded in debugView
            TestSedCoreUtil.waitForDebugTreeInterface();
            assertNotNull(TestSedCoreUtil.selectInDebugTree(debugView, 0, 0, 0, 1));
            //close the bot view
            proofView.close();
            assertFalse(((KeYDebugTarget) target).getProof().isDisposed());
         }
         
         @Override
         public void configureDebugPerspective(SWTWorkbenchBot bot) throws Exception {
            TestUtilsUtil.openView(ProofView.VIEW_ID);
         }
         
         @Override
         public void cleanupDebugPerspective(SWTWorkbenchBot bot) throws Exception {
            TestUtilsUtil.closeView(ProofView.VIEW_ID);
         }
      };
      doKeYDebugTargetTest("SWTBotProofViewTest_testRuleApplication", 
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
                           Boolean.FALSE,
                           10, 
                           executor);
   }
   
   /**
    * tests the correct function of the {@link ProofView} when "step into" ans "resume" is performed.
    * @throws Exception
    */
   public void testViewSteps() throws Exception {
         IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor() {

            @Override
            public void configureDebugPerspective(SWTWorkbenchBot bot) throws Exception {
               TestUtilsUtil.openView(ProofView.VIEW_ID);
            }

            @Override
            public void test(SWTWorkbenchBot bot, IJavaProject project,
                  IMethod method, String targetName, SWTBotView debugView,
                  SWTBotTree debugTree, ISEDebugTarget target, ILaunch launch)
                  throws Exception {
               //step into the proof and check if loaded proof is the same on debugView and proofView
               performStep(debugView, bot, target, 0, 0, 0);
               SWTBotView proofView = getProofBotView(bot);
               ProofView view = getProofView(proofView);
               assertSameProof(target, view);
               performStep(debugView, bot, target, 0, 0, 0, 0);
               proofView = getProofBotView(bot);
               assertSameProof(target, view);
               proofView.close();
            }

            @Override
            public void cleanupDebugPerspective(SWTWorkbenchBot bot) throws Exception {
               IViewPart view = TestUtilsUtil.findView(ProofView.VIEW_ID);
               if (view != null) {
                  TestUtilsUtil.closeView(view);
               }
            }
            
         };
         doKeYDebugTargetTest("SWTBotProofViewTest_testViewSteps", 
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
               Boolean.FALSE,
               10, 
               executor);
   }
   
   /**
    * tests the correct display of the nodes in the {link {@link ProofView#getSourceViewer()}.
    * @throws Exception
    */
   public void testSourceViewer() throws Exception {
      IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor() {

         @Override
         public void configureDebugPerspective(SWTWorkbenchBot bot) throws Exception {
            TestUtilsUtil.openView(ProofView.VIEW_ID);
         }

         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project,
               IMethod method, String targetName, SWTBotView debugView,
               SWTBotTree debugTree, ISEDebugTarget target, ILaunch launch)
               throws Exception {
            //step into the proof
            performStep(debugView, bot, target, 0, 0, 0);
            SWTBotView proofView = getProofBotView(bot);
            ProofView view = getProofView(proofView);
            int count = proofView.bot().tree().rowCount();
            proofView.bot().tree().select(count - 1);
            assertTrue(proofView.bot().tree().getTreeItem("10:OPEN GOAL") != null);
            assertTrue(proofView.bot().tree().getTreeItem("10:OPEN GOAL").isSelected());
            //get the node that is selected
            Node goal = view.getCurrentProof().openGoals().head().node();
            IdentitySequentPrintFilter filter = new IdentitySequentPrintFilter();
            filter.setSequent(goal.sequent());
            LogicPrinter printer = new SequentViewLogicPrinter(new ProgramPrinter(null), 
                                                               SymbolicExecutionUtil.createNotationInfo(view.getCurrentProof()), 
                                                               goal.proof().getServices(),
                                                               view.getUI().getTermLabelVisibilityManager());
            //check if source viewer is showing the content correctly
            assertEquals(proofView.bot().styledText().getText(), 
                         ProofSourceViewerDecorator.computeText(SymbolicExecutionUtil.createNotationInfo(view.getCurrentProof()), goal, filter, printer));
            proofView.close();
            
            
         }

         @Override
         public void cleanupDebugPerspective(SWTWorkbenchBot bot) throws Exception {
            IViewPart view = TestUtilsUtil.findView(ProofView.VIEW_ID);
            if (view != null) {
               TestUtilsUtil.closeView(view);
            }
         }
         
      };
      doKeYDebugTargetTest("SWTBotProofViewTest_testSourceViewer", 
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
            Boolean.FALSE,
            10, 
            executor);
      
   }
   
   /**
    * tests of the loaded proof in the {@link ISEDebugTarget} is the same as the one in the {@link ProofView}.
    * @param target the {@link ISEDebugTarget} to check
    * @param view the {@link ProofView} to check
    */
   private void assertSameProof(ISEDebugTarget target, ProofView view) {
      assertTrue(target instanceof KeYDebugTarget);
      assertEquals(((KeYDebugTarget) target).getProof(), view.getCurrentProof());
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
    * returns the {@link SWTBotView} of the {@link SWTWorkbenchBot} with ID {@link ProofView#VIEW_ID}.
    * @param bot the {@link SWTWorkbenchBot} to use
    * @return the {@link SWTBotView} with {@link ProofView#VIEW_ID}
    */
   private SWTBotView getProofBotView(SWTWorkbenchBot bot) {
      SWTBotView proofView = bot.viewById(ProofView.VIEW_ID);
      return proofView;
   }
   
   /**
    * returns the {@link ProofView} applicable to the given {@link SWTBotView}.
    * @param view the {@link SWTBotView} to extract the {@link ProofView} from
    * @return the extracted {@link ProofView}
    */
   private ProofView getProofView(SWTBotView view) {
      assertNotNull(view);
      IViewPart newView = view.getReference().getView(true);
      assertTrue(newView instanceof ProofView);
      return (ProofView) newView;
   }
}
