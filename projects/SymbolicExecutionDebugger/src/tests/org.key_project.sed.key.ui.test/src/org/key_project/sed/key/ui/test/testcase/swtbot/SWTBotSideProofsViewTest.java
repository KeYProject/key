package org.key_project.sed.key.ui.test.testcase.swtbot;

import org.eclipse.debug.core.ILaunch;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.util.StarterPreferenceUtil;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.starter.KeYIDEProofStarter;
import org.key_project.keyide.ui.util.KeYIDEPreferences;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.ui.test.Activator;
import org.key_project.sed.key.ui.view.SideProofsView;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.SideProofStore;
import de.uka.ilkd.key.symbolic_execution.util.SideProofStore.Entry;

/**
 * Tests for {@link SideProofsView}.
 * @author Martin Hentschel
 */
public class SWTBotSideProofsViewTest extends AbstractSWTBotKeYPropertyTabTest {
   /**
    * Performs the following steps to test the functionality of {@link SideProofsView}.
    * <ol>
    *    <li>Perform symbolic execution without collecting side proofs.</li>
    *    <li>
    *       Perform symbolic execution and collecting side proofs.
    *       <ol>
    *          <li>Open collected side proofs in KeY IDE.</li>
    *          <li>Delete all collected side proofs.</li>
    *       </ol>
    *    </li>
    *    <li>Perform symbolic execution without collecting side proofs again.</li>
    * </ol>
    * @throws Exception Occurred Exception
    */
   @Test
   public void testCollectingOpeningAndDeletion() throws Exception {
      // Define required settings
      boolean originalEnabled = SideProofStore.DEFAULT_INSTANCE.isEnabled();
      SideProofStore.DEFAULT_INSTANCE.setEnabled(false);
      boolean originalDoNotAsk = StarterPreferenceUtil.isDontAskForProofStarter();
      String originalProofStarter = StarterPreferenceUtil.getSelectedProofStarterID();
      String originalSwitch = KeYIDEPreferences.getSwitchToKeyPerspective();
      StarterPreferenceUtil.setDontAskForProofStarter(true);
      StarterPreferenceUtil.setSelectedProofStarterID(KeYIDEProofStarter.STARTER_ID);
      KeYIDEPreferences.setSwitchToKeyPerspective(MessageDialogWithToggle.NEVER);
      try {
         // Test without collecting side proofs
         doKeYDebugTargetTest("SWTBotSideProofsViewTest_testCollectingOpeningAndDeletion1", 
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
                              Boolean.TRUE,
                              8, 
                              new SideProofsViewTestExecutor(false, false, 0, -1, new int[][] {}));
         // Test with collecting side proofs
         doKeYDebugTargetTest("SWTBotSideProofsViewTest_testCollectingOpeningAndDeletion2", 
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
                              Boolean.TRUE,
                              8, 
                              new SideProofsViewTestExecutor(true, true, 4, 0, new int[][] {{1}, {0, 2}, {0}}));
         // Test without collecting side proofs again
         doKeYDebugTargetTest("SWTBotSideProofsViewTest_testCollectingOpeningAndDeletion3", 
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
                              Boolean.TRUE,
                              8, 
                              new SideProofsViewTestExecutor(true, false, 0, -1, new int[][] {}));
      }
      finally {
         SideProofStore.DEFAULT_INSTANCE.setEnabled(originalEnabled);
         StarterPreferenceUtil.setDontAskForProofStarter(originalDoNotAsk);
         StarterPreferenceUtil.setSelectedProofStarterID(originalProofStarter);
         KeYIDEPreferences.setSwitchToKeyPerspective(originalSwitch);
      }
   }
   
   /**
    * The {@link IKeYDebugTargetTestExecutor} used by {@link SWTBotSideProofsViewTest#testCollectingOpeningAndDeletion()}.
    * @author Martin Hentschel
    */
   private static class SideProofsViewTestExecutor extends AbstractKeYDebugTargetTestExecutor {
      /**
       * Switch collecting side proofs.
       */
      private final boolean switchCollecting;

      /**
       * Expected collect side proofs value.
       */
      private final boolean expectedCollecting;
      
      /**
       * The expected number of collected side proofs.
       */
      private final int expectedSideProofsCount;
      
      /**
       * The index to open its proof or {@code -1} to not open.
       */
      private final int openProofAtIndex;
      
      /**
       * The indices to delete.
       */
      private final int[][] indicesToDelete;
      
      /**
       * Constructor.
       * @param switchCollecting Switch collecting side proofs.
       * @param expectedCollecting Expected collect side proofs value.
       * @param expectedSideProofsCount The expected number of collected side proofs.
       * @param openProofAtIndex The index to open its proof or {@code -1} to not open.
       * @param indicesToDelete The indices to delete.
       */
      public SideProofsViewTestExecutor(boolean switchCollecting, 
                                        boolean expectedCollecting, 
                                        int expectedSideProofsCount, 
                                        int openProofAtIndex, 
                                        int[][] indicesToDelete) {
         this.switchCollecting = switchCollecting;
         this.expectedCollecting = expectedCollecting;
         this.expectedSideProofsCount = expectedSideProofsCount;
         this.openProofAtIndex = openProofAtIndex;
         this.indicesToDelete = indicesToDelete;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void configureDebugPerspective(SWTWorkbenchBot bot, IPerspectiveDescriptor debugPerspective) throws Exception {
         TestUtilsUtil.openView(SideProofsView.VIEW_ID);
         if (switchCollecting) {
            SWTBotView view = bot.viewById(SideProofsView.VIEW_ID);
            SWTBotTable table = view.bot().table();
            table.contextMenu("Collect Side Proofs").click();
         }
         assertEquals(expectedCollecting, SideProofStore.DEFAULT_INSTANCE.isEnabled());
      }

      /**
       * {@inheritDoc}
       */      
      @Override
      public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
         // Make sure that no side proofs are available
         assertEquals(0, SideProofStore.DEFAULT_INSTANCE.countEntries());
         // Finish symbolic execution
         SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0); // Select thread
         resume(bot, item, target);
         TestSedCoreUtil.waitUntilDebugTargetCanResume(bot, target);
         // Expand debug tree to initiate side proofs
         TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0, 1, 0, 0, 2);
         TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0, 1, 0, 1, 2);
         TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0, 1, 1, 1);
         // Test collected side proofs
         SWTBotView view = bot.viewById(SideProofsView.VIEW_ID);
         view.setFocus();
         SWTBotTable table = view.bot().table();
         assertMinSideProofs(view, table, expectedSideProofsCount);
         // Open proof
         if (openProofAtIndex >= 0) {
            table.select(openProofAtIndex);
            table.contextMenu("Open").click();
            SWTBotEditor openedEditor = bot.activeEditor();
            assertEquals(KeYEditor.EDITOR_ID, openedEditor.getReference().getId());
            openedEditor.close();
         }
         // Delete proofs
         Entry[] originalEntries = SideProofStore.DEFAULT_INSTANCE.getEntries();
         int remaingRows = expectedSideProofsCount;
         for (int[] toDelete : indicesToDelete) {
            table.select(toDelete);
            table.contextMenu("Delete").click();
            remaingRows -= toDelete.length;
            assertMinSideProofs(view, table, remaingRows);
            testProofDisposed(originalEntries);
         }
         // Ensure that deleted proofs are disposed
         testProofDisposed(originalEntries);
         // Remove missing proofs
         SideProofStore.DEFAULT_INSTANCE.clearProofs();
         // Ensure that deleted proofs are disposed
         assertExactSideProofs(view, table, 0);
         testProofDisposed(originalEntries);
         // Make sure that no side proofs are available
         assertEquals(0, SideProofStore.DEFAULT_INSTANCE.countEntries());
      }
      
      /**
       * Makes sure that the {@link Entry}s of {@link SideProofStore#DEFAULT_INSTANCE} 
       * are shown in the given {@link SWTBotTable}.
       * @param view The {@link SWTBotView} showing the {@link SideProofsView}.
       * @param table The {@link SWTBotTable} which shows the {@link Entry}s.
       * @param expectedSideProofsCount The expected number of side proofs.
       */
      protected void assertExactSideProofs(SWTBotView view, SWTBotTable table, int expectedSideProofsCount) {
         view.bot().waitUntil(Conditions.tableHasRows(table, expectedSideProofsCount));
         Entry[] entries = SideProofStore.DEFAULT_INSTANCE.getEntries();
         assertEquals(expectedSideProofsCount, entries.length);
         for (int i = 0; i < entries.length; i++) {
            Object data = TestUtilsUtil.getTableItemData(table.getTableItem(i));
            assertTrue(data instanceof Entry);
            assertSame(entries[i], data);
         }
      }
      
      /**
       * Makes sure that the {@link Entry}s of {@link SideProofStore#DEFAULT_INSTANCE} 
       * are shown in the given {@link SWTBotTable}.
       * @param view The {@link SWTBotView} showing the {@link SideProofsView}.
       * @param table The {@link SWTBotTable} which shows the {@link Entry}s.
       * @param expectedSideProofsCount The expected number of side proofs.
       */
      protected void assertMinSideProofs(SWTBotView view, SWTBotTable table, int expectedSideProofsCount) {
         TestUtilsUtil.waitUntilTableHasAtLeastRows(view.bot(), table, expectedSideProofsCount);
         Entry[] entries = SideProofStore.DEFAULT_INSTANCE.getEntries();
         assertTrue(entries.length >= expectedSideProofsCount);
         for (int i = 0; i < entries.length; i++) {
            Object data = TestUtilsUtil.getTableItemData(table.getTableItem(i));
            assertTrue(data instanceof Entry);
            assertSame(entries[i], data);
         }
      }

      /**
       * Tests {@link Proof#isDisposed()}.
       * @param originalEntries The {@link Entry}s to test its {@link Proof}s.
       */
      protected void testProofDisposed(Entry[] originalEntries) {
         for (Entry entry : originalEntries) {
            assertEquals(!SideProofStore.DEFAULT_INSTANCE.containsEntry(entry), entry.getProof().isDisposed());
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void cleanupDebugPerspective(SWTWorkbenchBot bot, IPerspectiveDescriptor debugPerspective) throws Exception {
         TestUtilsUtil.closeView(SideProofsView.VIEW_ID);
      }
   }
}
