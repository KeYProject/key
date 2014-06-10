/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.keyide.ui.test.testcase.swtbot;

import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotList;
import org.eclipse.ui.IPageLayout;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.util.java.StringUtil;
import org.key_project.util.test.util.SWTBotTabbedPropertyList;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;

/**
 * Provides the basic functionality to test a properties tab of the {@link KeYEditor}.
 * @author Martin Hentschel
 */
public abstract class AbstractSWTBotKeYEditorPropertiesTest extends AbstractSWTBotKeYEditorTest {
   /**
    * Tests a properties tab of the {@link KeYEditor}.
    * @param projectName The project name to use.
    * @param pathToSourceFilesInBundle The path to the plug-in to the source files to extract into the created project.
    * @param contractName The name of the contract to prove.
    * @param inOutlineView {@code true} set focus to properties view, {@code false} set focus to editor.
    * @param pSteps The {@link IPropertiesTestSteps} to execute.
    * @throws Exception Occurred Exception
    */
   protected void doPropertiesTest(String projectName,
                                   String pathToSourceFilesInBundle,
                                   String contractName,
                                   final boolean inOutlineView,
                                   final IPropertiesTestSteps pSteps) throws Exception {
      IKeYEditorTestSteps steps = new IKeYEditorTestSteps() {
         @Override
         public void test(IJavaProject project,
                          KeYEnvironment<CustomUserInterface> environment, 
                          Proof proof, 
                          SWTWorkbenchBot bot, 
                          SWTBotEditor editor,
                          KeYEditor keyEditor) throws Exception {
            TestUtilsUtil.openView(IPageLayout.ID_PROP_SHEET);
            SWTBotView propertiesView = TestUtilsUtil.getPropertiesView(bot);
            if (inOutlineView) {
               SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
               outlineView.setFocus();
            }
            else {
               editor.setFocus();
            }
            // Test root
            KeYMediator mediator = environment.getMediator();
            pSteps.assertNodeTab(editor, keyEditor, propertiesView, mediator, mediator.getSelectedNode());
            // Apply rule interactively
            applyTaclet(mediator, mediator.getSelectedNode().sequent(), false, 0, PosInTerm.getTopLevel(), "impRight");
            pSteps.assertNodeTab(editor, keyEditor, propertiesView, mediator, mediator.getSelectedNode());
            // Select root
            mediator.getSelectionModel().setSelectedNode(proof.root());
            pSteps.assertNodeTab(editor, keyEditor, propertiesView, mediator, mediator.getSelectedNode());
            // Finish proof
            environment.getUi().waitWhileAutoMode();
            pSteps.assertNodeTab(editor, keyEditor, propertiesView, mediator, mediator.getSelectedNode());
         }
      };
      doEditorTest(projectName, pathToSourceFilesInBundle, contractName, false, steps);
   }
   
   /**
    * Executes the test steps of {@link IPropertiesTestSteps#assertNodeTab(SWTBotEditor, KeYEditor, SWTBotView, KeYMediator, Node)}.
    * @author Martin Hentschel
    */
   protected static interface IPropertiesTestSteps {
      /**
       * Executes the test steps.
       * @param editor The used {@link SWTBotEditor} of the {@link KeYEditor}.
       * @param keyEditor The opened {@link KeYEditor}.
       * @param propertiesView The properties view.
       * @param mediator The {@link KeYMediator} to use.
       * @param node The expected {@link Node}.
       * @throws Exception Occurred Exception
       */
      public void assertNodeTab(SWTBotEditor editor,
                                KeYEditor keyEditor,
                                SWTBotView propertiesView,
                                KeYMediator mediator,
                                Node node) throws Exception;
   }
   
   /**
    * Ensures that the given {@link SWTBotList} contains the expected items.
    * @param expectedItems The expected items.
    * @param list The {@link SWTBotList} to test.
    */
   protected void assertList(Iterable<?> expectedItems, SWTBotList list) {
      int i = 0;
      String[] currentItems = list.getItems();
      if (expectedItems != null) {
         for (Object expectedItem : expectedItems) {
            if (expectedItem != null) {
               assertEquals(expectedItem.toString(), currentItems[i]);
               i++;
            }
         }
      }
      assertEquals(currentItems.length, i);
   }

   /**
    * Validates the given value.
    * @param value The value to validate.
    * @return The validated value.
    */
   protected String validate(String value) {
      return value != null ? value : StringUtil.EMPTY_STRING;
   }

   /**
    * Returns the shown {@link SWTBotTabbedPropertyList}.
    * @param propertiesView The {@link SWTBotView} to search in.
    * @return The shown {@link SWTBotTabbedPropertyList}.
    */
   protected SWTBotTabbedPropertyList getPropertiesTabs(SWTBotView propertiesView) {
      SWTBotTabbedPropertyList tabs = SWTBotTabbedPropertyList.tabbedPropertyList(propertiesView.bot());
      assertNotNull(tabs);
      return tabs;
   }
}