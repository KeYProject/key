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

package org.key_project.sed.ui.test.testcase.swtbot;

import org.eclipse.debug.core.ILaunch;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.junit.Test;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationType;
import org.key_project.sed.core.annotation.impl.CommentAnnotation;
import org.key_project.sed.core.annotation.impl.CommentAnnotationLink;
import org.key_project.sed.core.annotation.impl.CommentAnnotationType;
import org.key_project.sed.core.annotation.impl.SearchAnnotation;
import org.key_project.sed.core.annotation.impl.SearchAnnotationLink;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.util.SEDAnnotationUtil;
import org.key_project.util.test.util.SWTBotTabbedPropertyList;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * <p>
 * Tests the property page tab "Annotations" using search and comment links.
 * </p>
 * <p>
 * In particular the comment functionality using {@link SearchAnnotation}
 * and {@link SearchAnnotationLink} is tested which is available in this 
 * property page tab.
 * </p>
 * @author Martin Hentschel
 */
public class SWTBotAnnotationsTabTest extends AbstractSWTBotPropertyTabTest {
   /**
    * Tests the shown values and the existence of tab "Node".
    */
   @Test
   public void testValuesAndTabExistence() throws Exception {
      doFixedExampleTest(createFixedExampleSteps(false));
   }
   
   /**
    * Creates the test steps to execute.
    * @return The created test steps.
    */
   public static ITestSteps createFixedExampleSteps(final boolean diagramProperties) {
      return new ITestSteps() {
         private ISEDDebugTarget target;
         
         private ISEDThread thread;
         
         private ISEDAnnotationType commentType;
         
         private CommentAnnotation commentAnnotation;
         
         private CommentAnnotationLink commentThreadLink;
         
         private boolean first = true;
         
         @Override
         public void initializeLaunch(ILaunch launch) throws Exception {
            target = (ISEDDebugTarget)launch.getDebugTarget();
            thread = target.getSymbolicThreads()[0];
            // Add comment link to thread
            commentType = SEDAnnotationUtil.getAnnotationtype(CommentAnnotationType.TYPE_ID);
            commentAnnotation = (CommentAnnotation)commentType.createAnnotation();
            commentAnnotation.setCommentType("MyCommentType");
            commentAnnotation.setCustomHighlightBackground(Boolean.FALSE);
            commentAnnotation.setCustomHighlightForeground(Boolean.FALSE);
            target.registerAnnotation(commentAnnotation);
            commentThreadLink = (CommentAnnotationLink)commentType.createLink(commentAnnotation, thread);
            commentThreadLink.setComment("CommentAnnotationLink on Thread");
            thread.addAnnotationLink(commentThreadLink);
         }
         
         @Override
         public void assertThread(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEDThread thread) throws Exception {
            assertFalse(tabs.hasTabItem("Annotations"));
         }
         
         @Override
         public void assertStatement(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEDStatement statement) throws Exception {
            assertFalse(tabs.hasTabItem("Annotations"));
         }
         
         @Override
         public void assertDebugTarget(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEDDebugTarget target) throws Exception {
            if (!diagramProperties) {
               assertTrue(tabs.selectTabItem("Annotations"));
               SWTBotTable table = propertiesView.bot().table();
               if (first) {
                  first = false;
                  assertEquals(1, table.rowCount());
                  assertSame(commentAnnotation, TestUtilsUtil.getTableItemData(table.getTableItem(0)));
                  // Edit comment
                  table.select(0);
                  table.contextMenu("Edit").click();
                  SWTBotShell editShell = propertiesView.bot().shell("Edit Annotation");
                  editShell.bot().text().setText("MyNewCommentType");
                  TestUtilsUtil.clickDirectly(editShell.bot(), "Finish");
                  editShell.bot().waitUntil(Conditions.shellCloses(editShell));
                  assertEquals("MyNewCommentType", commentAnnotation.getCommentType());
                  // Try to edit comment type
                  table.select(0);
                  assertFalse(table.contextMenu("Delete").isEnabled());
                  // Show comment links
                  table.contextMenu("Show annotation links").click();
                  SWTBotShell linksShell = propertiesView.bot().shell("Annotation links");
                  assertEquals(1, linksShell.bot().table().rowCount());
                  assertSame(commentThreadLink, TestUtilsUtil.getTableItemData(linksShell.bot().table().getTableItem(0)));
                  TestUtilsUtil.clickDirectly(linksShell.bot(), "Close");
                  linksShell.bot().waitUntil(Conditions.shellCloses(linksShell));
                  // Show comment links again and follow/delete link
                  table.contextMenu("Show annotation links").click();
                  linksShell = propertiesView.bot().shell("Annotation links");
                  SWTBotTable linksTable = linksShell.bot().table();
                  assertEquals(1, linksShell.bot().table().rowCount());
                  assertSame(commentThreadLink, TestUtilsUtil.getTableItemData(linksShell.bot().table().getTableItem(0)));
                  linksTable.select(0);
                  linksTable.contextMenu("Follow").click();
                  Thread.sleep(200); // Wait until selection has changed
                  Object[] selected = TestUtilsUtil.getSelectedObjects(debugTree);
                  assertEquals(1, selected.length);
                  assertSame(thread, selected[0]);
                  linksShell.setFocus();
                  linksTable.select(0);
                  linksTable.contextMenu("Delete").click();
                  assertFalse(linksShell.isOpen());
                  assertFalse(thread.containsAnnotationLink(commentThreadLink));
                  assertFalse(target.isRegistered(commentAnnotation));
                  assertEquals(0, table.rowCount());
                  // Perform search
                  propertiesView.bot().button("Search").click();
                  search(propertiesView, "x++");
                  ISEDAnnotation[] annotations = target.getRegisteredAnnotations();
                  assertEquals(1, annotations.length);
                  SearchAnnotation firstSearch = (SearchAnnotation)annotations[0];
                  assertEquals("x++", firstSearch.getSearch());
                  assertEquals(1, table.rowCount());
                  assertSame(firstSearch, TestUtilsUtil.getTableItemData(table.getTableItem(0)));
                  assertEquals(1, firstSearch.getLinks().length);
                  assertEquals("x++;", firstSearch.getLinks()[0].getTarget().getName());
                  // Perform second search
                  propertiesView.bot().button("Search").click();
                  search(propertiesView, "foo");
                  annotations = target.getRegisteredAnnotations();
                  assertEquals(2, annotations.length);
                  assertSame(firstSearch, annotations[0]);
                  SearchAnnotation secondSearch = (SearchAnnotation)annotations[1];
                  assertEquals("foo", secondSearch.getSearch());
                  assertEquals(2, table.rowCount());
                  assertSame(firstSearch, TestUtilsUtil.getTableItemData(table.getTableItem(0)));
                  assertSame(secondSearch, TestUtilsUtil.getTableItemData(table.getTableItem(1)));
                  assertEquals(1, secondSearch.getLinks().length);
                  assertEquals("foo(result)", secondSearch.getLinks()[0].getTarget().getName());
                  // Move up
                  table.select(1);
                  table.contextMenu("Move up").click();
                  annotations = target.getRegisteredAnnotations();
                  assertEquals(2, annotations.length);
                  assertSame(secondSearch, annotations[0]);
                  assertSame(firstSearch, annotations[1]);
                  assertEquals(2, table.rowCount());
                  assertSame(secondSearch, TestUtilsUtil.getTableItemData(table.getTableItem(0)));
                  assertSame(firstSearch, TestUtilsUtil.getTableItemData(table.getTableItem(1)));
                  // Move down
                  table.select(0);
                  table.contextMenu("Move down").click();
                  annotations = target.getRegisteredAnnotations();
                  assertEquals(2, annotations.length);
                  assertSame(firstSearch, annotations[0]);
                  assertSame(secondSearch, annotations[1]);
                  assertEquals(2, table.rowCount());
                  assertSame(firstSearch, TestUtilsUtil.getTableItemData(table.getTableItem(0)));
                  assertSame(secondSearch, TestUtilsUtil.getTableItemData(table.getTableItem(1)));
                  // Change checked states
                  assertTrue(firstSearch.isEnabled());
                  assertTrue(secondSearch.isEnabled());
                  assertTrue(table.getTableItem(0).isChecked());
                  assertTrue(table.getTableItem(1).isChecked());
                  table.getTableItem(0).uncheck();
                  assertFalse(firstSearch.isEnabled());
                  assertTrue(secondSearch.isEnabled());
                  assertFalse(table.getTableItem(0).isChecked());
                  assertTrue(table.getTableItem(1).isChecked());
                  table.getTableItem(0).check();
                  assertTrue(firstSearch.isEnabled());
                  assertTrue(secondSearch.isEnabled());
                  assertTrue(table.getTableItem(0).isChecked());
                  assertTrue(table.getTableItem(1).isChecked());
                  // Delete first search
                  table.select(0);
                  table.contextMenu("Delete").click();
                  annotations = target.getRegisteredAnnotations();
                  assertEquals(1, annotations.length);
                  assertSame(secondSearch, annotations[0]);
                  assertEquals(1, table.rowCount());
                  assertSame(secondSearch, TestUtilsUtil.getTableItemData(table.getTableItem(0)));
                  // Edit first search
                  table.select(0);
                  table.contextMenu("Edit").click();
                  editShell = propertiesView.bot().shell("Edit Annotation");
                  editShell.bot().text().setText("x++");
                  TestUtilsUtil.clickDirectly(editShell.bot(), "Finish");
                  editShell.bot().waitUntil(Conditions.shellCloses(editShell));
                  assertEquals("MyNewCommentType", commentAnnotation.getCommentType());
                  annotations = target.getRegisteredAnnotations();
                  assertEquals(1, annotations.length);
                  assertSame(secondSearch, annotations[0]);
                  assertEquals("x++", secondSearch.getSearch());
                  assertEquals(1, table.rowCount());
                  assertSame(secondSearch, TestUtilsUtil.getTableItemData(table.getTableItem(0)));
                  assertEquals(1, secondSearch.getLinks().length);
                  assertEquals("x++;", secondSearch.getLinks()[0].getTarget().getName());
                  // Delete second search
                  table.select(0);
                  table.contextMenu("Delete").click();
                  annotations = target.getRegisteredAnnotations();
                  assertEquals(0, annotations.length);
                  assertEquals(0, table.rowCount());
               }
               else {
                  assertEquals(0, table.rowCount());
               }
            }
            else {
               assertFalse(tabs.hasTabItem("Annotations"));
            }
         }
         
         protected void search(SWTBotView propertiesView, String search) {
            SWTBotShell shell = propertiesView.bot().shell("Search");
            shell.bot().text().setText(search);
            TestUtilsUtil.clickDirectly(shell.bot(), "Finish");
            shell.bot().waitUntil(Conditions.shellCloses(shell));
         }

         @Override
         public void assertMethodReturn(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEDMethodReturn methodReturn) throws Exception {
            assertFalse(tabs.hasTabItem("Annotations"));
         }

         @Override
         public void assertMethodCall(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEDMethodCall methodCall) throws Exception {
            assertFalse(tabs.hasTabItem("Annotations"));
         }
      };
   }
}