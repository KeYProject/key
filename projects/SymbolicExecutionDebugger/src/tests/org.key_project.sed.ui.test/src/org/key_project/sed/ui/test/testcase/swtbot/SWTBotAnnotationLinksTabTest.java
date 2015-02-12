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
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.annotation.ISEDAnnotationType;
import org.key_project.sed.core.annotation.impl.CommentAnnotation;
import org.key_project.sed.core.annotation.impl.CommentAnnotationLink;
import org.key_project.sed.core.annotation.impl.CommentAnnotationType;
import org.key_project.sed.core.annotation.impl.SearchAnnotation;
import org.key_project.sed.core.annotation.impl.SearchAnnotationType;
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
 * Tests the property page tab "Annotation Links" using search and comment links.
 * </p>
 * <p>
 * In particular the comment functionality using {@link CommentAnnotation}
 * and {@link CommentAnnotationLink} is tested which is available in this 
 * property page tab.
 * </p>
 * @author Martin Hentschel
 */
public class SWTBotAnnotationLinksTabTest extends AbstractSWTBotPropertyTabTest {
   /**
    * Tests the shown values and the existence of tab "Node".
    */
   @Test
   public void testValuesAndTabExistence() throws Exception {
      doFixedExampleTest(createFixedExampleSteps());
   }
   
   /**
    * Creates the test steps to execute.
    * @return The created test steps.
    */
   public static ITestSteps createFixedExampleSteps() {
      return new ITestSteps() {
         private ISEDDebugTarget target;
         
         private ISEDAnnotationType commentType;
         
         private ISEDAnnotation commentAnnotation;
         
         private CommentAnnotationLink commentThreadLink;
         
         private ISEDAnnotationType searchType;
         
         private SearchAnnotation searchAnnotation;
         
         private ISEDAnnotationLink searchThreadLink;
         
         @Override
         public void initializeLaunch(ILaunch launch) throws Exception {
            target = (ISEDDebugTarget)launch.getDebugTarget();
            ISEDThread thread = target.getSymbolicThreads()[0];
            // Add comment link to thread
            commentType = SEDAnnotationUtil.getAnnotationtype(CommentAnnotationType.TYPE_ID);
            commentAnnotation = commentType.createAnnotation();
            commentAnnotation.setCustomHighlightBackground(Boolean.FALSE);
            commentAnnotation.setCustomHighlightForeground(Boolean.FALSE);
            target.registerAnnotation(commentAnnotation);
            commentThreadLink = (CommentAnnotationLink)commentType.createLink(commentAnnotation, thread);
            commentThreadLink.setComment("CommentAnnotationLink on Thread");
            thread.addAnnotationLink(commentThreadLink);
            // Add search link to thread
            searchType = SEDAnnotationUtil.getAnnotationtype(SearchAnnotationType.TYPE_ID);
            searchAnnotation = (SearchAnnotation)searchType.createAnnotation();
            searchAnnotation.setSearch(thread.getName());
            searchAnnotation.setCustomHighlightBackground(Boolean.FALSE);
            searchAnnotation.setCustomHighlightForeground(Boolean.FALSE);
            target.registerAnnotation(searchAnnotation);
            searchThreadLink = searchType.createLink(searchAnnotation, thread);
            thread.addAnnotationLink(searchThreadLink);
         }
         
         @Override
         public void assertThread(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEDThread thread) throws Exception {
            assertTrue(tabs.selectTabItem("Annotation Links"));
            SWTBotTable table = propertiesView.bot().table();
            assertEquals(2, propertiesView.bot().table().rowCount());
            assertSame(commentThreadLink, TestUtilsUtil.getTableItemData(table.getTableItem(0)));
            assertSame(searchThreadLink, TestUtilsUtil.getTableItemData(table.getTableItem(1)));
            // Delete comment link
            table.select(0);
            table.contextMenu("Delete").click();
            assertEquals(1, propertiesView.bot().table().rowCount());
            assertSame(searchThreadLink, TestUtilsUtil.getTableItemData(table.getTableItem(0)));
            assertFalse(target.isRegistered(commentAnnotation));
            assertTrue(target.isRegistered(searchAnnotation));
            assertFalse(thread.containsAnnotationLink(commentThreadLink));
            assertTrue(thread.containsAnnotationLink(searchThreadLink));
            // Try to delete search link
            assertFalse(table.contextMenu("Delete").isEnabled());
            assertTrue(target.isRegistered(searchAnnotation));
            assertFalse(thread.containsAnnotationLink(commentThreadLink));
            assertTrue(thread.containsAnnotationLink(searchThreadLink));
         }
         
         @Override
         public void assertStatement(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEDStatement statement) throws Exception {
            // Test initially empty links
            assertTrue(tabs.selectTabItem("Annotation Links"));
            SWTBotTable table = propertiesView.bot().table();
            assertEquals(0, table.rowCount());
            // Create first comment of type "Type1"
            propertiesView.bot().button("New Comment").click();
            createComent(propertiesView, "Type1", "Type1Comment");
            ISEDAnnotation[] annotations = target.getRegisteredAnnotations();
            assertEquals(2, annotations.length);
            assertSame(searchAnnotation, annotations[0]);
            CommentAnnotation type1Annotation = (CommentAnnotation)annotations[1];
            assertEquals("Type1", type1Annotation.getCommentType());
            ISEDAnnotationLink[] links = statement.getAnnotationLinks();
            assertEquals(1, links.length);
            CommentAnnotationLink firstLink = (CommentAnnotationLink)links[0];
            assertEquals("Type1Comment", firstLink.getComment());
            ISEDAnnotationLink[] annotationLinks = type1Annotation.getLinks();
            assertEquals(1, annotationLinks.length);
            assertSame(firstLink, annotationLinks[0]);
            assertEquals(1, table.rowCount());
            assertSame(firstLink, TestUtilsUtil.getTableItemData(table.getTableItem(0)));
            // Create first comment of type "Type2"
            propertiesView.bot().button("New Comment").click();
            createComent(propertiesView, "Type2", "Type2Comment");
            annotations = target.getRegisteredAnnotations();
            assertEquals(3, annotations.length);
            assertSame(searchAnnotation, annotations[0]);
            assertSame(type1Annotation, annotations[1]);
            CommentAnnotation type2Annotation = (CommentAnnotation)annotations[2];
            assertEquals("Type2", type2Annotation.getCommentType());
            links = statement.getAnnotationLinks();
            assertEquals(2, links.length);
            assertSame(firstLink, links[0]);
            CommentAnnotationLink secondLink = (CommentAnnotationLink)links[1];
            assertEquals("Type2Comment", secondLink.getComment());
            annotationLinks = type2Annotation.getLinks();
            assertEquals(1, annotationLinks.length);
            assertSame(secondLink, annotationLinks[0]);
            assertEquals(2, table.rowCount());
            assertSame(firstLink, TestUtilsUtil.getTableItemData(table.getTableItem(0)));
            assertSame(secondLink, TestUtilsUtil.getTableItemData(table.getTableItem(1)));
            // Edit first comment of type "Type1"
            table.select(0);
            table.contextMenu("Edit").click();
            SWTBotShell shell = propertiesView.bot().shell("Edit Comment");
            shell.bot().text().setText("Type1Comment-1");
            TestUtilsUtil.clickDirectly(shell.bot(), "Finish");
            shell.bot().waitUntil(Conditions.shellCloses(shell));
            assertEquals("Type1Comment-1", firstLink.getComment());
            assertEquals(2, table.rowCount());
            assertSame(firstLink, TestUtilsUtil.getTableItemData(table.getTableItem(0)));
            assertSame(secondLink, TestUtilsUtil.getTableItemData(table.getTableItem(1)));
            // Create second comment of type "Type1"
            propertiesView.bot().button("New Comment").click();
            createComent(propertiesView, "Type1", "Type1Comment-2");
            annotations = target.getRegisteredAnnotations();
            assertEquals(3, annotations.length);
            assertSame(searchAnnotation, annotations[0]);
            assertSame(type1Annotation, annotations[1]);
            assertSame(type2Annotation, annotations[2]);
            assertEquals("Type1", type1Annotation.getCommentType());
            links = statement.getAnnotationLinks();
            assertEquals(3, links.length);
            assertSame(firstLink, links[0]);
            assertSame(secondLink, links[1]);
            CommentAnnotationLink thirdLink = (CommentAnnotationLink)links[2];
            assertEquals("Type1Comment-2", thirdLink.getComment());
            annotationLinks = type1Annotation.getLinks();
            assertEquals(2, annotationLinks.length);
            assertSame(firstLink, annotationLinks[0]);
            assertSame(thirdLink, annotationLinks[1]);
            assertEquals(3, table.rowCount());
            assertSame(firstLink, TestUtilsUtil.getTableItemData(table.getTableItem(0)));
            assertSame(secondLink, TestUtilsUtil.getTableItemData(table.getTableItem(1)));
            assertSame(thirdLink, TestUtilsUtil.getTableItemData(table.getTableItem(2)));
         }
         
         protected void createComent(SWTBotView propertiesView, String type, String comment) {
            SWTBotShell shell = propertiesView.bot().shell("New Comment");
            shell.bot().comboBox().setText(type);
            shell.bot().text().setText(comment);
            TestUtilsUtil.clickDirectly(shell.bot(), "Finish");
            shell.bot().waitUntil(Conditions.shellCloses(shell));
         }
         
         @Override
         public void assertDebugTarget(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEDDebugTarget target) throws Exception {
            assertFalse(tabs.hasTabItem("Annotation Links"));
         }

         @Override
         public void assertMethodReturn(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEDMethodReturn methodReturn) throws Exception {
            assertTrue(tabs.selectTabItem("Annotation Links"));
            assertEquals(0, propertiesView.bot().table().rowCount());
         }

         @Override
         public void assertMethodCall(SWTBotTree debugTree, SWTBotView propertiesView, SWTBotTabbedPropertyList tabs, ISEDMethodCall methodCall) throws Exception {
            assertTrue(tabs.selectTabItem("Annotation Links"));
            assertEquals(0, propertiesView.bot().table().rowCount());
         }
      };
   }
}