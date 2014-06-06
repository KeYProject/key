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

package org.key_project.util.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.gef.editparts.ZoomManager;
import org.eclipse.gef.ui.actions.GEFActionConstants;
import org.eclipse.graphiti.ui.editor.DiagramEditor;
import org.eclipse.jface.action.IContributionItem;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotLabel;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotText;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.navigator.resources.ProjectExplorer;
import org.junit.Test;
import org.key_project.util.eclipse.view.editorInView.AbstractEditorInViewView;
import org.key_project.util.eclipse.view.editorInView.EditorInViewEditorSite;
import org.key_project.util.eclipse.view.editorInView.EditorInViewWorkbenchPage;
import org.key_project.util.eclipse.view.editorInView.IGlobalEnablement;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;
import org.key_project.util.test.util.PropertyChangeListenerLogger;
import org.key_project.util.test.util.TestUtilsUtil;
import org.key_project.util.test.view.GraphitiEditorInViewView;
import org.key_project.util.test.view.TextControlEditorInViewView;

/**
 * Tests {@link AbstractEditorInViewView}, {@link EditorInViewEditorSite} and
 * {@link EditorInViewWorkbenchPage}.
 * @author Martin Hentschel
 */
public class SWTBotAbstractEditorInViewViewTest extends TestCase {
   /**
    * <p>
    * Tests {@link AbstractEditorInViewView#isEditorEnabled()} and
    * {@link AbstractEditorInViewView#setEditorEnabled(boolean)}.
    * </p>
    * <p>
    * The test makes also sure that the global enabled state of editor
    * and action bar contribution is only {@code true} if no message
    * is shown in view and the editor is enabled.
    * </p>
    */
   @Test
   public void testEditorEnabled() throws Exception {
      SWTBotView view = null;
      try {
         // Close welcome view
         SWTWorkbenchBot bot = new SWTWorkbenchBot();
         TestUtilsUtil.closeWelcomeView(bot);
         // Open view
         IViewPart part = TestUtilsUtil.openView(TextControlEditorInViewView.VIEW_ID);
         assertTrue(part instanceof TextControlEditorInViewView);
         TextControlEditorInViewView textView = (TextControlEditorInViewView)part;
         assertNotNull(textView.getEditorPart());
         assertNotNull(textView.getEditorActionBarContributor());
         view = bot.viewById(TextControlEditorInViewView.VIEW_ID);
         assertTrue(view.isActive());
         // Make sure that no editor is opened
         assertTrue(textView.isMessageShown());
         assertTrue(textView.isEditorEnabled());
         assertTrue(textView.isEditorCompositeEnabled());
         assertFalse(textView.getEditorPart().isGlobalEnabled());
         assertFalse(textView.getEditorActionBarContributor().isGlobalEnabled());
         // Disable editor
         textView.setEditorEnabled(false);
         assertFalse(textView.isEditorEnabled());
         assertFalse(textView.isEditorCompositeEnabled());
         assertFalse(textView.getEditorPart().isGlobalEnabled());
         assertFalse(textView.getEditorActionBarContributor().isGlobalEnabled());
         // Enable editor
         textView.setEditorEnabled(true);
         assertTrue(textView.isEditorEnabled());
         assertTrue(textView.isEditorCompositeEnabled());
         assertFalse(textView.getEditorPart().isGlobalEnabled());
         assertFalse(textView.getEditorActionBarContributor().isGlobalEnabled());
         // Hide message
         textView.setMessage(null);
         assertFalse(textView.isMessageShown());
         assertTrue(textView.isEditorEnabled());
         assertTrue(textView.isEditorCompositeEnabled());
         assertTrue(textView.getEditorPart().isGlobalEnabled());
         assertTrue(textView.getEditorActionBarContributor().isGlobalEnabled());
         // Disable editor
         textView.setEditorEnabled(false);
         assertFalse(textView.isEditorEnabled());
         assertFalse(textView.isEditorCompositeEnabled());
         assertFalse(textView.getEditorPart().isGlobalEnabled());
         assertFalse(textView.getEditorActionBarContributor().isGlobalEnabled());
         // Enable editor
         textView.setEditorEnabled(true);
         assertTrue(textView.isEditorEnabled());
         assertTrue(textView.isEditorCompositeEnabled());
         assertTrue(textView.getEditorPart().isGlobalEnabled());
         assertTrue(textView.getEditorActionBarContributor().isGlobalEnabled());
      }
      finally {
         if (view != null) {
            view.close();
         }
      }
   }
   
   /**
    * Tests {@link AbstractEditorInViewView#doSave(org.eclipse.core.runtime.IProgressMonitor)} and
    * {@link AbstractEditorInViewView#doSaveAs()}.
    */
   @Test
   public void testSaveAndSaveAs() throws Exception {
      SWTBotView view = null;
      try {
         // Close welcome view
         SWTWorkbenchBot bot = new SWTWorkbenchBot();
         TestUtilsUtil.closeWelcomeView(bot);
         // Open view
         IViewPart part = TestUtilsUtil.openView(TextControlEditorInViewView.VIEW_ID);
         assertTrue(part instanceof TextControlEditorInViewView);
         TextControlEditorInViewView textView = (TextControlEditorInViewView)part;
         assertNotNull(textView.getEditorPart());
         assertNotNull(textView.getEditorActionBarContributor());
         view = bot.viewById(TextControlEditorInViewView.VIEW_ID);
         assertTrue(view.isActive());
         // Make sure that no real editor is opened
         assertEquals(0, bot.editors().size());
         // Make sure that message is shown
         assertEquals(0, textView.getEditorPart().getSaveCount());
         assertEquals(0, textView.getEditorPart().getSaveAsCount());
         // Call save
         textView.doSave(new NullProgressMonitor());
         assertEquals(1, textView.getEditorPart().getSaveCount());
         assertEquals(0, textView.getEditorPart().getSaveAsCount());
         // Call save as
         textView.doSaveAs();
         assertEquals(1, textView.getEditorPart().getSaveCount());
         assertEquals(1, textView.getEditorPart().getSaveAsCount());
      }
      finally {
         if (view != null) {
            view.close();
         }
      }
   }
   
   /**
    * Tests {@link AbstractEditorInViewView#getMessage()},
    * {@link AbstractEditorInViewView#setMessage(String)},
    * {@link AbstractEditorInViewView#isEditorShown()},
    * {@link AbstractEditorInViewView#isMessageShown()},
    * the events observed via {@link AbstractEditorInViewView#addPropertyChangeListener(String, java.beans.PropertyChangeListener)},
    * that the {@link IGlobalEnablement} of contained editor/contributor is correctly updated and
    * {@link AbstractEditorInViewView#isDirty()},
    * {@link AbstractEditorInViewView#isSaveAsAllowed()} and
    * {@link AbstractEditorInViewView#isSaveOnCloseNeeded()}.
    */
   @Test
   public void testMessage() throws Exception {
      SWTBotView view = null;
      TextControlEditorInViewView textView = null;
      try {
         // Close welcome view
         SWTWorkbenchBot bot = new SWTWorkbenchBot();
         TestUtilsUtil.closeWelcomeView(bot);
         // Open view
         IViewPart part = TestUtilsUtil.openView(TextControlEditorInViewView.VIEW_ID);
         assertTrue(part instanceof TextControlEditorInViewView);
         textView = (TextControlEditorInViewView)part;
         assertNotNull(textView.getEditorPart());
         assertNotNull(textView.getEditorActionBarContributor());
         view = bot.viewById(TextControlEditorInViewView.VIEW_ID);
         assertTrue(view.isActive());
         PropertyChangeListenerLogger editorListener = new PropertyChangeListenerLogger();
         textView.addPropertyChangeListener(AbstractEditorInViewView.PROP_EDITOR_SHOWN, editorListener);
         PropertyChangeListenerLogger messageListener = new PropertyChangeListenerLogger();
         textView.addPropertyChangeListener(AbstractEditorInViewView.PROP_MESSAGE_SHOWN, messageListener);
         // Make sure that no real editor is opened
         assertEquals(0, bot.editors().size());
         // Make sure that message is shown
         SWTBotLabel label = view.bot().label();
         assertEquals("Initial message from TextControlEditorInViewView.", label.getText());
         assertTrue(label.isVisible());
         assertFalse(textView.isEditorShown());
         assertTrue(textView.isMessageShown());
         PropertyChangeListenerLogger.assertNoLoggerEvent(editorListener, messageListener);
         assertFalse(textView.getEditorPart().isGlobalEnabled());
         assertFalse(textView.getEditorActionBarContributor().isGlobalEnabled());
         assertFalse(textView.isDirty());
         assertFalse(textView.isSaveAsAllowed());
         assertFalse(textView.isSaveOnCloseNeeded());
         // Show new text
         textView.setMessage("Hello World!");
         assertEquals("Hello World!", label.getText());
         assertTrue(label.isVisible());
         assertFalse(textView.isEditorShown());
         assertTrue(textView.isMessageShown());
         PropertyChangeListenerLogger.assertNoLoggerEvent(editorListener, messageListener);
         assertFalse(textView.getEditorPart().isGlobalEnabled());
         assertFalse(textView.getEditorActionBarContributor().isGlobalEnabled());
         assertFalse(textView.isDirty());
         assertFalse(textView.isSaveAsAllowed());
         assertFalse(textView.isSaveOnCloseNeeded());
         // Show editor
         textView.setMessage(null);
         assertFalse(label.isVisible());
         SWTBotText text = view.bot().text();
         assertEquals("This is an Editor.", text.getText());
         assertTrue(text.isVisible());
         assertTrue(textView.isEditorShown());
         assertFalse(textView.isMessageShown());
         assertEquals(1, editorListener.countLog());
         assertEquals(1, messageListener.countLog());
         PropertyChangeListenerLogger.assertLoggerEvent(part, AbstractEditorInViewView.PROP_MESSAGE_SHOWN, true, false, messageListener);
         PropertyChangeListenerLogger.assertLoggerEvent(part, AbstractEditorInViewView.PROP_EDITOR_SHOWN, false, true, editorListener);
         assertTrue(textView.getEditorPart().isGlobalEnabled());
         assertTrue(textView.getEditorActionBarContributor().isGlobalEnabled());
         assertFalse(textView.isDirty());
         assertTrue(textView.isSaveAsAllowed());
         assertFalse(textView.isSaveOnCloseNeeded());
         // Make editor dirty
         textView.getEditorPart().setDirty(true);
         assertTrue(textView.isDirty());
         assertTrue(textView.isSaveAsAllowed());
         assertTrue(textView.isSaveOnCloseNeeded());
         // Show editor again
         textView.setMessage(null);
         assertFalse(label.isVisible());
         assertEquals("This is an Editor.", text.getText());
         assertTrue(text.isVisible());
         assertTrue(textView.isEditorShown());
         assertFalse(textView.isMessageShown());
         PropertyChangeListenerLogger.assertNoLoggerEvent(editorListener, messageListener);
         assertTrue(textView.getEditorPart().isGlobalEnabled());
         assertTrue(textView.getEditorActionBarContributor().isGlobalEnabled());
         assertTrue(textView.isDirty());
         assertTrue(textView.isSaveAsAllowed());
         assertTrue(textView.isSaveOnCloseNeeded());
         // Make editor not dirty
         textView.getEditorPart().setDirty(false);
         assertFalse(textView.isDirty());
         assertTrue(textView.isSaveAsAllowed());
         assertFalse(textView.isSaveOnCloseNeeded());
         // Show new text
         textView.setMessage("Hello World Again!");
         assertEquals("Hello World Again!", label.getText());
         assertTrue(label.isVisible());
         assertFalse(text.isVisible());
         assertFalse(textView.isEditorShown());
         assertTrue(textView.isMessageShown());
         PropertyChangeListenerLogger.assertLoggerEvent(part, AbstractEditorInViewView.PROP_MESSAGE_SHOWN, false, true, messageListener);
         PropertyChangeListenerLogger.assertLoggerEvent(part, AbstractEditorInViewView.PROP_EDITOR_SHOWN, true, false, editorListener);
         assertFalse(textView.getEditorPart().isGlobalEnabled());
         assertFalse(textView.getEditorActionBarContributor().isGlobalEnabled());
         assertFalse(textView.isDirty());
         assertFalse(textView.isSaveAsAllowed());
         assertFalse(textView.isSaveOnCloseNeeded());
         // Show editor again
         textView.setMessage(null);
         assertFalse(label.isVisible());
         assertEquals("This is an Editor.", text.getText());
         assertTrue(text.isVisible());
         assertTrue(textView.isEditorShown());
         assertFalse(textView.isMessageShown());
         PropertyChangeListenerLogger.assertLoggerEvent(part, AbstractEditorInViewView.PROP_MESSAGE_SHOWN, true, false, messageListener);
         PropertyChangeListenerLogger.assertLoggerEvent(part, AbstractEditorInViewView.PROP_EDITOR_SHOWN, false, true, editorListener);
         assertTrue(textView.getEditorPart().isGlobalEnabled());
         assertTrue(textView.getEditorActionBarContributor().isGlobalEnabled());
         assertFalse(textView.isDirty());
         assertTrue(textView.isSaveAsAllowed());
         assertFalse(textView.isSaveOnCloseNeeded());
      }
      finally {
         if (textView != null) {
            textView.getEditorPart().setDirty(false);
         }
         if (view != null) {
            view.close();
         }
      }
   }
   
   /**
    * Makes sure that the Graphiti editor {@link DiagramEditor} is correctly
    * shown in an {@link IViewPart} via {@link AbstractEditorInViewView}
    * implementation {@link GraphitiEditorInViewView}. 
    */
   @Test
   public void testGraphitiEditorInView() throws Exception {
      SWTBotView view = null;
      try {
         // Close welcome view
         SWTWorkbenchBot bot = new SWTWorkbenchBot();
         TestUtilsUtil.closeWelcomeView(bot);
         // Open view
         final IViewPart part = TestUtilsUtil.openView(GraphitiEditorInViewView.VIEW_ID);
         view = bot.viewById(GraphitiEditorInViewView.VIEW_ID);
         assertTrue(view.isActive());
         // Make sure that no editor is opened
         assertEquals(0, bot.editors().size());
         // Make sure that Graphiti editor is shown
         ZoomManager manager = (ZoomManager)part.getAdapter(ZoomManager.class);
         assertNotNull(manager);
         // Get zoom in menu item
         IRunnableWithResult<IContributionItem> runMenu = new AbstractRunnableWithResult<IContributionItem>() {
            @Override
            public void run() {
               try {
                  IToolBarManager manager = part.getViewSite().getActionBars().getToolBarManager();
                  assertNotNull(manager);
                  IContributionItem zoomInItem = manager.find(GEFActionConstants.ZOOM_IN);
                  setResult(zoomInItem);
               }
               catch (Exception e) {
                  setException(e);
               }
            }
         };
         Display.getDefault().syncExec(runMenu);
         if (runMenu.getException() != null) {
            throw runMenu.getException();
         }
         assertNotNull(runMenu.getResult());
         assertTrue(runMenu.getResult().isEnabled());
         // Select project explorer
         SWTBotView projectView = bot.viewById(ProjectExplorer.VIEW_ID);
         TestUtilsUtil.activateView(projectView);
         assertFalse(runMenu.getResult().isEnabled());
         // Select view again
         TestUtilsUtil.activateView(view);
         assertTrue(runMenu.getResult().isEnabled());
      }
      finally {
         if (view != null) {
            view.close();
         }
      }
   }
}