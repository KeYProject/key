package org.key_project.util.test.testcase.swtbot;

import junit.framework.TestCase;

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
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;
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
    * Tests {@link AbstractEditorInViewView#getMessage()} and
    * {@link AbstractEditorInViewView#setMessage(String)}.
    */
   @Test
   public void testMessage() throws Exception {
      SWTBotView view = null;
      try {
         // Close welcome view
         SWTWorkbenchBot bot = new SWTWorkbenchBot();
         TestUtilsUtil.closeWelcomeView(bot);
         // Open view
         final IViewPart part = TestUtilsUtil.openView(TextControlEditorInViewView.VIEW_ID);
         view = bot.viewById(TextControlEditorInViewView.VIEW_ID);
         assertTrue(view.isActive());
         assertTrue(part instanceof TextControlEditorInViewView);
         TextControlEditorInViewView textView = (TextControlEditorInViewView)part;
         // Make sure that no editor is opened
         assertEquals(0, bot.editors().size());
         // Make sure that message is shown
         SWTBotLabel label = view.bot().label();
         assertEquals("Initial message from TextControlEditorInViewView.", label.getText());
         assertTrue(label.isVisible());
         // Show new text
         textView.setMessage("Hello World!");
         assertEquals("Hello World!", label.getText());
         assertTrue(label.isVisible());
         // Show editor
         textView.setMessage(null);
         assertFalse(label.isVisible());
         SWTBotText text = view.bot().text();
         assertEquals("This is an Editor.", text.getText());
         assertTrue(text.isVisible());
         // Show editor again
         textView.setMessage(null);
         assertFalse(label.isVisible());
         assertEquals("This is an Editor.", text.getText());
         assertTrue(text.isVisible());
         // Show new text
         textView.setMessage("Hello World Again!");
         assertEquals("Hello World Again!", label.getText());
         assertTrue(label.isVisible());
         assertFalse(text.isVisible());
         // Show editor again
         textView.setMessage(null);
         assertFalse(label.isVisible());
         assertEquals("This is an Editor.", text.getText());
         assertTrue(text.isVisible());
      }
      finally {
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
