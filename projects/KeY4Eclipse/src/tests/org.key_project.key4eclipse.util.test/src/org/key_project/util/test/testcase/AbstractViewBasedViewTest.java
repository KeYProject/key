/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package org.key_project.util.test.testcase;

import junit.framework.TestCase;

import org.eclipse.ui.IPerspectiveDescriptor;
import org.eclipse.ui.IViewPart;
import org.junit.Test;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.view.AbstractViewBasedView;
import org.key_project.util.test.perspective.EmptyTestPerspectiveFactory;
import org.key_project.util.test.util.TestUtilsUtil;
import org.key_project.util.test.view.LoggingAbstractViewBasedView;
import org.key_project.util.test.view.LoggingAbstractViewBasedView.LogEntry;

/**
 * Tests for {@link AbstractViewBasedView}.
 * @author Martin Hentschel
 */
public class AbstractViewBasedViewTest extends TestCase {
   /**
    * {@inheritDoc}
    */
   @Override
   public void setUp() throws Exception {
      TestUtilsUtil.closeWelcomeView();
   }

   /**
    * Makes sure that the correct {@link IViewPart} is detected when
    * views are opened, closed or activated.
    */
   @Test
   public void testOpeningClosingOfDebugViews() throws Exception {
      IPerspectiveDescriptor perspective = WorkbenchUtil.openPerspective(EmptyTestPerspectiveFactory.PERSPECTIVE_ID);
      try {
         // Open view
         LoggingAbstractViewBasedView view = (LoggingAbstractViewBasedView)TestUtilsUtil.openView(LoggingAbstractViewBasedView.VIEW_ID);
         assertEquals(0, view.getLog().length);
         assertNull(view.getBaseView());
         // Open wrong debug view
         IViewPart variableView = (IViewPart)TestUtilsUtil.openView("org.key_project.util.test.view.GraphitiEditorInViewView");
         assertNotNull(variableView);
         assertEquals(0, view.getLog().length);
         assertNull(view.getBaseView());
         // Open correct debug view
         IViewPart debugView = (IViewPart)TestUtilsUtil.openView(LoggingAbstractViewBasedView.BASE_VIEW_ID);
         assertNotNull(debugView);
         assertLog(view, null, debugView);
         assertEquals(debugView, view.getBaseView());
         // Select wrong debug view
         WorkbenchUtil.activate(variableView);
         assertEquals(0, view.getLog().length);
         assertEquals(debugView, view.getBaseView());
         // Select debug view
         WorkbenchUtil.activate(debugView);
         assertEquals(0, view.getLog().length);
         assertEquals(debugView, view.getBaseView());
         // Close wrong view
         WorkbenchUtil.closeView(variableView);
         assertEquals(0, view.getLog().length);
         assertEquals(debugView, view.getBaseView());
         // Close debug view
         WorkbenchUtil.closeView(debugView);
         assertLog(view, debugView, null);
         assertNull(view.getBaseView());
         // Close view to make sure that listener was removed
         WorkbenchUtil.closeView(view);
         // Open correct debug view
         debugView = (IViewPart)TestUtilsUtil.openView(LoggingAbstractViewBasedView.BASE_VIEW_ID);
         assertNotNull(debugView);
         assertEquals(0, view.getLog().length);
         assertNull(view.getBaseView());
      }
      finally {
         WorkbenchUtil.closePerspective(perspective, false, false);
      }
   }
   
   /**
    * Opens an {@link AbstractDebugViewBasedEditorInViewView} in a perspective
    * that contains already a debug view which is not the expected one.
    */
   @Test
   public void testInitialOpeningWrongDebugViewAlreadyOpened() throws Exception {
      IPerspectiveDescriptor perspective = WorkbenchUtil.openPerspective(EmptyTestPerspectiveFactory.PERSPECTIVE_ID);
      try {
         IViewPart variableView = (IViewPart)TestUtilsUtil.openView("org.key_project.util.test.view.GraphitiEditorInViewView");
         assertNotNull(variableView);
         LoggingAbstractViewBasedView view = (LoggingAbstractViewBasedView)TestUtilsUtil.openView(LoggingAbstractViewBasedView.VIEW_ID);
         assertEquals(0, view.getLog().length);
         assertNull(view.getBaseView());
      }
      finally {
         WorkbenchUtil.closePerspective(perspective, false, false);
      }
   }
   
   /**
    * Opens an {@link AbstractDebugViewBasedEditorInViewView} in a perspective
    * that contains already the debug view.
    */
   @Test
   public void testInitialOpeningDebugViewAlreadyOpened() throws Exception {
      IPerspectiveDescriptor perspective = WorkbenchUtil.openPerspective(EmptyTestPerspectiveFactory.PERSPECTIVE_ID);
      try {
         IViewPart debugView = (IViewPart)TestUtilsUtil.openView(LoggingAbstractViewBasedView.BASE_VIEW_ID);
         assertNotNull(debugView);
         LoggingAbstractViewBasedView view = (LoggingAbstractViewBasedView)TestUtilsUtil.openView(LoggingAbstractViewBasedView.VIEW_ID);
         assertLog(view, null, debugView);
         assertEquals(debugView, view.getBaseView());
      }
      finally {
         WorkbenchUtil.closePerspective(perspective, false, false);
      }
   }

   /**
    * Makes sure that the correct {@link LogEntry} was logged.
    * @param view The {@link LoggingAbstractViewBasedView} which provides the {@link LogEntry} instances.
    * @param oldExpected The old expected {@link IViewPart}.
    * @param newExpected The new expected {@link IViewPart}.
    */
   protected void assertLog(LoggingAbstractViewBasedView view, IViewPart oldExpected, IViewPart newExpected) {
      LogEntry[] log = view.getLog();
      assertEquals(1, log.length);
      assertEquals(oldExpected, log[0].getOldBaseView());
      assertEquals(newExpected, log[0].getNewBaseView());
      view.clearLog();
   }
   
   /**
    * Opens an {@link AbstractDebugViewBasedEditorInViewView} in a perspective
    * that contains no other views.
    */
   @Test
   public void testInitialOpeningNoOtherViews() throws Exception {
      IPerspectiveDescriptor perspective = WorkbenchUtil.openPerspective(EmptyTestPerspectiveFactory.PERSPECTIVE_ID);
      try {
         LoggingAbstractViewBasedView view = (LoggingAbstractViewBasedView)TestUtilsUtil.openView(LoggingAbstractViewBasedView.VIEW_ID);
         assertEquals(0, view.getLog().length);
         assertNull(view.getBaseView());
      }
      finally {
         WorkbenchUtil.closePerspective(perspective, false, false);
      }
   }
}