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

package org.key_project.sed.ui.visualization.test.testcase;

import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.debug.ui.IDebugView;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.junit.Before;
import org.junit.Test;
import org.key_project.sed.ui.visualization.test.view.LoggingDebugViewBasedEditorInViewView;
import org.key_project.sed.ui.visualization.test.view.LoggingDebugViewBasedEditorInViewView.LogEntry;
import org.key_project.sed.ui.visualization.view.AbstractDebugViewBasedEditorInViewView;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.test.perspective.EmptyTestPerspectiveFactory;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for {@link AbstractDebugViewBasedEditorInViewView}.
 * @author Martin Hentschel
 */
public class AbstractDebugViewBasedEditorInViewViewTest extends AbstractSetupTestCase {
   /**
    * {@inheritDoc}
    */
   @Before
   @Override
   public void setUp() throws Exception {
      super.setUp();
      TestUtilsUtil.closeWelcomeView();
   }

   /**
    * Makes sure that the correct {@link IDebugView} is detected when
    * views are opened, closed or activated.
    */
   @Test
   public void testOpeningClosingOfDebugViews() throws Exception {
      IPerspectiveDescriptor perspective = WorkbenchUtil.openPerspective(EmptyTestPerspectiveFactory.PERSPECTIVE_ID);
      try {
         // Open view
         LoggingDebugViewBasedEditorInViewView view = (LoggingDebugViewBasedEditorInViewView)TestUtilsUtil.openView(LoggingDebugViewBasedEditorInViewView.VIEW_ID);
         assertEquals(0, view.getLog().length);
         assertNull(view.getDebugView());
         // Open wrong debug view
         IDebugView variableView = (IDebugView)TestUtilsUtil.openView(IDebugUIConstants.ID_VARIABLE_VIEW);
         assertNotNull(variableView);
         assertEquals(0, view.getLog().length);
         assertNull(view.getDebugView());
         // Open correct debug view
         IDebugView debugView = (IDebugView)TestUtilsUtil.openView(IDebugUIConstants.ID_DEBUG_VIEW);
         assertNotNull(debugView);
         assertLog(view, null, debugView);
         assertEquals(debugView, view.getDebugView());
         // Select wrong debug view
         WorkbenchUtil.activate(variableView);
         assertEquals(0, view.getLog().length);
         assertEquals(debugView, view.getDebugView());
         // Select debug view
         WorkbenchUtil.activate(debugView);
         assertEquals(0, view.getLog().length);
         assertEquals(debugView, view.getDebugView());
         // Close wrong view
         WorkbenchUtil.closeView(variableView);
         assertEquals(0, view.getLog().length);
         assertEquals(debugView, view.getDebugView());
         // Close debug view
         WorkbenchUtil.closeView(debugView);
         assertLog(view, debugView, null);
         assertNull(view.getDebugView());
         // Close view to make sure that listener was removed
         WorkbenchUtil.closeView(view);
         // Open correct debug view
         debugView = (IDebugView)TestUtilsUtil.openView(IDebugUIConstants.ID_DEBUG_VIEW);
         assertNotNull(debugView);
         assertEquals(0, view.getLog().length);
         assertNull(view.getDebugView());
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
         IDebugView variableView = (IDebugView)TestUtilsUtil.openView(IDebugUIConstants.ID_VARIABLE_VIEW);
         assertNotNull(variableView);
         LoggingDebugViewBasedEditorInViewView view = (LoggingDebugViewBasedEditorInViewView)TestUtilsUtil.openView(LoggingDebugViewBasedEditorInViewView.VIEW_ID);
         assertEquals(0, view.getLog().length);
         assertNull(view.getDebugView());
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
         IDebugView debugView = (IDebugView)TestUtilsUtil.openView(IDebugUIConstants.ID_DEBUG_VIEW);
         assertNotNull(debugView);
         LoggingDebugViewBasedEditorInViewView view = (LoggingDebugViewBasedEditorInViewView)TestUtilsUtil.openView(LoggingDebugViewBasedEditorInViewView.VIEW_ID);
         assertLog(view, null, debugView);
         assertEquals(debugView, view.getDebugView());
      }
      finally {
         WorkbenchUtil.closePerspective(perspective, false, false);
      }
   }

   /**
    * Makes sure that the correct {@link LogEntry} was logged.
    * @param view The {@link LoggingDebugViewBasedEditorInViewView} which provides the {@link LogEntry} instances.
    * @param oldExpected The old expected {@link IDebugView}.
    * @param newExpected The new expected {@link IDebugView}.
    */
   protected void assertLog(LoggingDebugViewBasedEditorInViewView view, IDebugView oldExpected, IDebugView newExpected) {
      LogEntry[] log = view.getLog();
      assertEquals(1, log.length);
      assertEquals(oldExpected, log[0].getOldDebugView());
      assertEquals(newExpected, log[0].getNewDebugView());
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
         LoggingDebugViewBasedEditorInViewView view = (LoggingDebugViewBasedEditorInViewView)TestUtilsUtil.openView(LoggingDebugViewBasedEditorInViewView.VIEW_ID);
         assertEquals(0, view.getLog().length);
         assertNull(view.getDebugView());
      }
      finally {
         WorkbenchUtil.closePerspective(perspective, false, false);
      }
   }
}