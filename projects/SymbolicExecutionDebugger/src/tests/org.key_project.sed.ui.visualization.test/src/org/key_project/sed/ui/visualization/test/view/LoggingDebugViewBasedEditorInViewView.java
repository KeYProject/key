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

package org.key_project.sed.ui.visualization.test.view;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.debug.ui.IDebugView;
import org.eclipse.ui.IEditorActionBarContributor;
import org.eclipse.ui.IEditorInput;
import org.key_project.sed.ui.visualization.test.testcase.AbstractDebugViewBasedEditorInViewViewTest;
import org.key_project.sed.ui.visualization.view.AbstractDebugViewBasedEditorInViewView;
import org.key_project.util.test.editor.TextControlEditor;

/**
 * Implementation of {@link AbstractDebugViewBasedEditorInViewView} which
 * logs the events detected via {@link #handleDebugViewChanged(IDebugView, IDebugView)}.
 * The view is used in test case {@link AbstractDebugViewBasedEditorInViewViewTest}.
 * @author Martin Hentschel
 * @see AbstractDebugViewBasedEditorInViewViewTest
 */
public class LoggingDebugViewBasedEditorInViewView extends AbstractDebugViewBasedEditorInViewView<TextControlEditor, IEditorActionBarContributor> {
   /**
    * The ID of this view.
    */
   public static final String VIEW_ID = "org.key_project.sed.ui.visualization.test.view.LoggingDebugViewBasedEditorInViewView";
   
   /**
    * The logged events.
    */
   private List<LogEntry> log = new LinkedList<LoggingDebugViewBasedEditorInViewView.LogEntry>();
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean shouldHandleDebugView(IDebugView debugView) {
      return IDebugUIConstants.ID_DEBUG_VIEW.equals(debugView.getSite().getId());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleDebugViewChanged(IDebugView oldDebugView, IDebugView newDebugView) {
      log.add(new LogEntry(oldDebugView, newDebugView));
   }
   
   /**
    * Returns the log.
    * @return The log.
    */
   public LogEntry[] getLog() {
      return log.toArray(new LogEntry[log.size()]);
   }

   /**
    * Clears the log.
    */
   public void clearLog() {
      log.clear();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected TextControlEditor createEditorPart() {
      return new TextControlEditor();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IEditorActionBarContributor createEditorActionBarContributor() {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IEditorInput createEditorInput() {
      return null;
   }
   
   /**
    * An event entry in the log. 
    * @author Martin Hentschel
    */
   public static class LogEntry {
      /**
       * The old {@link IDebugView}.
       */
      private IDebugView oldDebugView;

      /**
       * The new {@link IDebugView}.
       */
      private IDebugView newDebugView;
      
      /**
       * Constructor.
       * @param oldDebugView The old {@link IDebugView}.
       * @param newDebugView The new {@link IDebugView}.
       */
      public LogEntry(IDebugView oldDebugView, IDebugView newDebugView) {
         super();
         this.oldDebugView = oldDebugView;
         this.newDebugView = newDebugView;
      }
      
      /**
       * Returns the old {@link IDebugView}.
       * @return The old {@link IDebugView}.
       */
      public IDebugView getOldDebugView() {
         return oldDebugView;
      }
      
      /**
       * Returns the new {@link IDebugView}.
       * @return The new {@link IDebugView}.
       */
      public IDebugView getNewDebugView() {
         return newDebugView;
      }
   }
}