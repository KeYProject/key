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

package org.key_project.util.test.view;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IViewReference;
import org.key_project.util.eclipse.swt.view.AbstractViewBasedView;
import org.key_project.util.test.testcase.AbstractViewBasedViewTest;

/**
 * Implementation of {@link LoggingAbstractViewBasedView} which
 * logs the events detected via {@link #handleBaseViewChanged(IViewPart, IViewPart)}.
 * The view is used in test case {@link AbstractViewBasedViewTest}.
 * @author Martin Hentschel
 * @see AbstractViewBasedViewTest
 */
public class LoggingAbstractViewBasedView extends AbstractViewBasedView {
   /**
    * The ID of this view.
    */
   public static final String VIEW_ID = "org.key_project.util.test.view.LoggingAbstractViewBasedView";
   
   /**
    * The ID of the treated base view.
    */
   public static final String BASE_VIEW_ID = "org.key_project.util.test.view.TextControlEditorInViewView";
   
   /**
    * The logged events.
    */
   private List<LogEntry> log = new LinkedList<LoggingAbstractViewBasedView.LogEntry>();

   /**
    * {@inheritDoc}
    */
   @Override
   public void createPartControl(Composite parent) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setFocus() {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean shouldHandleBaseViewReference(IViewReference baseViewReference) {
      return BASE_VIEW_ID.equals(baseViewReference.getId());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean shouldHandleBaseView(IViewPart baseView) {
      return BASE_VIEW_ID.equals(baseView.getSite().getId());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleBaseViewChanged(IViewPart oldBaseView, IViewPart newBaseView) {
      log.add(new LogEntry(oldBaseView, newBaseView));
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
    * An event entry in the log. 
    * @author Martin Hentschel
    */
   public static class LogEntry {
      /**
       * The old {@link IViewPart}.
       */
      private IViewPart oldBaseView;

      /**
       * The new {@link IViewPart}.
       */
      private IViewPart newBaseView;
      
      /**
       * Constructor.
       * @param oldBaseView The old {@link IViewPart}.
       * @param newBaseView The new {@link IViewPart}.
       */
      public LogEntry(IViewPart oldBaseView, IViewPart newBaseView) {
         super();
         this.oldBaseView = oldBaseView;
         this.newBaseView = newBaseView;
      }
      
      /**
       * Returns the old {@link IViewPart}.
       * @return The old {@link IViewPart}.
       */
      public IViewPart getOldBaseView() {
         return oldBaseView;
      }
      
      /**
       * Returns the new {@link IViewPart}.
       * @return The new {@link IViewPart}.
       */
      public IViewPart getNewBaseView() {
         return newBaseView;
      }
   }
}