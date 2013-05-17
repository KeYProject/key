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

package org.key_project.sed.ui.visualization.view;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IViewReference;

/**
 * This {@link IViewPart} shows a thumbnail of the Graphiti editor shown
 * in an {@link ExecutionTreeView}.
 * @author Martin Hentschel
 */
public class ExecutionTreeThumbNailView extends AbstractViewBasedThumbNailView {
   /**
    * The ID of this view.
    */
   public static final String VIEW_ID = "org.key_project.sed.ui.graphiti.view.ExecutionTreeThumbNailView";

   /**
    * Listens for visibility changes of the editor in the base view.
    */
   private PropertyChangeListener editorVisibleListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handleEditorVisiblePropertyChange(evt);
      }
   };

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean shouldHandleBaseViewReference(IViewReference baseViewReference) {
      return ExecutionTreeView.VIEW_ID.equals(baseViewReference.getId());
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean shouldHandleBaseView(IViewPart baseView) {
      return baseView instanceof ExecutionTreeView;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleBaseViewChanged(IViewPart oldBaseView, IViewPart newBaseView) {
      if (oldBaseView != null) {
         ((ExecutionTreeView)oldBaseView).removePropertyChangeListener(ExecutionTreeView.PROP_EDITOR_SHOWN, editorVisibleListener);
      }
      if (newBaseView != null) {
         ((ExecutionTreeView)newBaseView).addPropertyChangeListener(ExecutionTreeView.PROP_EDITOR_SHOWN, editorVisibleListener);
      }
      super.handleBaseViewChanged(oldBaseView, newBaseView);
   }   
   
   /**
    * When the editor is shown or hidden in the base view.
    * @param evt The even.
    */
   protected void handleEditorVisiblePropertyChange(PropertyChangeEvent evt) {
      refreshThumbnailViewer();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void refreshThumbnailViewer() {
      ExecutionTreeView part = (ExecutionTreeView)getBaseView();
      if (part != null && part.isEditorShown()) {
         createThumbNailViewer(part); // Show thumb nail.
      }
      else {
         createThumbNailViewer(null); // Show nothing if the editor is not visible in base view.
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (getBaseView() != null) {
         ((ExecutionTreeView)getBaseView()).removePropertyChangeListener(ExecutionTreeView.PROP_EDITOR_SHOWN, editorVisibleListener);
      }
      super.dispose();
   }
}