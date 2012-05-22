package org.key_project.sed.ui.visualization.view;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.ui.IViewPart;

/**
 * This {@link IViewPart} shows a thumbnail of the Graphiti editor shown
 * in an {@link ExecutionTreeView}.
 * @author Martin Hentschel
 */
public class ExecutionTreeThumbNailView extends AbstractViewBasedThumbNailView {
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