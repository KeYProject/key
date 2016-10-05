package org.key_project.sed.ui.visualization.view;

import java.util.LinkedHashSet;
import java.util.Set;

import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.internal.ui.viewers.model.TreeModelContentProvider;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IViewerUpdate;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IViewerUpdateListener;
import org.eclipse.debug.internal.ui.views.launch.LaunchView;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.debug.ui.IDebugView;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.ui.IEditorActionBarContributor;
import org.eclipse.ui.IEditorPart;
import org.key_project.sed.core.model.ISEDebugElement;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.ui.util.SEDUIUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.ObjectUtil;

/**
 * This {@link AbstractDebugViewBasedEditorInViewView} treats only the {@link LaunchView}.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public abstract class AbstractLaunchViewBasedEditorInViewView<E extends IEditorPart, C extends IEditorActionBarContributor> extends AbstractDebugViewBasedEditorInViewView<E, C> {
   /**
    * The message which is shown to the user if the debug view is not opened.
    */
   public static final String MESSAGE_DEBUG_VIEW_NOT_OPENED = "View \"Debug\" is not opened.";

   /**
    * The message which is shown if no {@link ISEDebugTarget} is selected.
    */
   public static final String MESSAGE_NO_DEBUG_TARGET_SELECTED = "No symbolic debug target is selected in View \"Debug\".";
   
   /**
    * Listens for selection changes on {@link #getDebugView()}.
    */
   private final ISelectionChangedListener debugViewSelectionListener = new ISelectionChangedListener() {
      @Override
      public void selectionChanged(SelectionChangedEvent event) {
         handleDebugViewSelectionChanged(event);
      }
   };
   
   /**
    * Listens for changes on the {@link TreeModelContentProvider} of {@link #getDebugView()}.
    */
   private final IViewerUpdateListener contentProviderListener = new IViewerUpdateListener() {
      @Override
      public void viewerUpdatesComplete() {
         handleViewerUpdatesComplete();
      }
      
      @Override
      public void viewerUpdatesBegin() {
         handleViewerUpdatesBegin();
      }
      
      @Override
      public void updateStarted(IViewerUpdate update) {
      }
      
      @Override
      public void updateComplete(IViewerUpdate update) {
      }
   };

   /**
    * Indicates that currently an update is in progress on the content provider of {@link #getDebugView()}.
    */
   private boolean viewerUpdateInProgress = false;
   
   /**
    * The last unhandled {@link SelectionChangedEvent} because an update on the content provider of {@link #getDebugView()} was in progress or a {@link Job} was running.
    */
   private SelectionChangedEvent eventToHandle;
  
   /**
    * Contains the shown debug targets.
    */
   private Set<ISEDebugTarget> shownDebugTargets;
   
   /**
    * Constructor.
    */
   public AbstractLaunchViewBasedEditorInViewView() {
      setMessage(MESSAGE_DEBUG_VIEW_NOT_OPENED);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      IDebugView debugView = getDebugView();
      if (debugView != null) {
         debugView.getSite().getSelectionProvider().removeSelectionChangedListener(debugViewSelectionListener);
         TreeModelContentProvider cp = SEDUIUtil.getContentProvider(debugView);
         if (cp != null) {
            cp.removeViewerUpdateListener(contentProviderListener);
         }
      }
      super.dispose();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void editorPartControlCreated(E editorPart, C contributor) {
      IDebugView debugView = getDebugView();
      if (debugView != null) {
         updateEditorContent(debugView.getViewer().getSelection());
         TreeModelContentProvider cp = SEDUIUtil.getContentProvider(debugView);
         if (cp != null) {
            cp.addViewerUpdateListener(contentProviderListener);
         }
      }
   }

   
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
      // Cleanup old view
      if (oldDebugView != null) {
         oldDebugView.getSite().getSelectionProvider().removeSelectionChangedListener(debugViewSelectionListener);
         TreeModelContentProvider cp = SEDUIUtil.getContentProvider(oldDebugView);
         if (cp != null) {
            cp.removeViewerUpdateListener(contentProviderListener);
         }
      }
      // Handle new view
      if (newDebugView != null) {
         newDebugView.getSite().getSelectionProvider().addSelectionChangedListener(debugViewSelectionListener);
         TreeModelContentProvider cp = SEDUIUtil.getContentProvider(newDebugView);
         if (cp != null) {
            cp.addViewerUpdateListener(contentProviderListener);
         }
         setMessage(MESSAGE_NO_DEBUG_TARGET_SELECTED);
         updateEditorContent(getDebugView().getSite().getSelectionProvider().getSelection());
      }
      else {
         setMessage(MESSAGE_DEBUG_VIEW_NOT_OPENED);
      }
   }
   
   /**
    * Updates the content shown in {@link #getEditorPart()}.
    * @param debugViewSelection The {@link ISelection} with the new {@link ISEDebugTarget}s to show.
    */
   protected void updateEditorContent(ISelection debugViewSelection) {
      try {
         final Set<ISEDebugTarget> oldTargets = shownDebugTargets;
         // Make sure that the editor is already created; ignore event otherwise.
         if (isEditorAvailable()) { 
            // Collect ISEDDebugTargets to show
            final Set<ISEDebugTarget> targets = new LinkedHashSet<ISEDebugTarget>();
            Object[] elements = SWTUtil.toArray(debugViewSelection);
            for (Object element : elements) {
               if (element instanceof ISEDebugElement) {
                  targets.add(((ISEDebugElement)element).getDebugTarget());
               }
               else if (element instanceof ILaunch) {
                  IDebugTarget[] launchTargets = ((ILaunch)element).getDebugTargets();
                  for (IDebugTarget target : launchTargets) {
                     if (target instanceof ISEDebugTarget) {
                        targets.add((ISEDebugTarget)target);
                     }
                  }
               }
            }
            // Check if new targets are selected
            if (!CollectionUtil.containsSame(targets, oldTargets)) {
               shownDebugTargets = targets;
            }
            doUpdateEditorContent(oldTargets, targets, elements);
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
      }
   }
   
   /**
    * Checks if the editor is already available.
    * @return {@code true} editor is available, {@code false} editor is not available.
    */
   protected boolean isEditorAvailable() {
      return getEditorPart() != null;
   }
   
   /**
    * Performs the actual change of the content in {@link #getEditorPart()}.
    * @param oldTargets The old {@link ISEDebugTarget}s.
    * @param newTargets The new {@link ISEDebugTarget}s.
    * @param newElements All elements in the new selection.
    */
   protected abstract void doUpdateEditorContent(Set<ISEDebugTarget> oldTargets, 
                                                 Set<ISEDebugTarget> newTargets, 
                                                 Object[] newElements);

   /**
    * When the selection on {@link #getDebugView()} has changed.
    * @param event The event.
    */
   protected void handleDebugViewSelectionChanged(SelectionChangedEvent event) {
      if (isViewerUpdateInProgress()) {
         eventToHandle = event;
      }
      else {
         if (event != null) {
            // Make sure that event was provided by debug's viewer and not by something else what can happen if a maximized view is minimized.
            if (ObjectUtil.equals(event.getSource(), getDebugView().getViewer())) {
               // Update diagram
               updateEditorContent(event.getSelection());
            }
         }
      }
   }
   
   protected boolean isViewerUpdateInProgress() {
      return viewerUpdateInProgress;
   }

   /**
    * When an update on the content provider of {@link #getDebugView()} has started.
    */
   protected synchronized void handleViewerUpdatesBegin() {
      viewerUpdateInProgress = true;
   }

   /**
    * When an update on the content provider of {@link #getDebugView()} has finished.
    */
   protected synchronized void handleViewerUpdatesComplete() {
      viewerUpdateInProgress = false;
      handleEventToHandleNow();
   }
   
   /**
    * Tries to handle an unhandled event now.
    */
   protected synchronized void handleEventToHandleNow() {
      if (eventToHandle != null && !isViewerUpdateInProgress()) {
         final SelectionChangedEvent toHandleNow = eventToHandle;
         eventToHandle = null;
         getSite().getShell().getDisplay().asyncExec(new Runnable() {
            @Override
            public void run() {
               handleDebugViewSelectionChanged(toHandleNow);
            }
         });
      }
   }
}
