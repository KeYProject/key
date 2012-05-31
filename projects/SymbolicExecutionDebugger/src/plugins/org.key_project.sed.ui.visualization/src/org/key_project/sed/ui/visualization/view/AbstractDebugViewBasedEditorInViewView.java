package org.key_project.sed.ui.visualization.view;

import org.eclipse.debug.ui.IDebugView;
import org.eclipse.ui.IEditorActionBarContributor;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IViewReference;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PartInitException;
import org.key_project.util.eclipse.view.editorInView.AbstractEditorInViewView;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

/**
 * <p>
 * Extension of {@link AbstractEditorInViewView} which uses an {@link IDebugView}
 * to compute the shown content.
 * </p>
 * <p>
 * Subclasses have to select an {@link IDebugView} via {@link #shouldHandleDebugView(IDebugView)}
 * and to do their job in {@link #handleDebugViewChanged(IDebugView, IDebugView)}.
 * </p>
 * @author Martin Hentschel
 */
public abstract class AbstractDebugViewBasedEditorInViewView<E extends IEditorPart, C extends IEditorActionBarContributor> extends AbstractEditorInViewView<E, C> {
   /**
    * Listens for changes on the {@link IWorkbenchPage} of this {@link IViewSite}.
    */
   private IPartListener partListener = new IPartListener() {
      @Override
      public void partOpened(IWorkbenchPart part) {
         handlePartOpened(part);
      }
      
      @Override
      public void partDeactivated(IWorkbenchPart part) {
         handlePartDeactivated(part);
      }
      
      @Override
      public void partClosed(IWorkbenchPart part) {
         handlePartClosed(part);
      }
      
      @Override
      public void partBroughtToTop(IWorkbenchPart part) {
         handlePartBroughtToTop(part);
      }
      
      @Override
      public void partActivated(IWorkbenchPart part) {
         handlePartActivated(part);
      }
   };
   
   /**
    * The {@link IDebugView} which is treated by this {@link IViewPart}.
    */
   private IDebugView debugView;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IViewSite site) throws PartInitException {
      super.init(site);
      getViewSite().getPage().addPartListener(partListener); // TODO: Fix bug that listener observes only the own events and not the events from other views.
      initDebugView(getViewSite());
   }

   /**
    * Searches the initial {@link IDebugView}.
    * @param page The {@link IWorkbenchPage} of this {@link IViewSite} to search in.
    */
   protected void initDebugView(final IViewSite site) {
      IViewReference view = ArrayUtil.search(site.getPage().getViewReferences(), new IFilter<IViewReference>() {
         @Override
         public boolean select(IViewReference view) {
            if (!ObjectUtil.equals(view.getId(), site.getId())) { // Avoid warning: Warning: Detected recursive attempt by part org.key_project.sed.ui.graphiti.view.ExecutionTreeView to create itself (this is probably, but not necessarily, a bug) 
               IViewPart part = view.getView(true);
               return part instanceof IDebugView && shouldHandleDebugView((IDebugView)part);
            }
            else {
               return false;
            }
         }
      });
      setDebugView(view != null ? (IDebugView)view.getView(true) : null);
   }
   
   /**
    * Checks if the given {@link IDebugView} should be handled by this
    * {@link IViewSite}.
    * @param debugView The {@link IDebugView} to check.
    * @return {@code true} = handle {@link IDebugView}, {@code false} do not handle {@link IDebugView}.
    */
   protected abstract boolean shouldHandleDebugView(IDebugView debugView);

   /**
    * Handles the event {@link IPartListener#partClosed(IWorkbenchPart)}.
    * @param part The closed {@link IWorkbenchPart}.
    */
   protected void handlePartClosed(IWorkbenchPart part) {
      if (part instanceof IDebugView && shouldHandleDebugView((IDebugView)part)) {
         setDebugView(null);
      }
   }

   /**
    * Handles the event {@link IPartListener#partOpened(IWorkbenchPart)}.
    * @param part The opened {@link IWorkbenchPart}.
    */
   protected void handlePartOpened(IWorkbenchPart part) {
      if (part instanceof IDebugView) {
         IDebugView debugView = (IDebugView)part;
         if (shouldHandleDebugView(debugView)) {
            setDebugView(debugView);
         }
      }
   }

   /**
    * Handles the event {@link IPartListener#partActivated(IWorkbenchPart)}.
    * @param part The activated {@link IWorkbenchPart}.
    */
   protected void handlePartActivated(IWorkbenchPart part) {
   }

   /**
    * Handles the event {@link IPartListener#partBroughtToTop(IWorkbenchPart)}.
    * @param part The {@link IWorkbenchPart} brought to top.
    */
   protected void handlePartBroughtToTop(IWorkbenchPart part) {
   }

   /**
    * Handles the event {@link IPartListener#partDeactivated(IWorkbenchPart)}.
    * @param part The deactivated {@link IWorkbenchPart}.
    */
   protected void handlePartDeactivated(IWorkbenchPart part) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      getViewSite().getPage().removePartListener(partListener);
      super.dispose();
   }

   /**
    * Returns the managed {@link IDebugView}.
    * @return The managed {@link IDebugView}.
    */
   public IDebugView getDebugView() {
      return debugView;
   }

   /**
    * Sets the {@link IDebugView} to managed.
    * @param debugView The {@link IDebugView} to manage.
    */
   protected void setDebugView(IDebugView debugView) {
      IDebugView oldDebugView = this.debugView;
      this.debugView = debugView;
      if (!ObjectUtil.equals(oldDebugView, this.debugView)) {
         handleDebugViewChanged(oldDebugView, this.debugView);
      }
   }
   
   /**
    * When a new {@link IDebugView} should be managed.
    * @param oldDebugView The old {@link IDebugView}.
    * @param newDebugView The new {@link IDebugView}.
    */
   protected abstract void handleDebugViewChanged(IDebugView oldDebugView, IDebugView newDebugView);
}
