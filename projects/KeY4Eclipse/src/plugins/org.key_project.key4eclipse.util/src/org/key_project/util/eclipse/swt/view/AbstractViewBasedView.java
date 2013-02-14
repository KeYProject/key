package org.key_project.util.eclipse.swt.view;

import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IViewReference;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.ViewPart;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

/**
 * <p>
 * Extension of {@link ViewPart} which uses another {@link IViewPart}
 * to compute the shown content.
 * </p>
 * <p>
 * Subclasses have to select an {@link IViewPart} via {@link #shouldHandleBaseView(IViewPart)}
 * and to do their job in {@link #handleBaseViewChanged(IViewPart, IViewPart)}.
 * </p>
 * @author Martin Hentschel
 */
public abstract class AbstractViewBasedView extends ViewPart {
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
    * The {@link IViewPart} which is treated by this {@link IViewPart}.
    */
   private IViewPart baseView;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IViewSite site) throws PartInitException {
      super.init(site);
      getViewSite().getPage().addPartListener(partListener);
      initBaseView(getViewSite());
   }

   /**
    * Searches the initial {@link IViewPart}.
    * @param page The {@link IWorkbenchPage} of this {@link IViewSite} to search in.
    */
   protected void initBaseView(final IViewSite site) {
      IViewReference view = ArrayUtil.search(site.getPage().getViewReferences(), new IFilter<IViewReference>() {
         @Override
         public boolean select(IViewReference view) {
            if (!ObjectUtil.equals(view.getId(), site.getId())) { // Avoid warning: Warning: Detected recursive attempt by part org.key_project.sed.ui.graphiti.view.ExecutionTreeView to create itself (this is probably, but not necessarily, a bug)
               if (shouldHandleBaseViewReference(view)) {
                  IViewPart part = view.getView(true);
                  return part instanceof IViewPart && shouldHandleBaseView((IViewPart)part);
               }
               else {
                  return false;
               }
            }
            else {
               return false;
            }
         }
      });
      setBaseView(view != null ? (IViewPart)view.getView(true) : null);
   }
   
   /**
    * Checks if the given {@link IViewReference} should be handled by this
    * {@link IViewSite}.
    * @param baseViewReference The {@link IViewReference} to check.
    * @return {@code true} = handle {@link IViewReference}, {@code false} do not handle {@link IViewReference}.
    */
   protected abstract boolean shouldHandleBaseViewReference(IViewReference baseViewReference);
   
   /**
    * Checks if the given {@link IViewPart} should be handled by this
    * {@link IViewSite}.
    * @param baseView The {@link IViewPart} to check.
    * @return {@code true} = handle {@link IViewPart}, {@code false} do not handle {@link IViewPart}.
    */
   protected abstract boolean shouldHandleBaseView(IViewPart baseView);

   /**
    * Handles the event {@link IPartListener#partClosed(IWorkbenchPart)}.
    * @param part The closed {@link IWorkbenchPart}.
    */
   protected void handlePartClosed(IWorkbenchPart part) {
      if (part instanceof IViewPart && shouldHandleBaseView((IViewPart)part)) {
         setBaseView(null);
      }
   }

   /**
    * Handles the event {@link IPartListener#partOpened(IWorkbenchPart)}.
    * @param part The opened {@link IWorkbenchPart}.
    */
   protected void handlePartOpened(IWorkbenchPart part) {
      if (part instanceof IViewPart) {
         IViewPart baseView = (IViewPart)part;
         if (shouldHandleBaseView(baseView)) {
            setBaseView(baseView);
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
    * Returns the managed {@link IViewPart}.
    * @return The managed {@link IViewPart}.
    */
   public IViewPart getBaseView() {
      return baseView;
   }

   /**
    * Sets the {@link IViewPart} to managed.
    * @param baseView The {@link IViewPart} to manage.
    */
   protected void setBaseView(IViewPart baseView) {
      IViewPart oldBaseView = this.baseView;
      this.baseView = baseView;
      if (!ObjectUtil.equals(oldBaseView, this.baseView)) {
         handleBaseViewChanged(oldBaseView, this.baseView);
      }
   }
   
   /**
    * When a new {@link IViewPart} should be managed.
    * @param oldBaseView The old {@link IViewPart}.
    * @param newBaseView The new {@link IViewPart}.
    */
   protected abstract void handleBaseViewChanged(IViewPart oldBaseView, IViewPart newBaseView);
}
