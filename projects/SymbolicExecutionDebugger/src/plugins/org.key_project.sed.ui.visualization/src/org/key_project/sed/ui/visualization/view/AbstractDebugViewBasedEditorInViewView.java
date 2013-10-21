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

import org.eclipse.debug.ui.IDebugView;
import org.eclipse.swt.events.DisposeEvent;
import org.eclipse.swt.events.DisposeListener;
import org.eclipse.ui.IEditorActionBarContributor;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener2;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IViewReference;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartReference;
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
   private IPartListener2 partListener = new IPartListener2() {
      @Override
      public void partActivated(IWorkbenchPartReference partRef) {
         handlePartActivated(partRef);
      }

      @Override
      public void partBroughtToTop(IWorkbenchPartReference partRef) {
         handlePartBroughtToTop(partRef);
      }

      @Override
      public void partClosed(IWorkbenchPartReference partRef) {
         handlePartClosed(partRef);
      }

      @Override
      public void partDeactivated(IWorkbenchPartReference partRef) {
         handlePartDeactivated(partRef);
      }

      @Override
      public void partOpened(IWorkbenchPartReference partRef) {
         handlePartOpened(partRef);
      }

      @Override
      public void partHidden(IWorkbenchPartReference partRef) {
         handlePartHidden(partRef);
      }

      @Override
      public void partVisible(IWorkbenchPartReference partRef) {
         handlePartVisible(partRef);
      }

      @Override
      public void partInputChanged(IWorkbenchPartReference partRef) {
         handlePartInputChanged(partRef);
      }
   };
   
   /**
    * This listener is added to {@link #debugView} because the
    * Eclipse API provides no event to detect when a view is closed
    * and not only hidden.
    */
   private DisposeListener disposeListener = new DisposeListener() {
      @Override
      public void widgetDisposed(DisposeEvent e) {
         handleDebugViewDisposed(e);
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
      site.getPage().addPartListener(partListener);
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
            if (!ObjectUtil.equals(view.getId(), site.getId()) &&
                !ObjectUtil.equals(view.getId(), ExecutionTreeThumbNailView.VIEW_ID)) { // Avoid warning: Warning: Detected recursive attempt by part org.key_project.sed.ui.graphiti.view.ExecutionTreeView to create itself (this is probably, but not necessarily, a bug) 
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
    * Handles the event {@link IPartListener2#partActivated(IWorkbenchPartReference)}.
    * @param partRef The source of the event.
    */
   protected void handlePartActivated(IWorkbenchPartReference partRef) {
   }

   /**
    * Handles the event {@link IPartListener2#partBroughtToTop(IWorkbenchPartReference)}.
    * @param partRef The source of the event.
    */
   protected void handlePartBroughtToTop(IWorkbenchPartReference partRef) {
   }

   /**
    * Handles the event {@link IPartListener2#partClosed(IWorkbenchPartReference)}.
    * @param partRef The source of the event.
    */
   protected void handlePartClosed(IWorkbenchPartReference partRef) {
   }

   /**
    * Handles the event {@link IPartListener2#partDeactivated(IWorkbenchPartReference)}.
    * @param partRef The source of the event.
    */
   protected void handlePartDeactivated(IWorkbenchPartReference partRef) {
   }

   /**
    * Handles the event {@link IPartListener2#partOpened(IWorkbenchPartReference)}.
    * @param partRef The source of the event.
    */
   protected void handlePartOpened(IWorkbenchPartReference partRef) {
   }

   /**
    * Handles the event {@link IPartListener2#partHidden(IWorkbenchPartReference)}.
    * @param partRef The source of the event.
    */
   protected void handlePartHidden(IWorkbenchPartReference partRef) {
   }

   /**
    * Handles the event {@link IPartListener2#partVisible(IWorkbenchPartReference)}.
    * @param partRef The source of the event.
    */
   protected void handlePartVisible(IWorkbenchPartReference partRef) {
      IWorkbenchPart part = partRef.getPart(true);
      if (part instanceof IDebugView) {
         IDebugView debugView = (IDebugView)part;
         if (shouldHandleDebugView(debugView)) {
            setDebugView(debugView);
         }
      }
   }

   /**
    * Handles the event {@link IPartListener2#partInputChanged(IWorkbenchPartReference)}.
    * @param partRef The source of the event.
    */
   protected void handlePartInputChanged(IWorkbenchPartReference partRef) {
   }

   /**
    * When the debug view was disposed.
    * @param e The event.
    */
   protected void handleDebugViewDisposed(DisposeEvent e) {
      setDebugView(null); // Attention: The debug view is only disposed when the workbench window is closed. For this reason it is not possible to detect closings at runtime.
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      getSite().getPage().removePartListener(partListener);
      if (this.debugView != null) {
         this.debugView.getViewer().getControl().removeDisposeListener(disposeListener);
      }
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
      if (oldDebugView != null) {
         oldDebugView.getViewer().getControl().removeDisposeListener(disposeListener);
      }
      this.debugView = debugView;
      if (this.debugView != null) {
         this.debugView.getViewer().getControl().addDisposeListener(disposeListener);
      }
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