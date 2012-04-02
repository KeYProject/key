package org.key_project.util.eclipse.view.editorInView;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorActionBarContributor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.actions.ActionFactory;
import org.eclipse.ui.part.ViewPart;

/**
 * <p>
 * Provides a basic implementation to show an {@link IEditorPart} in
 * an {@link IViewPart}. Subclasses have to instantiate the used {@link IEditorPart}
 * in {@link #createEditorPart()} and the {@link IEditorInput} to use via
 * {@link #getEditorInput()}. If an {@link IEditorActionBarContributor} should
 * be used it must be created via {@link #createEditorActionBarContributor()}.
 * </p>
 * <p>
 * The virtual {@link EditorInViewEditorSite} and his {@link EditorInViewWorkbenchPage}
 * are used to let the {@link IEditorPart} believe that he is a normal {@link IEditorPart}.
 * </p>
 * @author Martin Hentschel
 * @see EditorInViewEditorSite
 * @see EditorInViewWorkbenchPage
 */
public abstract class AbstractEditorInViewView extends ViewPart {
   /**
    * The shown {@link IEditorPart}.
    */
   private IEditorPart editorPart;
   
   /**
    * The used {@link IEditorActionBarContributor} of {@link #editorPart}.
    */
   private IEditorActionBarContributor editorActionBarContributor;
   
   /**
    * The used {@link EditorInViewWorkbenchPage}.
    */
   private EditorInViewWorkbenchPage virtualEditorWorkbenchPage;
   
   /**
    * The used {@link EditorInViewEditorSite}.
    */
   private EditorInViewEditorSite virtualEditorSite;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createPartControl(Composite parent) {
      editorPart.createPartControl(parent);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IViewSite site) throws PartInitException {
      // Initialize view
      super.init(site);
      // Initialize action bars
      initActionBars(getViewSite(), getViewSite().getActionBars());
      // Create editor to show in this view
      editorPart = createEditorPart();
      Assert.isNotNull(editorPart);
      editorActionBarContributor = createEditorActionBarContributor();
      virtualEditorWorkbenchPage = new EditorInViewWorkbenchPage(getViewSite(), editorPart);
      virtualEditorSite = new EditorInViewEditorSite(getViewSite(), virtualEditorWorkbenchPage, editorActionBarContributor);
      editorPart.init(virtualEditorSite, getEditorInput());
   }

   /**
    * Creates an {@link IEditorPart} which should be shown in this {@link IViewPart}.
    * @return The created {@link IEditorPart}.
    */
   protected abstract IEditorPart createEditorPart();
   
   /**
    * Creates an {@link IEditorActionBarContributor} to use together with the created {@link IEditorPart}.
    * @return The {@link IEditorActionBarContributor} to use or {@code null} if no one should be used.
    */
   protected abstract IEditorActionBarContributor createEditorActionBarContributor();
   
   /**
    * Creates the {@link IEditorInput} which should be shown in the created {@link IEditorPart}.
    * @return The {@link IEditorInput} to show in the created {@link IEditorPart}.
    */
   protected abstract IEditorInput getEditorInput();

   /**
    * This method can be overwritten to initialize the used {@link IActionBars}.
    * The default implementation adds the edit menu to the {@link IActionBars}.
    * @param viewSite The {@link IViewSite} of this {@link IViewPart}.
    * @param actionBars The {@link IActionBars} to initialize.
    */
   protected void initActionBars(IViewSite viewSite, IActionBars actionBars) {
      MenuManager edit = new MenuManager("Edit", IWorkbenchActionConstants.M_EDIT);
      edit.add(ActionFactory.SELECT_ALL.create(viewSite.getWorkbenchWindow()));
      edit.add(ActionFactory.DELETE.create(viewSite.getWorkbenchWindow()));
      actionBars.getMenuManager().add(edit);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void setFocus() {
      editorPart.setFocus();
   }

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("rawtypes")
   @Override
   public Object getAdapter(Class adapter) {
      Object result = editorPart.getAdapter(adapter);
      if (result != null) {
         return result;
      }
      else {
         return super.getAdapter(adapter);
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (editorPart != null) {
         editorPart.dispose();
         editorPart = null;
      }
      if (editorActionBarContributor != null) {
         editorActionBarContributor.dispose();
         editorActionBarContributor = null;
      }
      if (virtualEditorSite != null) {
         virtualEditorSite.dispose();
         virtualEditorSite = null;
      }
      if (virtualEditorWorkbenchPage != null) {
         virtualEditorWorkbenchPage.dispose();
         virtualEditorWorkbenchPage = null;
      }
      super.dispose();
   }
}
