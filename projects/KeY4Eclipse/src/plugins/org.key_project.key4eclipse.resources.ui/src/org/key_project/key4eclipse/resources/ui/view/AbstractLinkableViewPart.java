package org.key_project.key4eclipse.resources.ui.view;

import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.IStateListener;
import org.eclipse.core.commands.State;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IPropertyListener;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.handlers.RegistryToggleState;
import org.eclipse.ui.part.EditorPart;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.view.AbstractWorkbenchPartBasedView;

/**
 * Provides the basic functionality for {@link IViewPart}s for which
 * the content is linked with other {@link IWorkbenchPart}s.
 * @author Martin Hentschel
 */
public abstract class AbstractLinkableViewPart extends AbstractWorkbenchPartBasedView {
   /**
    * The link with editor/view state.
    */
   private State linkState;
   
   /**
    * Listens for changes on {@link #linkState}.
    */
   private final IStateListener stateListener = new IStateListener() {
      @Override
      public void handleStateChange(State state, Object oldValue) {
         refreshContentCausedByLinking();
      }
   };
   
   /**
    * The base {@link IWorkbenchPart} for which the content will be shown
    * if {@link #linkState} is selected.
    */
   private IWorkbenchPart basePart;
   
   /**
    * Listens for changes on {@link #basePart}.
    */
   private final IPropertyListener basePartListener = new IPropertyListener() {
      @Override
      public void propertyChanged(Object source, int propId) {
         handleBasePartPropertyChanged(source, propId);
      }
   };

   /**
    * Listens for changes on {@link #basePart}.
    */
   private final ISelectionChangedListener basePartSelectionChangedListener = new ISelectionChangedListener() {
      @Override
      public void selectionChanged(SelectionChangedEvent event) {
         handleBasePartSelectionChanged(event);
      }
   };

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IViewSite site) throws PartInitException {
      super.init(site);
      ICommandService service = (ICommandService)PlatformUI.getWorkbench().getService(ICommandService.class);
      Command linkCmd = service.getCommand("org.key_project.key4eclipse.resources.ui.LinkWithWorkbenchPartCommand");
      if (linkCmd != null) {
         linkState = linkCmd.getState(RegistryToggleState.STATE_ID);
         if (linkState != null) {
            linkState.addListener(stateListener);
         }
      }
      basePart = site.getPage().getActivePart();
      if (basePart instanceof EditorPart) {
         ((EditorPart) basePart).addPropertyListener(basePartListener);
      }
      if (basePart != null && basePart.getSite() != null && basePart.getSite().getSelectionProvider() != null) {
         basePart.getSite().getSelectionProvider().addSelectionChangedListener(basePartSelectionChangedListener);
      }
   }

   /**
    * Checks if the shown content is linked with the selected {@link IWorkbenchPart}.
    * @return {@code true} is linked, {@code false} is independent.
    */
   public boolean isLinkWithBasePart() {
      boolean linkWith = false;
      if (linkState != null) {
         Object value = linkState.getValue();
         linkWith = value instanceof Boolean && ((Boolean) value).booleanValue();
      }
      return linkWith;
   }

   /**
    * When the linked state has changed.
    * The current state is available via {@link #isLinkWithBasePart()}.
    */
   protected abstract void refreshContentCausedByLinking();

   /**
    * When a property on {@link #basePart} has changed.
    * @param source The source {@link Object}.
    * @param propId The ID of the changed property.
    */
   protected void handleBasePartPropertyChanged(Object source, int propId) {
      if (propId == EditorPart.PROP_INPUT) {
         refreshContentCausedByLinking();
      }
   }

   /**
    * When the selection on {@link #basePart} has changed.
    * @param event The {@link SelectionChangedEvent}.
    */
   protected void handleBasePartSelectionChanged(SelectionChangedEvent event) {
      if (event.getSelection() instanceof IStructuredSelection) {
         refreshContentCausedByLinking();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handlePartActivated(IWorkbenchPart part) {
      updateBasePart();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handlePartDeactivated(IWorkbenchPart part) {
      updateBasePart();
   }
   
   /**
    * Updates {@link #basePart} and if required the shown content.
    */
   protected void updateBasePart() {
      IWorkbenchPart activePart = getSite().getPage().getActivePart();
      if (activePart != this) {
         if (activePart != basePart) {
            if (basePart instanceof EditorPart) {
               ((EditorPart) basePart).removePropertyListener(basePartListener);
            }
            if (basePart != null && basePart.getSite() != null && basePart.getSite().getSelectionProvider() != null) {
               basePart.getSite().getSelectionProvider().removeSelectionChangedListener(basePartSelectionChangedListener);
            }
            basePart = activePart;
            if (basePart instanceof EditorPart) {
               ((EditorPart) basePart).addPropertyListener(basePartListener);
            }
            if (basePart != null && basePart.getSite() != null && basePart.getSite().getSelectionProvider() != null) {
               basePart.getSite().getSelectionProvider().addSelectionChangedListener(basePartSelectionChangedListener);
            }
            if (isLinkWithBasePart()) {
               refreshContentCausedByLinking();
            }
         }
      }
   }
   
   /**
    * Computes the {@link IResource} linked with.
    * @return The {@link IResource}s linked with.
    */
   protected Set<IResource> computeLinkedResources() {
      Set<IResource> result = new HashSet<IResource>();
      if (basePart instanceof IEditorPart) {
         IEditorInput input = ((IEditorPart) basePart).getEditorInput();
         if (input instanceof IFileEditorInput) {
            IFile file = ((IFileEditorInput) input).getFile();
            if (file != null) {
               result.add(file);
            }
         }
      }
      if (basePart != null && basePart.getSite() != null && basePart.getSite().getSelectionProvider() != null) {
         ISelection selection = basePart.getSite().getSelectionProvider().getSelection();
         Object[] elements = SWTUtil.toArray(selection);
         for (Object element : elements) {
            if (element instanceof IResource) {
               result.add((IResource) element);
            }
            else if (element instanceof IAdaptable) {
               Object adapted = ((IAdaptable) element).getAdapter(IResource.class);
               if (adapted instanceof IResource) {
                  result.add((IResource) adapted);
               }
            }
         }
      }
      return result;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (basePart instanceof EditorPart) {
         ((EditorPart) basePart).removePropertyListener(basePartListener);
      }
      if (basePart != null && basePart.getSite() != null && basePart.getSite().getSelectionProvider() != null) {
         basePart.getSite().getSelectionProvider().removeSelectionChangedListener(basePartSelectionChangedListener);
      }
      if (linkState != null) {
         linkState.removeListener(stateListener);
      }
      super.dispose();
   }
}
