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

package org.key_project.util.eclipse.view.editorInView;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorActionBarContributor;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IKeyBindingService;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.internal.PartSite;
import org.eclipse.ui.services.IDisposable;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * <p>
 * Implementation of {@link IEditorSite} which can be used to show an
 * {@link IEditorPart} in an {@link IViewPart}.
 * </p>
 * <p>
 * The default implementation of such view is provided in {@link AbstractEditorInViewView}.
 * </p>
 * @author Martin Hentschel
 * @see AbstractEditorInViewView
 * @see EditorInViewWorkbenchPage
 */
@SuppressWarnings({ "deprecation", "restriction" })
public class EditorInViewEditorSite extends PartSite implements IEditorSite, IDisposable {
   /**
    * The {@link IViewSite} of an {@link IViewPart} which contains an {@link IEditorPart}.
    */
   private final IViewSite wrapperViewSite;
   
   /**
    * The {@link IEditorActionBarContributor} of the {@link IEditorPart} which 
    * is shown in the {@link IViewSite} of {@link #wrapperViewSite}.
    */
   private final IEditorActionBarContributor wrappedEditorContributor;
   
   /**
    * The used {@link IWorkbenchPage} used to let the {@link IEditorPart} believe
    * that he is a normal {@link IEditorPart}.
    */
   private final EditorInViewWorkbenchPage page;
   
   /**
    * Indicates that this {@link IEditorSite} is disposed or not.
    */
   private boolean disposed = false;
   
   /**
    * Collect the context menus that where registered via the {@code #registerContextMenu(...)} methods.
    */
   private final List<RegisteredContextMenu> registeredContextMenus = new LinkedList<RegisteredContextMenu>();
   
   /**
    * Constructor.
    * @param wrapperViewSite The {@link IViewSite} of an {@link IViewPart} which contains an {@link IEditorPart}.
    * @param page The {@link IEditorPart} shown in the {@link IViewPart} of {@link #wrapperViewSite}.
    * @param wrappedEditorContributor The {@link IEditorActionBarContributor} of the {@link IEditorPart} which is shown in the {@link IViewSite} of {@link #wrapperViewSite}.
    */
   public EditorInViewEditorSite(IViewSite wrapperViewSite, 
                                 EditorInViewWorkbenchPage page, 
                                 IEditorActionBarContributor wrappedEditorContributor) {
      super(((PartSite)wrapperViewSite).getModel(), wrapperViewSite.getPart(), null, null);
      Assert.isNotNull(page);
      Assert.isNotNull(wrapperViewSite);
      this.page = page;
      this.wrapperViewSite = wrapperViewSite;
      this.wrappedEditorContributor = wrappedEditorContributor;
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IActionBars getActionBars() {
      return wrapperViewSite.getActionBars();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Returns the via constructor defined {@link IEditorActionBarContributor}.
    * </p>
    */
   @Override
   public IEditorActionBarContributor getActionBarContributor() {
      return wrappedEditorContributor;
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to {@link #registerContextMenu(MenuManager, ISelectionProvider)} and the parameter includeEditorInput is lost.
    * </p>
    */
   @Override
   public void registerContextMenu(MenuManager menuManager, ISelectionProvider selectionProvider, boolean includeEditorInput) {
      registerContextMenu(menuManager, selectionProvider);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to {@link #registerContextMenu(String, MenuManager, ISelectionProvider)} and the parameter includeEditorInput is lost.
    * </p>
    */
   @Override
   public void registerContextMenu(String menuId, MenuManager menuManager, ISelectionProvider selectionProvider, boolean includeEditorInput) {
      registerContextMenu(menuId, menuManager, selectionProvider);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Returns the via constructor defined {@link EditorInViewWorkbenchPage}.
    * </p>
    */   
   @Override
   public EditorInViewWorkbenchPage getPage() {
      return page;
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}. During the constructor
    * execution it returns the active {@link IWorkbenchWindow} of {@link PlatformUI}.
    * </p>
    */
   @Override
   public IWorkbenchWindow getWorkbenchWindow() {
      return wrapperViewSite != null ? wrapperViewSite.getWorkbenchWindow() : WorkbenchUtil.getActiveWorkbenchWindow();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public String getId() {
      return wrapperViewSite.getId();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public String getPluginId() {
      return wrapperViewSite.getPluginId();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public String getRegisteredName() {
      return wrapperViewSite.getRegisteredName();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void registerContextMenu(String menuId, MenuManager menuManager, ISelectionProvider selectionProvider) {
      wrapperViewSite.registerContextMenu(menuId, menuManager, selectionProvider);
      registeredContextMenus.add(new RegisteredContextMenu(menuId, menuManager, selectionProvider));
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void registerContextMenu(MenuManager menuManager, ISelectionProvider selectionProvider) {
      wrapperViewSite.registerContextMenu(menuManager, selectionProvider);
      registeredContextMenus.add(new RegisteredContextMenu(menuManager, selectionProvider));
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IKeyBindingService getKeyBindingService() {
      return wrapperViewSite.getKeyBindingService();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public ISelectionProvider getSelectionProvider() {
      return wrapperViewSite.getSelectionProvider();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public Shell getShell() {
      return wrapperViewSite.getShell();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void setSelectionProvider(ISelectionProvider provider) {
      wrapperViewSite.setSelectionProvider(provider);
   }

   /**
    * Checks if this {@link IEditorSite} is disposed or not.
    * @return {@code true} disposed, {@code false} not disposed.
    */
   public boolean isDisposed() {
      return disposed;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (!isDisposed()) {
         disposed = true;
      }
   }
   
   /**
    * Returns all tracked {@link RegisteredContextMenu}.
    * @return All tracked {@link RegisteredContextMenu}.
    */
   public List<RegisteredContextMenu> getRegisteredContextMenus() {
      return registeredContextMenus;
   }

   /**
    * The data used to register a context menu.
    * @author Martin Hentschel
    */
   public static class RegisteredContextMenu {
      /**
       * The ID of the menu.
       */
      private final String menuId;
      
      /**
       * The {@link MenuManager}.
       */
      private final MenuManager menuManager;
      
      /**
       * The {@link ISelectionProvider}.
       */
      private final ISelectionProvider selectionProvider;

      /**
       * Constructor.
       * @param menuManager The {@link MenuManager}.
       * @param selectionProvider The {@link ISelectionProvider}.
       */
      public RegisteredContextMenu(MenuManager menuManager, ISelectionProvider selectionProvider) {
         this(null, menuManager, selectionProvider);
      }

      /**
       * Constructor.
       * @param menuId The ID of the menu.
       * @param menuManager The {@link MenuManager}.
       * @param selectionProvider The {@link ISelectionProvider}.
       */
      public RegisteredContextMenu(String menuId, MenuManager menuManager, ISelectionProvider selectionProvider) {
         this.menuId = menuId;
         this.menuManager = menuManager;
         this.selectionProvider = selectionProvider;
      }

      /**
       * Returns the ID of the menu.
       * @return The ID of the menu.
       */
      public String getMenuId() {
         return menuId;
      }

      /**
       * Returns the {@link MenuManager}.
       * @return The {@link MenuManager}.
       */
      public MenuManager getMenuManager() {
         return menuManager;
      }

      /**
       * Returns the {@link ISelectionProvider}.
       * @return The {@link ISelectionProvider}.
       */
      public ISelectionProvider getSelectionProvider() {
         return selectionProvider;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String toString() {
         return "menuId = " + menuId + ", menuManager = " + menuManager + ", selectionProvider = " + selectionProvider;
      }
   }
}