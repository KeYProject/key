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

import java.beans.PropertyChangeListener;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StackLayout;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Widget;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorActionBarContributor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.ISaveablePart;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.actions.ActionFactory;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.view.AbstractBeanViewPart;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

/**
 * <p>
 * Provides a basic implementation to show an {@link IEditorPart} in
 * an {@link IViewPart}. Subclasses have to instantiate the used {@link IEditorPart}
 * in {@link #createEditorPart()} and the {@link IEditorInput} to use via
 * {@link #createEditorInput()}. If an {@link IEditorActionBarContributor} should
 * be used it must be created via {@link #createEditorActionBarContributor()}.
 * </p>
 * <p>
 * The virtual {@link EditorInViewEditorSite} and his {@link EditorInViewWorkbenchPage}
 * are used to let the {@link IEditorPart} believe that he is a normal {@link IEditorPart}.
 * </p>
 * <p>
 * Instead of the editor it is possible to show a message to the user. The
 * message is defined via {@link #setMessage(String)} and accessible via
 * {@link #getMessage()}. It is also possible in subclasses to show other
 * SWT {@link Widget}s instead of the editor by overwriting {@link #createAdditionalControls(Composite)}
 * and {@link #updateShownControl(Composite, StackLayout)}. 
 * </p>
 * <p>
 * If the used {@link IEditorPart} and/or {@link IEditorActionBarContributor}
 * is also an instance of {@link IGlobalEnablement} his global enablement state
 * is synchronized with {@link #isEditorShown()} value. This can be used to 
 * disable actions and keyboard shortcuts of the editor/contributor when
 * a message is shown. 
 * </p>
 * @author Martin Hentschel
 * @see EditorInViewEditorSite
 * @see EditorInViewWorkbenchPage
 * @see IGlobalEnablement
 */
public abstract class AbstractEditorInViewView<E extends IEditorPart, C extends IEditorActionBarContributor> extends AbstractBeanViewPart implements ISaveablePart {
   /**
    * Property of {@link #isEditorShown()} which can be observed via a {@link PropertyChangeListener}.
    */
   public static final String PROP_EDITOR_SHOWN = "editorShown";
   
   /**
    * Property of {@link #isMessageShown()} which can be observed via a {@link PropertyChangeListener}.
    */
   public static final String PROP_MESSAGE_SHOWN = "messageShown";
   
   /**
    * The shown {@link IEditorPart}.
    */
   private E editorPart;
   
   /**
    * The used {@link IEditorActionBarContributor} of {@link #editorPart}.
    */
   private C editorActionBarContributor;
   
   /**
    * The used {@link EditorInViewWorkbenchPage}.
    */
   private EditorInViewWorkbenchPage virtualEditorWorkbenchPage;
   
   /**
    * The used {@link EditorInViewEditorSite}.
    */
   private EditorInViewEditorSite virtualEditorSite;
   
   /**
    * The {@link Composite} which contains the whole content of this
    * {@link IViewSite}. It contains {@link #editorComposite} or {@link #messageLabel}.
    */
   private Composite rootComposite;
   
   /**
    * Layout of {@link #rootComposite}.
    */
   private StackLayout rootLayout;
   
   /**
    * {@link Composite} which contains the created editor.
    */
   private Composite editorComposite;
   
   /**
    * {@link Label} which shows a message.
    */
   private Label messageLabel;
   
   /**
    * The text shown in {@link #messageLabel}.
    */
   private String messageText;
   
   /**
    * Indicates if the editor is enabled or not.
    */
   private boolean editorEnabled = true;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createPartControl(Composite parent) {
      // Create root
      rootLayout = new StackLayout();
      rootComposite = new Composite(parent, SWT.NONE);
      rootComposite.setLayout(rootLayout);
      // Create editor
      editorComposite = new Composite(rootComposite, SWT.NONE);
      editorComposite.setLayout(new FillLayout());
      editorComposite.setEnabled(isEditorEnabled());
      editorPart.createPartControl(editorComposite);
      editorPartControlCreated(editorPart, editorActionBarContributor);
      // Create message label
      createAdditionalControls(rootComposite);
      // Show editor or message text
      updateShownControl(rootComposite, rootLayout);
   }

   /**
    * Can be overwritten in subclasses to do some work after the editor control
    * is created.
    * @param editorPart The {@link IEditorPart} for that the part control was created
    * @param contributor The {@link IEditorActionBarContributor} which is used for the {@link IEditorPart}.
    */
   protected void editorPartControlCreated(E editorPart, C contributor) {
   }

   /**
    * Creates additional controls like the message {@link Label}.
    * @param parent The parent {@link Composite}.
    */
   protected void createAdditionalControls(Composite parent) {
      messageLabel = new Label(parent, SWT.NONE);
      SWTUtil.setText(messageLabel, messageText);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IViewSite site) throws PartInitException {
      // Initialize view
      super.init(site);
      // Create editor to show in this view
      editorPart = createEditorPart();
      Assert.isNotNull(editorPart);
      editorActionBarContributor = createEditorActionBarContributor();
      virtualEditorWorkbenchPage = new EditorInViewWorkbenchPage(getViewSite(), editorPart);
      virtualEditorSite = new EditorInViewEditorSite(getViewSite(), virtualEditorWorkbenchPage, editorActionBarContributor);
      initActionBars(getViewSite(), virtualEditorSite.getActionBars());
      if (editorActionBarContributor != null) {
         editorActionBarContributor.init(virtualEditorSite.getActionBars(), virtualEditorWorkbenchPage);
      }
      editorPart.init(virtualEditorSite, createEditorInput());
   }

   /**
    * Creates an {@link IEditorPart} which should be shown in this {@link IViewPart}.
    * @return The created {@link IEditorPart}.
    */
   protected abstract E createEditorPart();
   
   /**
    * Creates an {@link IEditorActionBarContributor} to use together with the created {@link IEditorPart}.
    * @return The {@link IEditorActionBarContributor} to use or {@code null} if no one should be used.
    */
   protected abstract C createEditorActionBarContributor();
   
   /**
    * Creates the {@link IEditorInput} which should be shown in the created {@link IEditorPart}.
    * @return The {@link IEditorInput} to show in the created {@link IEditorPart}.
    */
   protected abstract IEditorInput createEditorInput();

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
      if (isEditorShown()) {
         editorPart.setFocus();
      }
      else if (isMessageShown()) {
         messageLabel.setFocus();
      }
      else {
         rootComposite.setFocus();
      }
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
      if (IEditorPart.class.equals(adapter)) {
         return getEditorPart();
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
   
   /**
    * Returns the shown message or {@code null}/empty string if the editor is shown.
    * @return The shown message or {@code null}/empty string if the editor is shown.
    */
   public String getMessage() {
      return messageText;
   }
   
   /**
    * Sets the message to show.
    * @param message The message to show or {@code null}/empty string to show the editor.
    */
   protected void setMessage(final String message) {
      this.messageText = message;
      if (messageLabel != null) {
         messageLabel.getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               SWTUtil.setText(messageLabel, message);
               updateShownControl(rootComposite, rootLayout);
            };
         });
      }
   }
   
   /**
    * Updates the visible control in the given root composite and his {@link StackLayout}.
    * @param root The root {@link Composite} of this {@link IViewSite}.
    * @param layout The {@link StackLayout} used in the given root {@link Composite}.
    */
   protected void updateShownControl(Composite root, StackLayout layout) {
      boolean oldEditorShown = isEditorShown();
      boolean oldMessageShown = isMessageShown();
      if (!StringUtil.isEmpty(messageText)) {
         layout.topControl = messageLabel;
      }
      else {
         layout.topControl = editorComposite;
      }
      root.layout();
      boolean editorShown = isEditorShown();
      updateEditorsGlobalEnablement(editorShown && isEditorEnabled());
      firePropertyChange(PROP_EDITOR_SHOWN, oldEditorShown, editorShown);
      firePropertyChange(PROP_MESSAGE_SHOWN, oldMessageShown, isMessageShown());
      firePropertyChange(PROP_DIRTY); // Fire event to update save and saveAs in workbench window
   }
   
   /**
    * Updates the global enabled state of the editor and his action bar contributor.
    * @param enabled The global enabled state to set.
    */
   protected void updateEditorsGlobalEnablement(boolean enabled) {
      if (editorActionBarContributor instanceof IGlobalEnablement) {
         ((IGlobalEnablement)editorActionBarContributor).setGlobalEnabled(enabled);
      }
      if (editorPart instanceof IGlobalEnablement) {
         ((IGlobalEnablement)editorPart).setGlobalEnabled(enabled);
      }
   }

   /**
    * Checks if the editor is enabled or not.
    * @return {@code true} editor is enabled, {@code false} editor is not enabled.
    */
   public boolean isEditorEnabled() {
      return editorEnabled;
   }

   /**
    * Defines if the editor is enabled or not.
    * @param editorEnabled {@code true} editor is enabled, {@code false} editor is not enabled.
    */
   public void setEditorEnabled(boolean editorEnabled) {
      this.editorEnabled = editorEnabled;
      Display.getDefault().syncExec(new Runnable() {
         @Override
         public void run() {
            if (editorComposite != null && !editorComposite.isDisposed()) {
               editorComposite.setEnabled(AbstractEditorInViewView.this.editorEnabled);
            }
            updateEditorsGlobalEnablement(AbstractEditorInViewView.this.editorEnabled && isEditorShown());
         }
      });
   }

   /**
    * Returns the {@link Composite} which contains the created {@link IEditorPart}.
    * @return The {@link Composite} which contains the created {@link IEditorPart}.
    */
   protected Composite getEditorComposite() {
      return editorComposite;
   }

   /**
    * Returns the contained {@link IEditorPart}.
    * @return The {@link IEditorPart} or {@code null} if it was not instantiated yet.
    */
   public E getEditorPart() {
      return editorPart;
   }

   /**
    * Returns the used {@link IEditorActionBarContributor} of {@link #getEditorPart()}.
    * @return The {@link IEditorActionBarContributor} or {@code null} if it was not instantiated yet/is not available.
    */
   protected C getEditorActionBarContributor() {
      return editorActionBarContributor;
   }
   
   /**
    * Checks if a message is shown.
    * @return {@code true} a message is shown, {@code false} no message is shown.
    */
   public boolean isMessageShown() {
      return rootLayout != null && ObjectUtil.equals(rootLayout.topControl, messageLabel);
   }
   
   /**
    * Checks if the {@link IEditorPart} is shown.
    * @return {@code true} the {@link IEditorPart} is shown, {@code false} the {@link IEditorPart} is not shown.
    */
   public boolean isEditorShown() {
      return rootLayout != null && ObjectUtil.equals(rootLayout.topControl, editorComposite);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Request is delegated to the contained {@link IEditorPart}.
    * </p>
    */
   @Override
   public void doSave(IProgressMonitor monitor) {
      if (editorPart != null) {
         editorPart.doSave(monitor);
      }
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Request is delegated to the contained {@link IEditorPart}.
    * </p>
    */
   @Override
   public void doSaveAs() {
      if (editorPart != null) {
         editorPart.doSaveAs();
      }
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Request is delegated to the contained {@link IEditorPart}.
    * </p>
    */
   @Override
   public boolean isDirty() {
      return isEditorShown() && editorPart.isDirty();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Request is delegated to the contained {@link IEditorPart}.
    * </p>
    */
   @Override
   public boolean isSaveAsAllowed() {
      return isEditorShown() && editorPart.isSaveAsAllowed();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Request is delegated to the contained {@link IEditorPart}.
    * </p>
    */
   @Override
   public boolean isSaveOnCloseNeeded() {
      return isEditorShown() && editorPart.isSaveOnCloseNeeded();
   }
}