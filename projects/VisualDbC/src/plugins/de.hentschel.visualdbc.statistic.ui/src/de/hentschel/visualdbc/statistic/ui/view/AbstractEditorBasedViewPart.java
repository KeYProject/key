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

package de.hentschel.visualdbc.statistic.ui.view;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StackLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.part.ViewPart;

/**
 * <p>
 * Provides a basic implementation for {@link ViewPart}s that shows
 * content based on the active {@link IEditorPart}.
 * </p>
 * <p>
 * Subclasses have to implement {@link #createControlFor(IEditorPart, Composite)}
 * in that they have to create a {@link Control} that is shown
 * when the {@link IEditorPart} is active.
 * </p>
 * @author Martin Hentschel
 */
public abstract class AbstractEditorBasedViewPart extends ViewPart {
   /**
    * Shows the content for {@link IEditorPart}s.
    */
   private Composite containerComposite;
   
   /**
    * Layout of {@link #containerComposite}.
    */
   private StackLayout containerLayout;
   
   /**
    * {@link Label} to show error messages.
    */
   private Label errorLabel;
   
   /**
    * The currently shown {@link Control}.
    */
   private Control activeControl;
   
   /**
    * Maps the {@link IEditorPart} to the {@link Control} that provides the content.
    */
   private Map<IEditorPart, Control> editorControls = new HashMap<IEditorPart, Control>();
   
   /**
    * Listener for changes of {@link IWorkbenchPart}s.
    */
   private IPartListener partListener = new IPartListener() {
      @Override
      public void partOpened(IWorkbenchPart part) {
      }
      
      @Override
      public void partDeactivated(IWorkbenchPart part) {
      }
      
      @Override
      public void partClosed(IWorkbenchPart part) {
         handlePartClosed(part);
      }
      
      @Override
      public void partBroughtToTop(IWorkbenchPart part) {
      }
      
      @Override
      public void partActivated(IWorkbenchPart part) {
         handlePartActivated(part);
      }
   };
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createPartControl(Composite parent) {
      // Create container
      containerComposite = new Composite(parent, SWT.NONE);
      containerLayout = new StackLayout();
      containerComposite.setLayout(containerLayout);
      // Create error label
      errorLabel = new Label(containerComposite, SWT.NONE);
      // Add listener
      getViewSite().getPage().addPartListener(partListener);
      // Update shown content
      updateContent();
   }

   /**
    * Shows the content of the active {@link IEditorPart}.
    */
   protected void updateContent() {
      // Get content for active editor
      IEditorPart activeEditor = getActiveEditor();
      if (activeEditor != null) {
         Control control = getControlFor(activeEditor);
         if (control != null) {
            showControl(control);
         }
         else {
            errorLabel.setText(getContentNotAvailableMessage(activeEditor));
            showControl(errorLabel);
         }
      }
      else {
         errorLabel.setText(getContentNotAvailableMessage(null));
         showControl(errorLabel);
      }
   }
   
   /**
    * When an {@link IWorkbenchPart} was activated.
    * @param part The {@link IWorkbenchPart} to activate.
    */
   protected void handlePartActivated(IWorkbenchPart part) {
      if (part instanceof IEditorPart) {
         updateContent();
      }
   }
   
   /**
    * When an {@link IWorkbenchPart} was closed.
    * @param part The closed {@link IWorkbenchPart}.
    */
   protected void handlePartClosed(IWorkbenchPart part) {
      if (part instanceof IEditorPart) {
         Control control = editorControls.remove((IEditorPart)part);
         if (control != null) {
            control.dispose();
         }
         updateContent();
      }
   }

   /**
    * Returns the {@link Control} for the given {@link IEditorPart}.
    * @param activeEditor The active {@link IEditorPart}.
    * @return The {@link Control} for the {@link IEditorPart} or {@code null} if no one is available.
    */
   protected Control getControlFor(IEditorPart activeEditor) {
      Control result = editorControls.get(activeEditor);
      if (result == null) {
         result = createControlFor(activeEditor, containerComposite);
         if (result != null) {
            editorControls.put(activeEditor, result);
         }
      }
      return result;
   }

   /**
    * Creates the content {@link Control} for the given {@link IEditorPart}.
    * @param activeEditor The active {@link IEditorPart}.
    * @param parent The parent {@link Composite}.
    * @return The created {@link Control} or {@code null} if no content is available.
    */
   protected abstract Control createControlFor(IEditorPart activeEditor, Composite parent);

   /**
    * Shows the {@link Control}.
    * @param controlToShow The {@link Control} to show. 
    */
   protected void showControl(Control controlToShow) {
      activeControl = controlToShow;
      containerLayout.topControl = controlToShow;
      containerComposite.layout();
   }

   /**
    * Returns the error message that is shown if no content is available
    * for the given {@link IEditorPart}.
    * @param editor The active {@link IEditorPart}.
    * @return The error message to show.
    */
   protected String getContentNotAvailableMessage(IEditorPart editor) {
      return "No content available.";
   }
   
   /**
    * Returns the active {@link IEditorPart} if available.
    * @return The active {@link IEditorPart} or {@code null} if no one is available.
    */
   protected IEditorPart getActiveEditor() {
      return getViewSite().getPage().getActiveEditor();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setFocus() {
      if (activeControl != null) {
         activeControl.forceFocus();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      // Remove listener
      getViewSite().getPage().removePartListener(partListener);
      // Dispose available content
      for (Control control : editorControls.values()) {
         control.dispose();
      }
      editorControls.clear();
      // Dispose own controls
      errorLabel.dispose();
      containerComposite.dispose();
      // Dispose super class
      super.dispose();
   }

   /**
    * Returns the currently shown {@link Control}.
    * @return The currently shown {@link Control}.
    */
   public Control getActiveControl() {
      return activeControl;
   }
}