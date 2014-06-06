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

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IMenuCreator;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.events.HelpListener;
import org.eclipse.swt.widgets.Event;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.actions.RetargetAction;
import org.key_project.util.java.ObjectUtil;

/**
 * This special {@link RetargetAction} disables the retarget functionality
 * of the contained and wrapped child {@link RetargetAction}. Instead of
 * the real active part believes the wrapped {@link RetargetAction} that
 * always the given fixed {@link IWorkbenchPart} is active.
 * @author Martin Hentschel
 */
//TODO: Implement tests
public class NoRetargetWrapperRetargetAction extends RetargetAction {
   /**
    * The {@link RetargetAction} to wrapp and to disable the retarget functionality.
    */
   private RetargetAction action = null;

   /**
    * The fixed {@link IWorkbenchPart} which is seen as active part in the wrapped {@link RetargetAction}.
    */
   private IWorkbenchPart fixedPart;
      
   /**
    * Listens for changes on {@link #action}.
    */
   private IPropertyChangeListener actionListener = new IPropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent event) {
         handleActionPropertyChange(event);
      }
   };
   
   /**
    * Constructor.
    * @param action The {@link RetargetAction} to wrapp and to disable the retarget functionality.
    * @param fixedPart The fixed {@link IWorkbenchPart} which is seen as active part in the wrapped {@link RetargetAction}.
    */
   public NoRetargetWrapperRetargetAction(RetargetAction action, IWorkbenchPart fixedPart) {
      super(action.getId(), action.getText(), action.getStyle());
      this.action = action;
      this.action.addPropertyChangeListener(actionListener);
      this.fixedPart = fixedPart;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      action.removePropertyChangeListener(actionListener);
      action.dispose();
      super.dispose();
   }

   /**
    * When a property of the wrapped {@link IAction} has changed,
    * an equal event is thrown for this {@link IAction}.
    * @param event The event to handle.
    */
   protected void handleActionPropertyChange(PropertyChangeEvent event) {
      firePropertyChange(new PropertyChangeEvent(this, event.getProperty(), event.getOldValue(), event.getNewValue()));
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void partActivated(IWorkbenchPart part) {
      action.partActivated(fixedPart);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void partClosed(IWorkbenchPart part) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void partDeactivated(IWorkbenchPart part) {
      if (ObjectUtil.equals(fixedPart, part)) {
         action.partActivated(fixedPart);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void enableAccelerator(boolean b) {
      action.enableAccelerator(b);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getAccelerator() {
      return action.getAccelerator();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void run() {
      action.run();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void runWithEvent(Event event) {
      action.runWithEvent(event);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IAction getActionHandler() {
      return action.getActionHandler();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setChecked(boolean checked) {
      action.setChecked(checked);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setHelpListener(HelpListener listener) {
      action.setHelpListener(listener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IWorkbenchPart getActivePart() {
      return action.getActivePart();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void partBroughtToTop(IWorkbenchPart part) {
      action.partBroughtToTop(part);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void partOpened(IWorkbenchPart part) {
      action.partOpened(part);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getActionDefinitionId() {
      return action.getActionDefinitionId();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getDescription() {
      return action.getDescription();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImageDescriptor getDisabledImageDescriptor() {
      return action.getDisabledImageDescriptor();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public HelpListener getHelpListener() {
      return action.getHelpListener();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImageDescriptor getHoverImageDescriptor() {
      return action.getHoverImageDescriptor();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getId() {
      return action.getId();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImageDescriptor getImageDescriptor() {
      return action.getImageDescriptor();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IMenuCreator getMenuCreator() {
      return action.getMenuCreator();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getStyle() {
      return action.getStyle();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getText() {
      return action.getText();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getToolTipText() {
      return action.getToolTipText();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isChecked() {
      return action.isChecked();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isEnabled() {
      return action.isEnabled();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setAccelerator(int keycode) {
      action.setAccelerator(keycode);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setActionDefinitionId(String id) {
      action.setActionDefinitionId(id);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setDescription(String text) {
      action.setDescription(text);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setDisabledImageDescriptor(ImageDescriptor newImage) {
      action.setDisabledImageDescriptor(newImage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setEnabled(boolean enabled) {
      if (action != null) {
         action.setEnabled(enabled);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setHoverImageDescriptor(ImageDescriptor newImage) {
      action.setHoverImageDescriptor(newImage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setId(String id) {
      super.setId(id);
      if (action != null) {
         action.setId(id);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setImageDescriptor(ImageDescriptor newImage) {
      action.setImageDescriptor(newImage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setMenuCreator(IMenuCreator creator) {
      action.setMenuCreator(creator);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setText(String text) {
      super.setText(text);
      if (action != null) {
         action.setText(text);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setToolTipText(String toolTipText) {
      action.setToolTipText(toolTipText);
   }
}