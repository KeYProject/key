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
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IMenuCreator;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.events.HelpListener;
import org.eclipse.swt.widgets.Event;
import org.key_project.util.Activator;
import org.key_project.util.eclipse.Logger;

/**
 * Wrapps existing {@link IAction} to add a global enabled state defined
 * via {@link IGlobalEnablement}.
 * @author Martin Hentschel
 * @see IGlobalEnablement
 */
//TODO: Implement tests
public class GlobalEnablementWrapperAction implements IAction, IGlobalEnablement {
   /**
    * The {@link IAction} to wrapp.
    */
   private IAction action;

   /**
    * The global enabled state.
    */
   private boolean globalEnabled;
   
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
    * Contained listeners.
    */
   private List<IPropertyChangeListener> listeners = new LinkedList<IPropertyChangeListener>();

   /**
    * Constructor.
    * @param action The {@link IAction} to wrapp.
    */
   public GlobalEnablementWrapperAction(IAction action) {
      super();
      Assert.isNotNull(action);
      this.action = action;
      action.addPropertyChangeListener(actionListener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      action.removePropertyChangeListener(actionListener);
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
   public void addPropertyChangeListener(IPropertyChangeListener listener) {
      if (listener != null) {
         listeners.add(listener);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removePropertyChangeListener(IPropertyChangeListener listener) {
      if (listener != null) {
         listeners.remove(listener);
      }
   }
   
   /**
    * Returns all available listeners.
    * @return The available listeners.
    */
   public IPropertyChangeListener[] getPropertyChangeListeners() {
      return listeners.toArray(new IPropertyChangeListener[listeners.size()]);
   }
   
   /**
    * Fires the event {@link IPropertyChangeListener#propertyChange(PropertyChangeEvent)}
    * to all available listeners.
    * @param event The event to fire.
    */
   protected void firePropertyChange(PropertyChangeEvent event) {
      IPropertyChangeListener[] listeners = getPropertyChangeListeners();
      for (IPropertyChangeListener listener : listeners) {
         listener.propertyChange(event);
      }
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
      try {
         return isGlobalEnabled() && action.isEnabled();
      }
      catch (Exception e) { // Sometimes org.eclipse.gef.editpolicies.NonResizableEditPolicy.getAlignCommand(NonResizableEditPolicy.java:236) throws a java.lang.NullPointerException for an unknown reason
         new Logger(Activator.getDefault(), Activator.PLUGIN_ID).logError("Exception during computation of enabled state in " + getClass() + ".", e);
         return false;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isHandled() {
      return action.isHandled();
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
   public void setActionDefinitionId(String id) {
      action.setActionDefinitionId(id);
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
      action.setEnabled(enabled);
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
   public void setHoverImageDescriptor(ImageDescriptor newImage) {
      action.setHoverImageDescriptor(newImage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setId(String id) {
      action.setId(id);
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
      action.setText(text);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setToolTipText(String text) {
      action.setToolTipText(text);
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
   public boolean isGlobalEnabled() {
      return globalEnabled;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setGlobalEnabled(boolean globalEnabled) {
      boolean oldEnabled = isEnabled();
      this.globalEnabled = globalEnabled;
      firePropertyChange(new PropertyChangeEvent(this, ENABLED, oldEnabled, isEnabled()));
   }
   
   /**
    * Returns the wrapped {@link IAction}.
    * @return The wrapped {@link IAction}.
    */
   public IAction getAction() {
      return action;
   }
}