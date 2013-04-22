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

package org.key_project.util.eclipse.swt;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IViewPart;
import org.key_project.util.bean.IBean;
import org.key_project.util.java.ArrayUtil;

/**
 * A {@link Composite} which is also an {@link IBean} and allows to
 * observe properties via {@link PropertyChangeListener} instances.
 * @author Martin Hentschel
 * @see IViewPart
 * @see IBean
 */
public class BeanComposite extends Composite implements IBean {
   /**
    * The used {@link PropertyChangeSupport}.
    */
   private PropertyChangeSupport pcs = new PropertyChangeSupport(this);
   
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style to use.
    */
   public BeanComposite(Composite parent, int style) {
      super(parent, style);
   }

   /**
    * Returns the used {@link PropertyChangeSupport}.
    * @return the used {@link PropertyChangeSupport}.
    */
   protected PropertyChangeSupport getPcs() {
       return pcs;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addPropertyChangeListener(PropertyChangeListener listener) {
       pcs.addPropertyChangeListener(listener);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
       pcs.addPropertyChangeListener(propertyName, listener);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void removePropertyChangeListener(PropertyChangeListener listener) {
       pcs.removePropertyChangeListener(listener);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void removePropertyChangeListener(String propertyName, PropertyChangeListener listener) {
       pcs.removePropertyChangeListener(propertyName, listener);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public PropertyChangeListener[] getPropertyChangeListeners() {
       return pcs.getPropertyChangeListeners();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public PropertyChangeListener[] getPropertyChangeListeners(String propertyName) {
       return pcs.getPropertyChangeListeners(propertyName);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasListeners() {
       return getPropertyChangeListeners().length >= 1;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasListeners(String propertyName) {
       return pcs.hasListeners(propertyName);
   }
   
   /**
    * Fires the event to all available listeners.
    * @param propertyName The property name.
    * @param index The changed index.
    * @param oldValue The old value.
    * @param newValue The new value.
    */
   protected void fireIndexedPropertyChange(String propertyName, int index, boolean oldValue, boolean newValue) {
       pcs.fireIndexedPropertyChange(propertyName, index, oldValue, newValue);
   }
   
   /**
    * Fires the event to all available listeners.
    * @param propertyName The property name.
    * @param index The changed index.
    * @param oldValue The old value.
    * @param newValue The new value.
    */
   protected void fireIndexedPropertyChange(String propertyName, int index, int oldValue, int newValue) {
       pcs.fireIndexedPropertyChange(propertyName, index, oldValue, newValue);
   }
   
   /**
    * Fires the event to all available listeners.
    * @param propertyName The property name.
    * @param index The changed index.
    * @param oldValue The old value.
    * @param newValue The new value.
    */    
   protected void fireIndexedPropertyChange(String propertyName, int index, Object oldValue, Object newValue) {
       pcs.fireIndexedPropertyChange(propertyName, index, oldValue, newValue);
   }
   
   /**
    * Fires the event to all listeners.
    * @param evt The event to fire.
    */
   protected void firePropertyChange(PropertyChangeEvent evt) {
       pcs.firePropertyChange(evt);
   }
   
   /**
    * Fires the event to all listeners.
    * @param propertyName The changed property.
    * @param oldValue The old value.
    * @param newValue The new value.
    */
   protected void firePropertyChange(String propertyName, boolean oldValue, boolean newValue) {
       pcs.firePropertyChange(propertyName, oldValue, newValue);
   }
   
   /**
    * Fires the event to all listeners.
    * @param propertyName The changed property.
    * @param oldValue The old value.
    * @param newValue The new value.
    */
   protected void firePropertyChange(String propertyName, int oldValue, int newValue) {
       pcs.firePropertyChange(propertyName, oldValue, newValue);
   }
   
   /**
    * Fires the event to all listeners.
    * @param propertyName The changed property.
    * @param oldValue The old value.
    * @param newValue The new value.
    */
   protected void firePropertyChange(String propertyName, Object oldValue, Object newValue) {
       pcs.firePropertyChange(propertyName, oldValue, newValue);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasListener(PropertyChangeListener listener) {
       return ArrayUtil.contains(getPropertyChangeListeners(), listener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasListener(String propertyName, PropertyChangeListener listener) {
       return ArrayUtil.contains(getPropertyChangeListeners(propertyName), listener);
   }
}