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

package org.key_project.util.bean;

import java.beans.PropertyChangeListener;

/**
 * <p>
 * Defines the methods that a Java bean must have.
 * </p>
 * <p>
 * Implementation of this interface should subclass from {@link Bean}
 * if possible.
 * </p>
 * @author Martin Hentschel
 * @see Bean
 */
public interface IBean {
    /**
     * Adds the given listener.
     * @param listener The listener to add.
     */
    public void addPropertyChangeListener(PropertyChangeListener listener);
    
    /**
     * Adds the given listener for the given property only.
     * @param propertyName The property to observe.
     * @param listener The listener to add.
     */
    public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener);
    
    /**
     * Removes the given listener.
     * @param listener The listener to remove.
     */
    public void removePropertyChangeListener(PropertyChangeListener listener);
    
    /**
     * Removes the given listener from the given property.
     * @param propertyName The property to no longer observe.
     * @param listener The listener to remove.
     */
    public void removePropertyChangeListener(String propertyName, PropertyChangeListener listener);
    
    /**
     * Returns all listeners.
     * @return The listeners.
     */
    public PropertyChangeListener[] getPropertyChangeListeners();
    
    /**
     * Returns all listeners of the given property.
     * @param propertyName The property.
     * @return The listeners of the given property.
     */
    public PropertyChangeListener[] getPropertyChangeListeners(String propertyName);
    
    /**
     * Checks if listeners are available.
     * @return {@code true} listeners available, {@code false} no listeners are available.
     */
    public boolean hasListeners();
    
    /**
     * Checks if listeners are available for the given property.
     * @param propertyName The property name.
     * @return {@code true} listeners available for the property, {@code false} no listeners are available for the property.
     */
    public boolean hasListeners(String propertyName);
    
    /**
     * Checks if the given listener is already available.
     * @param listener The listener to check.
     * @return {@code true} listener is available, {@code false} listener is not available.
     */
    public boolean hasListener(PropertyChangeListener listener);

    /**
     * Checks if the given listener is available for the given property.
     * @param propertyName The property.
     * @param listener The listener to check.
     * @return {@code true} listener is available for the property, {@code false} listener is not available for the property.
     */
    public boolean hasListener(String propertyName, PropertyChangeListener listener);
}