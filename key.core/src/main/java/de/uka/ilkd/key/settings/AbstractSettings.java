/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;

/**
 * @author Alexander Weigl
 * @version 1 (1/30/22)
 */
public abstract class AbstractSettings implements Settings {
    protected final PropertyChangeSupport changeSupport = new PropertyChangeSupport(this);

    @Override
    public void addPropertyChangeListener(PropertyChangeListener listener) {
        changeSupport.addPropertyChangeListener(listener);
    }

    @Override
    public void removePropertyChangeListener(PropertyChangeListener listener) {
        changeSupport.removePropertyChangeListener(listener);
    }

    @Override
    public PropertyChangeListener[] getPropertyChangeListeners() {
        return changeSupport.getPropertyChangeListeners();
    }

    @Override
    public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        changeSupport.addPropertyChangeListener(propertyName, listener);
    }

    @Override
    public void removePropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        changeSupport.removePropertyChangeListener(propertyName, listener);
    }


    protected PropertyChangeListener[] getPropertyChangeListeners(String propertyName) {
        return changeSupport.getPropertyChangeListeners(propertyName);
    }

    protected void firePropertyChange(String propertyName, Object oldValue, Object newValue) {
        changeSupport.firePropertyChange(propertyName, oldValue, newValue);
    }

    protected void firePropertyChange(String propertyName, int oldValue, int newValue) {
        changeSupport.firePropertyChange(propertyName, oldValue, newValue);
    }

    protected void firePropertyChange(String propertyName, boolean oldValue, boolean newValue) {
        changeSupport.firePropertyChange(propertyName, oldValue, newValue);
    }

    protected void firePropertyChange(PropertyChangeEvent event) {
        changeSupport.firePropertyChange(event);
    }

    protected void fireIndexedPropertyChange(String propertyName, int index, Object oldValue,
            Object newValue) {
        changeSupport.fireIndexedPropertyChange(propertyName, index, oldValue, newValue);
    }

    protected void fireIndexedPropertyChange(String propertyName, int index, int oldValue,
            int newValue) {
        changeSupport.fireIndexedPropertyChange(propertyName, index, oldValue, newValue);
    }

    protected void fireIndexedPropertyChange(String propertyName, int index, boolean oldValue,
            boolean newValue) {
        changeSupport.fireIndexedPropertyChange(propertyName, index, oldValue, newValue);
    }

    protected boolean hasListeners(String propertyName) {
        return changeSupport.hasListeners(propertyName);
    }
}
