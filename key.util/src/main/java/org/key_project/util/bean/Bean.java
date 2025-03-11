/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.bean;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;

import org.key_project.util.java.ArrayUtil;

import org.jspecify.annotations.Nullable;

/**
 * Implements the basic methods that a Java bean should have and is the default implementation of
 * {@link IBean}.
 *
 * @author Martin Hentschel
 * @see IBean
 */
public class Bean implements IBean {
    /**
     * The used {@link PropertyChangeSupport}.
     */
    @SuppressWarnings("nullness") // TODO Check with Werner Dietl why this is so.
    private final PropertyChangeSupport pcs = new PropertyChangeSupport(this);

    /**
     * Returns the used {@link PropertyChangeSupport}.
     *
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
     *
     * @param propertyName The property name.
     * @param index The changed index.
     * @param oldValue The old value.
     * @param newValue The new value.
     */
    protected void fireIndexedPropertyChange(String propertyName, int index, boolean oldValue,
            boolean newValue) {
        pcs.fireIndexedPropertyChange(propertyName, index, oldValue, newValue);
    }

    /**
     * Fires the event to all available listeners.
     *
     * @param propertyName The property name.
     * @param index The changed index.
     * @param oldValue The old value.
     * @param newValue The new value.
     */
    protected void fireIndexedPropertyChange(String propertyName, int index, int oldValue,
            int newValue) {
        pcs.fireIndexedPropertyChange(propertyName, index, oldValue, newValue);
    }

    /**
     * Fires the event to all available listeners.
     *
     * @param propertyName The property name.
     * @param index The changed index.
     * @param oldValue The old value.
     * @param newValue The new value.
     */
    protected void fireIndexedPropertyChange(String propertyName, int index,
            @Nullable Object oldValue, @Nullable Object newValue) {
        pcs.fireIndexedPropertyChange(propertyName, index, oldValue, newValue);
    }

    /**
     * Fires the event to all listeners.
     *
     * @param evt The event to fire.
     */
    protected void firePropertyChange(PropertyChangeEvent evt) {
        pcs.firePropertyChange(evt);
    }

    /**
     * Fires the event to all listeners.
     *
     * @param propertyName The changed property.
     * @param oldValue The old value.
     * @param newValue The new value.
     */
    protected void firePropertyChange(String propertyName, boolean oldValue, boolean newValue) {
        pcs.firePropertyChange(propertyName, oldValue, newValue);
    }

    /**
     * Fires the event to all listeners.
     *
     * @param propertyName The changed property.
     * @param oldValue The old value.
     * @param newValue The new value.
     */
    protected void firePropertyChange(String propertyName, int oldValue, int newValue) {
        pcs.firePropertyChange(propertyName, oldValue, newValue);
    }

    /**
     * Fires the event to all listeners.
     *
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
