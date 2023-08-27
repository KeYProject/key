/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.mergerule.predicateabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * An observable {@link ArrayList}; poor reimplementation of the JavaFX class.
 *
 * @author Dominic Steinhoefel
 */
public class ObservableArrayList<E> extends ArrayList<E> {
    private static final long serialVersionUID = 1L;

    private final List<ObservableArrayListChangeListener> listeners = new ArrayList<>();

    public void addListener(ObservableArrayListChangeListener listener) {
        listeners.add(listener);
    }

    public void removeListener(ObservableArrayListChangeListener listener) {
        listeners.remove(listener);
    }

    @Override
    public void clear() {
        super.clear();
        informListeners();
    }

    @Override
    public E set(int index, E element) {
        E result = super.set(index, element);
        informListeners();
        return result;
    }

    @Override
    public boolean add(E e) {
        boolean result = super.add(e);
        informListeners();
        return result;
    }

    @Override
    public boolean addAll(Collection<? extends E> c) {
        boolean result = super.addAll(c);
        informListeners();
        return result;
    }

    @Override
    public void add(int index, E element) {
        super.add(index, element);
        informListeners();
    }

    @Override
    public boolean addAll(int index, Collection<? extends E> c) {
        boolean result = super.addAll(index, c);
        informListeners();
        return result;
    }

    @Override
    public E remove(int index) {
        E result = super.remove(index);
        informListeners();
        return result;
    }

    @Override
    public boolean remove(Object o) {
        boolean result = super.remove(o);
        informListeners();
        return result;
    }

    @Override
    public boolean removeAll(Collection<?> c) {
        boolean result = super.removeAll(c);
        informListeners();
        return result;
    }

    @Override
    protected void removeRange(int fromIndex, int toIndex) {
        super.removeRange(fromIndex, toIndex);
        informListeners();
    }

    private void informListeners() {
        listeners.forEach(ObservableArrayListChangeListener::changed);
    }

    @FunctionalInterface
    interface ObservableArrayListChangeListener {
        void changed();
    }
}
