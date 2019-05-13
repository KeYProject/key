// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

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

    private List<ObservableArrayListChangeListener> listeners = new ArrayList<>();

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
        listeners.stream().forEach(l -> l.changed());
    }

    @FunctionalInterface
    static interface ObservableArrayListChangeListener {
        void changed();
    }
}
