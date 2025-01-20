/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.api;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (21.04.17)
 */
public class ScriptResults implements List<ScriptResult> {
    private final List<ScriptResult> delegated = new ArrayList<>();

    @Override
    public int size() {
        return delegated.size();
    }

    @Override
    public boolean isEmpty() {
        return delegated.isEmpty();
    }

    @Override
    public boolean contains(Object o) {
        return delegated.contains(o);
    }

    @Override
    public Iterator<ScriptResult> iterator() {
        return delegated.iterator();
    }

    @Override
    public Object[] toArray() {
        return delegated.toArray();
    }

    @Override
    public <T> T[] toArray(T[] a) {
        return delegated.toArray(a);
    }

    @Override
    public boolean add(ScriptResult scriptResult) {
        return delegated.add(scriptResult);
    }

    @Override
    public boolean remove(Object o) {
        return delegated.remove(o);
    }

    @Override
    public boolean containsAll(Collection<?> c) {
        return delegated.containsAll(c);
    }

    @Override
    public boolean addAll(Collection<? extends ScriptResult> c) {
        return delegated.addAll(c);
    }

    @Override
    public boolean addAll(int index, Collection<? extends ScriptResult> c) {
        return delegated.addAll(index, c);
    }

    @Override
    public boolean removeAll(Collection<?> c) {
        return delegated.removeAll(c);
    }

    @Override
    public boolean retainAll(Collection<?> c) {
        return delegated.retainAll(c);
    }

    @Override
    public void replaceAll(UnaryOperator<ScriptResult> operator) {
        delegated.replaceAll(operator);
    }

    @Override
    public void sort(Comparator<? super ScriptResult> c) {
        delegated.sort(c);
    }

    @Override
    public void clear() {
        delegated.clear();
    }

    @Override
    public boolean equals(Object o) {
        return delegated.equals(o);
    }

    @Override
    public int hashCode() {
        return delegated.hashCode();
    }

    @Override
    public ScriptResult get(int index) {
        return delegated.get(index);
    }

    @Override
    public ScriptResult set(int index, ScriptResult element) {
        return delegated.set(index, element);
    }

    @Override
    public void add(int index, ScriptResult element) {
        delegated.add(index, element);
    }

    @Override
    public ScriptResult remove(int index) {
        return delegated.remove(index);
    }

    @Override
    public int indexOf(Object o) {
        return delegated.indexOf(o);
    }

    @Override
    public int lastIndexOf(Object o) {
        return delegated.lastIndexOf(o);
    }

    @Override
    public ListIterator<ScriptResult> listIterator() {
        return delegated.listIterator();
    }

    @Override
    public ListIterator<ScriptResult> listIterator(int index) {
        return delegated.listIterator(index);
    }

    @Override
    public List<ScriptResult> subList(int fromIndex, int toIndex) {
        return delegated.subList(fromIndex, toIndex);
    }

    @Override
    public Spliterator<ScriptResult> spliterator() {
        return delegated.spliterator();
    }

    @Override
    public boolean removeIf(Predicate<? super ScriptResult> filter) {
        return delegated.removeIf(filter);
    }

    @Override
    public Stream<ScriptResult> stream() {
        return delegated.stream();
    }

    @Override
    public Stream<ScriptResult> parallelStream() {
        return delegated.parallelStream();
    }

    @Override
    public void forEach(Consumer<? super ScriptResult> action) {
        delegated.forEach(action);
    }
}
