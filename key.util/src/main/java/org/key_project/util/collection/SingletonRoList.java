/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.stream.Stream;

/**
 *
 * @author Alexander Weigl
 * @version 1 (4/19/26)
 */
public record SingletonRoList<T>(T item) implements RoList<T> {
    @Override
    public int size() {
        return 1;
    }

    @Override
    public T get(int index) {
        if (index == 0) {
            return item();
        }
        throw new IndexOutOfBoundsException();
    }

    @Override
    public boolean isEmpty() {
        return false;
    }

    @Override
    public boolean contains(Object e) {
        return Objects.equals(e, item);
    }

    @Override
    public Iterator<T> iterator() {
        return new Iterator<>() {
            private boolean called;

            @Override
            public boolean hasNext() {
                return !called;
            }

            @Override
            public T next() {
                if (called) {
                    throw new NoSuchElementException();
                }
                called = true;
                return item;
            }
        };
    }

    @Override
    public T getFirst() {
        return item;
    }

    @Override
    public T getLast() {
        return item;
    }

    @Override
    public Stream<T> stream() {
        return Stream.of(item);
    }
}
