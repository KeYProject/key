package org.key_project.util.collection;

import org.jspecify.annotations.Nullable;

import java.util.Iterator;
import java.util.List;
import java.util.stream.Stream;

/**
 *
 * @author Alexander Weigl
 * @version 1 (4/19/26)
 */
public interface RoList<E extends @Nullable Object> extends Iterable<E> {
    int size();
    E get(int index);

    boolean isEmpty();
    default boolean isNonEmpty() {
        return !isEmpty();
    }

    boolean contains(Object e);
    Iterator<E> iterator();
    E getFirst();
    E getLast();

    Stream<E> stream();

    default List<E> toList() {
        return stream().toList();
    }
}
