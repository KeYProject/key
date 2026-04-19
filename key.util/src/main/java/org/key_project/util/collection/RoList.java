package org.key_project.util.collection;

import org.jspecify.annotations.Nullable;

import java.util.*;
import java.util.function.BiConsumer;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collector;
import java.util.stream.Stream;

/**
 *
 * @author Alexander Weigl
 * @version 1 (4/19/26)
 */
public interface RoList<E extends @Nullable Object> extends Iterable<E> {
    RoList<?> EMPTY = new RoList<>() {
        @Override
        public int size() {
            return 0;
        }

        @Override
        public Object get(int index) {
            throw new IndexOutOfBoundsException();
        }

        @Override
        public boolean isEmpty() {
            return true;
        }

        @Override
        public boolean contains(Object e) {
            return false;
        }

        @Override
        public Iterator<Object> iterator() {
            return new Iterator<>() {
                @Override
                public boolean hasNext() {
                    return false;
                }

                @Override
                public Object next() {
                    throw new NoSuchElementException();
                }
            };
        }

        @Override
        public Object getFirst() {
            throw new NoSuchElementException();
        }

        @Override
        public Object getLast() {
            throw new NoSuchElementException();
        }

        @Override
        public Stream<Object> stream() {
            return Stream.empty();
        }
    };

    static <T> Collector<? super T, List<T>, RoList<T>> collector() {
        return new Collector<>() {
            @Override
            public Supplier<List<T>> supplier() {
                return ArrayList::new;
            }

            @Override
            public BiConsumer<List<T>, T> accumulator() {
                return List::add;
            }

            @Override
            public BinaryOperator<List<T>> combiner() {
                return (a, b) -> {
                    a.addAll(b);
                    return a;
                };
            }

            @Override
            public Function<List<T>, RoList<T>> finisher() {
                return (a) -> RoList.fromList(a);
            }

            @Override
            public Set<Characteristics> characteristics() {
                return Set.of();
            }
        };
    }

    static <T> RoList<T> fromList(List<T> a) {
        if(a.isEmpty()) {
            return RoList.empty();
        }else if(a.size()==1){
            return RoList.singleton(a.getFirst());
        }else{
            return new ImmutableArray<>(a);
        }
    }

    static <T> RoList<T> singleton(T item) {
        return new SingletonRoList<>(item);
    }

    static <T> RoList<T> empty() {
        return (RoList<T>) EMPTY;
    }

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
