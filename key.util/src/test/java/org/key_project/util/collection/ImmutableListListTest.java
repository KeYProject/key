/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.Collections;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.stream.IntStream;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;
import static org.key_project.util.collection.ImmutableListArrayTest.create;

/**
 *
 * @author Alexander Weigl
 * @version 1 (16.05.26)
 */
class ImmutableListListTest {
    private final ImmutableListList<Integer> list123 = new ImmutableListList<>(createList(3));
    private final ImmutableListList<Integer> listEmpty =
        new ImmutableListList<>(Collections.emptyList());
    private final ImmutableListList<Integer> listVeryLong =
        new ImmutableListList<>(createList(1024));
    private final ImmutableListList<Integer> list10 = new ImmutableListList<>(createList(10));

    public static List<Integer> createList(int i) {
        return IntStream.range(1, i + 1).boxed().toList();
    }

    @Test
    void content() {
        assertThat(list123).containsExactly(1, 2, 3);
        assertThat(list10).containsExactly(1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
    }

    @Test
    void size() {
        assertThat(list123.size()).isEqualTo(3);
        assertThat(listEmpty.size()).isEqualTo(0);
        assertThat(listVeryLong.size()).isEqualTo(1024);
        assertThat(list10.size()).isEqualTo(10);
    }

    @Test
    void head() {
        assertThat(list123.head()).isEqualTo(1);
        assertThat(listVeryLong.head()).isEqualTo(1);
        assertThat(list10.head()).isEqualTo(1);

        Assertions.assertThrows(NoSuchElementException.class,
            () -> assertThat(listEmpty.head()).isEqualTo(-1));
    }


    @Test
    void last() {
        assertThat(list123.last()).isEqualTo(3);
        assertThat(listVeryLong.last()).isEqualTo(1024);
        assertThat(list10.last()).isEqualTo(10);

        Assertions.assertThrows(NoSuchElementException.class,
            () -> assertThat(listEmpty.last()).isEqualTo(-1));
    }


    @Test
    void exists() {
        assertThat(list123.exists(a -> a == -1)).isEqualTo(false);
        assertThat(listVeryLong.exists(a -> a == -1)).isEqualTo(false);
        assertThat(list10.exists(a -> a == -1)).isEqualTo(false);

        assertThat(listEmpty.exists(a -> true)).isEqualTo(false);

        assertThat(list123.exists(a -> a == 1)).isEqualTo(true);
        assertThat(listVeryLong.exists(a -> a == 1023)).isEqualTo(true);
        assertThat(list10.exists(a -> a == 5)).isEqualTo(true);
    }


    @Test
    void toArray() {
        Integer[] array = list123.toArray(new Integer[0]);
        Integer[] array2 = create(3);

        assertThat(array).isEqualTo(array2);

        assertThat(listVeryLong.toArray(new Integer[0]))
                .isEqualTo(create(1024));

        assertThat(list10.toArray(new Integer[0]))
                .isEqualTo(create(10));

        assertThat(listEmpty.toArray(new Integer[0]))
                .isEqualTo(new Integer[0]);

        assertThat(list123.toArray(Integer.class))
                .isEqualTo(create(3));

        assertThat(listVeryLong.toArray(Integer.class))
                .isEqualTo(create(1024));

        assertThat(list10.toArray(Integer.class))
                .isEqualTo(create(10));

        assertThat(list10.toArray(new Integer[10]))
                .isEqualTo(create(10));

        assertThat(listEmpty.toArray(Integer.class))
                .isEqualTo(new Integer[0]);
    }

    @Test
    void stream() {
        assertThat(listEmpty.stream().toList()).isEmpty();

        assertThat(list123.stream().toList())
                .isNotEmpty()
                .containsExactly(create(3));

        assertThat(listVeryLong.stream().toList())
                .isNotEmpty()
                .containsExactly(create(1024));

        assertThat(list10.stream().toList())
                .isNotEmpty()
                .containsExactly(create(10));
    }


    @Test
    void isEmpty() {
        assertThat(listEmpty.isEmpty()).isTrue();
        assertThat(list123.isEmpty()).isFalse();
        assertThat(listVeryLong.isEmpty()).isFalse();
        assertThat(list10.isEmpty()).isFalse();
    }

    @Test
    void removeFirst() {
        removeFirst(listEmpty);
        removeFirst(list123);
        removeFirst(list10);
        removeFirst(listVeryLong);

        assertThat(listEmpty.removeFirst(0))
                .isEqualTo(listEmpty);

        assertThat(list123.removeFirst(1))
                .containsExactly(2, 3);

        assertThat(list123.removeFirst(1).removeFirst(3))
                .containsExactly(2);

        assertThat(list123.removeFirst(1).removeFirst(3).removeFirst(2))
                .isEmpty();
    }

    void removeFirst(ImmutableList<Integer> seq) {
        while (!seq.isEmpty()) {
            int pivot = seq.get(seq.size() / 2);
            seq = seq.removeFirst(pivot);
            assertThat(seq).doesNotContain(pivot);
        }
    }

    @Test
    void removeAll() {
        removeAll(listEmpty);
        removeAll(listVeryLong);
        removeAll(list123);
        removeAll(list10);

        assertThat(listEmpty.removeFirst(0))
                .isEqualTo(listEmpty);


        assertThat(
            new ImmutableListArray<>(
                new Integer[] { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 })
                    .removeAll(0))
                .isEqualTo(listEmpty)
                .isEmpty();
    }

    void removeAll(ImmutableList<Integer> seq) {
        while (!seq.isEmpty()) {
            int pivot = seq.get(seq.size() / 2);
            seq = seq.removeAll(pivot);
            assertThat(seq).doesNotContain(pivot);
        }
    }


    @Test
    void testToArray() {
    }

    @Test
    void iterator() {
        assertThat(listEmpty).doesNotContain(0);

        assertThat(list123)
                .isNotEmpty()
                .containsExactly(create(3));

        assertThat(listVeryLong)
                .isNotEmpty()
                .containsExactly(create(1024));

        assertThat(list10)
                .isNotEmpty()
                .containsExactly(create(10));
    }

    @Test
    void filter() {
        assertThat(listEmpty.filter((a) -> true)).isEmpty();
        assertThat(listEmpty.filter((a) -> false)).isEmpty();


        assertThat(list10.filter((a) -> false)).isEmpty();
        assertThat(list10.filter((a) -> true))
                .isEqualTo(list10);
    }

    @Test
    void map() {
        assertThat(list123.map((a) -> a + 1))
                .containsExactly(2, 3, 4);

        assertThat(listEmpty.map((a) -> a + 1))
                .isEmpty();
    }

    @Test
    void get() {
        for (int i = 0; i < list10.size(); i++) {
            assertThat(list10.get(i)).isEqualTo(i + 1);
        }

        Assertions.assertThrows(IndexOutOfBoundsException.class, () -> list10.get(list10.size()));

        Assertions.assertThrows(IndexOutOfBoundsException.class, () -> list10.get(-1));

        Assertions.assertThrows(IndexOutOfBoundsException.class, () -> listEmpty.get(0));
    }
}
