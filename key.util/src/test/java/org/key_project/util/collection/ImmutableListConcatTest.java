/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.List;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 *
 * @author Alexander Weigl
 * @version 1 (16.05.26)
 */
class ImmutableListConcatTest {
    private final ImmutableListConcat<Integer> data = new ImmutableListConcat<>(
        new ImmutableListArray<>(ImmutableListArrayTest.create(5)),
        new ImmutableListList<>(ImmutableListListTest.createList(5)));
    private final ImmutableListConcat<Integer> listEmpty = new ImmutableListConcat<>(
        new ImmutableListArray<>(new Integer[0]), new ImmutableListList<>(List.of()));
    private final ImmutableListConcat<Integer> listEmptyEmpty = new ImmutableListConcat<>(
        listEmpty, listEmpty);
    private final ImmutableList list123 = new ImmutableListList<Integer>(List.of(1, 2, 3));
    private final ImmutableListConcat<Integer> listFirstEmpty123 =
        new ImmutableListConcat<>(listEmptyEmpty, list123);


    @Test
    void get() {
        assertThat(list123.get(0)).isEqualTo(1);
        assertThat(list123.get(1)).isEqualTo(2);
        assertThat(list123.get(2)).isEqualTo(3);

        Assertions.assertThrows(IndexOutOfBoundsException.class,
            () -> listEmpty.get(0));

        Assertions.assertThrows(IndexOutOfBoundsException.class,
            () -> listEmptyEmpty.get(0));

        Assertions.assertThrows(IndexOutOfBoundsException.class,
            () -> list123.get(4));
    }

    @Test
    void exists() {
        assertThat(data.exists((i) -> i == 1)).isTrue();
        assertThat(data.exists((i) -> i == 5)).isTrue();
        assertThat(data.exists((i) -> i == 10)).isFalse();
        assertThat(data.exists((i) -> i == 0)).isFalse();

        assertThat(listEmpty.exists((i) -> true)).isFalse();
        assertThat(listEmptyEmpty.exists((i) -> true)).isFalse();
    }

    @Test
    void testEquals() {
        assertThat(listEmptyEmpty).isEqualTo(listEmpty);
        assertThat(listFirstEmpty123).isEqualTo(list123);
        assertThat(list123).isEqualTo(listFirstEmpty123);
    }

    @Test
    void size() {
        assertThat(data.size()).isEqualTo(10);
        assertThat(listEmpty.size()).isEqualTo(0);
        assertThat(listEmptyEmpty.size()).isEqualTo(0);
    }

    @Test
    void isEmpty() {
        assertThat(data.isEmpty()).isFalse();
        assertThat(listEmpty.isEmpty()).isTrue();
        assertThat(listEmptyEmpty.isEmpty()).isTrue();
    }

    @Test
    void removeFirst() {
        System.out.println(data);
        assertThat(data)
                .containsExactly(1, 2, 3, 4, 5, 1, 2, 3, 4, 5);

        assertThat(data.removeFirst(1))
                .containsExactly(2, 3, 4, 5, 1, 2, 3, 4, 5);

        assertThat(data.removeFirst(1).removeFirst(1))
                .containsExactly(2, 3, 4, 5, 2, 3, 4, 5);

        assertThat(listFirstEmpty123.removeFirst(1))
                .containsExactly(2, 3);

        assertThat(listFirstEmpty123.removeFirst(1).removeFirst(3))
                .containsExactly(2);


        assertThat(listEmpty.removeFirst(0)).isEqualTo(listEmpty);
        assertThat(listEmptyEmpty.removeFirst(0)).isEqualTo(listEmpty);
    }

    @Test
    void removeAll() {
        assertThat(data.removeAll(1))
                .containsExactly(2, 3, 4, 5, 2, 3, 4, 5);

    }

    @Test
    void iterator() {
    }
}
