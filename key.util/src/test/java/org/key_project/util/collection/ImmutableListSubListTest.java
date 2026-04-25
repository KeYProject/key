/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.List;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 *
 * @author Alexander Weigl
 * @version 1 (16.05.26)
 */
class ImmutableListSubListTest {
    private final ImmutableList<Integer> seq =
        new ImmutableListArray<>(ImmutableListArrayTest.create(5));
    private final ImmutableListConcat<Integer> data = new ImmutableListConcat<>(
        seq,
        new ImmutableListList<>(ImmutableListListTest.createList(5)));
    private final ImmutableListConcat<Integer> listEmpty = new ImmutableListConcat<>(
        new ImmutableListArray<>(new Integer[0]), new ImmutableListList<>(List.of()));

    @Test
    void test() {
        assertThat(data.take(1)).containsExactly(1);
        assertThat(data.take(0)).isEqualTo(listEmpty);

        assertThat(data.take(5))
                .hasSize(5)
                .containsExactly(1, 2, 3, 4, 5)
                .isEqualTo(seq);

        assertThat(data.skip(5))
                .hasSize(5)
                .containsExactly(1, 2, 3, 4, 5)
                .isEqualTo(seq);
    }
}
