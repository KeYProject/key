/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.*;

/**
 *
 * @author Alexander Weigl
 * @version 1 (16.05.26)
 */
class ImmutableListReverseTest {
    private final ImmutableList<Integer> seq =
        new ImmutableListArray<>(ImmutableListArrayTest.create(5));

    @Test
    void reverse() {
        assertThat(seq).containsExactly(1, 2, 3, 4, 5);
        assertThat(seq.reverse())
                .hasSize(5)
                .containsExactly(5, 4, 3, 2, 1);

        assertThat(seq.reverse().reverse())
                .hasSize(5)
                .containsExactly(1, 2, 3, 4, 5);


        assertThat(seq.prepend().reverse().prepend())
                .hasSize(5)
                .containsExactly(5, 4, 3, 2, 1);

        assertThat(seq.reverse().take(3).reverse())
                .hasSize(3)
                .isEqualTo(seq.skip(2));
    }
}
