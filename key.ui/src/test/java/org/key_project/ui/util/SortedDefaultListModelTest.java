/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.ui.util;

import java.util.Comparator;
import java.util.List;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatThrownBy;

class SortedDefaultListModelTest {

    @Test
    void keepsElementsSorted() {
        var model = new SortedDefaultListModel<Integer>(Comparator.naturalOrder());

        model.addElement(3);
        model.addElement(1);
        model.addElement(2);

        assertThat(model.getList()).containsExactly(1, 2, 3);
    }

    @Test
    void replacesAndReinsertsAtSortedPosition() {
        var model = new SortedDefaultListModel<Integer>(Comparator.naturalOrder());
        model.addAll(List.of(1, 2, 3));

        assertThat(model.set(1, 10)).isEqualTo(2);
        assertThat(model.getList()).containsExactly(1, 3, 10);
    }

    @Test
    void rejectsPositionalInsertion() {
        var model = new SortedDefaultListModel<Integer>(Comparator.naturalOrder());

        assertThatThrownBy(() -> model.add(0, 1))
                .isInstanceOf(UnsupportedOperationException.class);
        assertThatThrownBy(() -> model.insertElementAt(1, 0))
                .isInstanceOf(UnsupportedOperationException.class);
    }
}
