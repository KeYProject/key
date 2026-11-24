/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.ui.util;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

class DefaultListModelTest {

    @Test
    void delegatesToListAndExposesBackingList() {
        var model = new DefaultListModel<String>();

        model.addElement("a");
        model.add(0, "b");

        assertThat(model.size()).isEqualTo(2);
        assertThat(model.get(1)).isEqualTo("a");
        assertThat(model.getElementAt(0)).isEqualTo("b");
        assertThat(model.getList()).containsExactly("b", "a");

        assertThat(model.removeElement("b")).isTrue();
        assertThat(model.remove(0)).isEqualTo("a");
        assertThat(model.isEmpty()).isTrue();
    }

    @Test
    void removesRangeAndClears() {
        var model = new DefaultListModel<Integer>();
        model.addAll(java.util.List.of(1, 2, 3, 4));

        model.removeRange(1, 3);
        assertThat(model.getList()).containsExactly(1, 4);

        model.clear();
        assertThat(model.isEmpty()).isTrue();
    }
}
