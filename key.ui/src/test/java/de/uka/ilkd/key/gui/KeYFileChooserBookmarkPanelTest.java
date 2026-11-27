/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui;

import java.io.File;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

class KeYFileChooserBookmarkPanelTest {

    @Test
    void normalizesCurrentDirectory() {
        File cwd = new File(System.getProperty("user.dir"));

        assertThat(KeYFileChooserBookmarkPanel.normalize(new File(".")))
                .isEqualTo(KeYFileChooserBookmarkPanel.normalize(cwd));
    }

    @Test
    void collapsesParentSegments() {
        assertThat(KeYFileChooserBookmarkPanel.normalize(new File("a/../b")))
                .isEqualTo(KeYFileChooserBookmarkPanel.normalize(new File("b")));
    }
}
