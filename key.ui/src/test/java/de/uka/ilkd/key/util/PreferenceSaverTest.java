/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.util;

import java.awt.Rectangle;
import java.util.List;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests which stored window bounds {@link PreferenceSaver} accepts. Windows reports a minimized
 * window at (-32000, -32000), and such bounds made the main window unreachable after a restart.
 */
class PreferenceSaverTest {
    private static final Rectangle SCREEN = new Rectangle(0, 0, 1920, 1080);
    private static final Rectangle SECOND_SCREEN = new Rectangle(1920, 0, 1920, 1080);

    @Test
    void windowOnScreenIsReachable() {
        assertThat(PreferenceSaver.isReachable(new Rectangle(100, 100, 1200, 800),
            List.of(SCREEN))).isTrue();
    }

    @Test
    void maximizedWindowOnWindowsIsReachable() {
        assertThat(PreferenceSaver.isReachable(new Rectangle(-8, -8, 1936, 1096),
            List.of(SCREEN))).isTrue();
    }

    @Test
    void minimizedWindowOnWindowsIsNotReachable() {
        assertThat(PreferenceSaver.isReachable(new Rectangle(-32000, -32000, 160, 28),
            List.of(SCREEN))).isFalse();
    }

    @Test
    void windowOnRemovedScreenIsNotReachable() {
        Rectangle bounds = new Rectangle(2500, 100, 1200, 800);
        assertThat(PreferenceSaver.isReachable(bounds, List.of(SCREEN, SECOND_SCREEN))).isTrue();
        assertThat(PreferenceSaver.isReachable(bounds, List.of(SCREEN))).isFalse();
    }

    @Test
    void windowWithTitleBarAboveScreenIsNotReachable() {
        assertThat(PreferenceSaver.isReachable(new Rectangle(100, -500, 1200, 800),
            List.of(SCREEN))).isFalse();
    }

    @Test
    void tinyWindowIsNotReachable() {
        assertThat(PreferenceSaver.isReachable(new Rectangle(100, 100, 0, 0), List.of(SCREEN)))
                .isFalse();
        assertThat(PreferenceSaver.isReachable(new Rectangle(100, 100, 0, 0), List.of()))
                .isFalse();
    }

    @Test
    void withoutScreenInformationOnlyTheSizeIsChecked() {
        assertThat(PreferenceSaver.isReachable(new Rectangle(-32000, -32000, 1200, 800),
            List.of())).isTrue();
    }
}
