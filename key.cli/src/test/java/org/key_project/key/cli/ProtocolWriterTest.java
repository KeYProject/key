/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli;

import java.io.ByteArrayOutputStream;
import java.nio.charset.StandardCharsets;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for {@link ProtocolWriter}: the protocol lines of the headless interface (§2, §6–§8) end
 * with a single {@code '\n'} on every platform, so Windows output is byte-identical to Unix output.
 */
class ProtocolWriterTest {

    private static String written(ByteArrayOutputStream bytes) {
        return bytes.toString(StandardCharsets.UTF_8);
    }

    @Test
    void terminatesLinesWithASingleLineFeed() {
        ByteArrayOutputStream bytes = new ByteArrayOutputStream();
        ProtocolWriter out = new ProtocolWriter(bytes);

        out.println("KEY_RESULT {}");
        out.println();
        out.println("GOAL 0 1");

        assertThat(written(bytes)).isEqualTo("KEY_RESULT {}\n\nGOAL 0 1\n");
        assertThat(written(bytes)).doesNotContain("\r");
    }

    @Test
    void flushesEveryLineWithoutAnExplicitFlushCall() {
        ByteArrayOutputStream bytes = new ByteArrayOutputStream();
        ProtocolWriter out = new ProtocolWriter(bytes);

        out.println("OPEN-GOAL-COUNT 1");

        assertThat(written(bytes)).isEqualTo("OPEN-GOAL-COUNT 1\n");
    }
}
