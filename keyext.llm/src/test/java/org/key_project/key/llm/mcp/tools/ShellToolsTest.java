/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.io.ByteArrayInputStream;
import java.nio.charset.StandardCharsets;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Headless tests of the {@link ShellTools} helpers: the bounded output read. No process is
 * started.
 *
 * @author Alexander Weigl
 */
class ShellToolsTest {

    @Test
    void readBoundedCapsTheOutputAtTheCharLimit() throws Exception {
        var big = "x".repeat(100_000);
        var result = ShellTools.readBounded(
            new ByteArrayInputStream(big.getBytes(StandardCharsets.UTF_8)), 65536);
        var marker = "\n... [output truncated at 65536 characters]";
        assertTrue(result.endsWith(marker), result);
        assertEquals(65536, result.indexOf(marker),
            "the prefix must hold exactly the capped number of characters");

        // a text of exactly the cap length is not truncated
        var exact = "y".repeat(65536);
        assertEquals(exact, ShellTools.readBounded(
            new ByteArrayInputStream(exact.getBytes(StandardCharsets.UTF_8)), 65536));

        assertEquals("hi", ShellTools.readBounded(
            new ByteArrayInputStream("hi".getBytes(StandardCharsets.UTF_8)), 65536));
    }

    @Test
    void readBoundedKeepsMultiByteCharactersIntact() throws Exception {
        // the cap cuts between characters, never inside a multi-byte character
        var text = "äöü".repeat(1000); // 3000 chars, 6000 bytes in UTF-8
        var result = ShellTools.readBounded(
            new ByteArrayInputStream(text.getBytes(StandardCharsets.UTF_8)), 2999);
        assertTrue(result.startsWith(text.substring(0, 2999)), result);
        assertEquals(2999, result.indexOf("\n... [output truncated at 2999 characters]"),
            result);
    }
}
