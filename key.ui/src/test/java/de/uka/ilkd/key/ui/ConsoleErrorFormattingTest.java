/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ui;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import de.uka.ilkd.key.util.parsing.BuildingExceptions;
import de.uka.ilkd.key.util.parsing.BuildingIssue;

import org.key_project.util.parsing.Position;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests that the console renders load errors with the concrete message, the source location and a
 * caret under the offending column - reusing the (GUI-independent) extraction in
 * {@code ExceptionTools#getMessages}.
 *
 * @author Claude (improveErrorMessages)
 */
public class ConsoleErrorFormattingTest {

    @Test
    public void formatsMessageLocationAndCaret() throws Exception {
        Path src = Files.createTempFile("consoleErr", ".key");
        Files.writeString(src, "line one\n   broken here\nline three\n");
        try {
            var issue = new BuildingIssue("something is wrong", null, false,
                Position.newOneBased(2, 4), src.toUri().toString());
            var ex = new RuntimeException("wrapper", new BuildingExceptions(List.of(issue)));

            String out = ConsoleUserInterfaceControl.formatLoadError(ex);

            assertTrue(out.contains("something is wrong"), out);
            assertTrue(out.contains(":2:4"), "should report line:column, but was:\n" + out);
            assertTrue(out.contains("   broken here"),
                "should show the source line, but was:\n" + out);
            // caret sits under column 4 (3 spaces of indent), i.e. on the 'b' of "broken"
            assertTrue(out.contains("\n       ^") || out.contains("    " + " ".repeat(3) + "^"),
                "should place a caret under the column, but was:\n" + out);
        } finally {
            Files.deleteIfExists(src);
        }
    }
}
