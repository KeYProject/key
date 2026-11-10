/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import org.key_project.key.llm.LlmSettings;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.Tool;
import org.key_project.key.llm.mcp.ToolCategory;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The {@code edit} tool: exact search/replace on text files of the Java model directory,
 * requiring user approval. The core {@link FileTools#applyEdit} semantics are tested headless on
 * a temporary file; the tool body itself resolves the model directory via the selected proof and
 * is thus only testable inside the running GUI.
 */
class FileToolsEditTest {

    // ------------------------------------------------------------------------ metadata

    @Test
    void editFileToolMetadata() {
        var tools = new KeYAgentTools();
        var tool = tools.agent(KeYAgentTools.TOOL_EDIT);
        assertNotNull(tool, "edit must be registered");
        assertEquals(ToolCategory.FILES, tool.category());
        // modifying files must require user approval, like shell
        assertEquals(Tool.ApprovalRequirement.ASK, tool.approval());
        assertFalse(tool.backgroundable());
        var parameters = tool.parameters();
        assertNotNull(parameters.properties().get("path"));
        assertNotNull(parameters.properties().get("oldString"));
        assertNotNull(parameters.properties().get("newString"));
        assertNotNull(parameters.properties().get("replaceAll"));
        assertTrue(parameters.required().contains("path"));
        assertTrue(parameters.required().contains("oldString"));
        assertTrue(parameters.required().contains("newString"));
        // the tool documents itself
        var markdown = tool.toMarkdown();
        assertTrue(markdown.contains("`oldString`"));
        assertTrue(markdown.contains("`replaceAll`"));
    }

    // ------------------------------------------------------- applyEdit semantics (core logic)

    @Test
    void singleOccurrenceIsReplaced(@TempDir Path dir) throws IOException {
        var file = dir.resolve("Main.java");
        Files.writeString(file, "class Main {\n    void foo() {}\n}\n");
        var result = FileTools.applyEdit(file, "src/Main.java", "void foo()",
            "void bar()", false);
        assertTrue(result.startsWith("Replaced 1 occurrence"), result);
        assertEquals("class Main {\n    void bar() {}\n}\n",
            Files.readString(file, StandardCharsets.UTF_8));
    }

    @Test
    void missingOldStringIsAnError(@TempDir Path dir) throws IOException {
        var file = dir.resolve("Main.java");
        Files.writeString(file, "class Main {}\n");
        var result = FileTools.applyEdit(file, "src/Main.java", "not present", "x", false);
        assertTrue(result.startsWith("Error: oldString not found"), result);
        assertEquals("class Main {}\n", Files.readString(file, StandardCharsets.UTF_8),
            "the file must stay untouched");
    }

    @Test
    void ambiguousOldStringIsRejectedUnlessReplaceAll(@TempDir Path dir) throws IOException {
        var file = dir.resolve("Main.java");
        Files.writeString(file, "a b a b\n");
        var ambiguous = FileTools.applyEdit(file, "Main.java", "a", "x", false);
        assertTrue(ambiguous.startsWith("Error: oldString occurs 2 times"), ambiguous);
        assertEquals("a b a b\n", Files.readString(file, StandardCharsets.UTF_8),
            "the file must stay untouched");

        var all = FileTools.applyEdit(file, "Main.java", "a", "x", true);
        assertTrue(all.startsWith("Replaced 2 occurrence(s)"), all);
        assertEquals("x b x b\n", Files.readString(file, StandardCharsets.UTF_8));
    }

    @Test
    void emptyNewStringDeletesAndRegexSpecialCharactersAreLiteral(@TempDir Path dir)
            throws IOException {
        var file = dir.resolve("App.java");
        Files.writeString(file, "int x = 1; // (a*) [x]?\nint x = 1; // (a*) [x]?\n");
        // regex metacharacters in old/new strings must be treated literally
        var result = FileTools.applyEdit(file, "App.java", "// (a*) [x]?", "", true);
        assertTrue(result.startsWith("Replaced 2 occurrence(s)"), result);
        assertEquals("int x = 1; \nint x = 1; \n",
            Files.readString(file, StandardCharsets.UTF_8));
    }

    @Test
    void emptyArgumentsAreRejected(@TempDir Path dir) throws IOException {
        var file = dir.resolve("Main.java");
        Files.writeString(file, "class Main {}\n");
        assertTrue(FileTools.applyEdit(file, "Main.java", "", "x", false)
                .startsWith("Error:"));
        assertTrue(FileTools.applyEdit(file, "Main.java", "class", null, false)
                .startsWith("Error:"));
        assertEquals("class Main {}\n", Files.readString(file, StandardCharsets.UTF_8));
    }

    @Test
    void oversizedFilesAreRejected(@TempDir Path dir) throws IOException {
        var file = dir.resolve("Big.java");
        Files.writeString(file, "x".repeat(4096));
        int oldLimit = LlmSettings.INSTANCE.getMaxFileSizeKB();
        LlmSettings.INSTANCE.setMaxFileSizeKB(1);
        try {
            var result = FileTools.applyEdit(file, "Big.java", "x", "y", false);
            assertTrue(result.startsWith("Error: file larger than maxFileSizeKB"), result);
        } finally {
            LlmSettings.INSTANCE.setMaxFileSizeKB(oldLimit);
        }
    }
}
