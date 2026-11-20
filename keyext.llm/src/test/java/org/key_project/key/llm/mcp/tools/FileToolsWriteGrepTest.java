/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.regex.Pattern;

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
 * Headless tests of the {@code write} and {@code grep} file tools: the core semantics (file
 * writing, tree search) run against temporary directories without a proof, plus the tool
 * metadata (name, category, approval, parameter schema).
 *
 * @author Alexander Weigl
 */
class FileToolsWriteGrepTest {

    // ------------------------------------------------------------------ write semantics

    @Test
    void writeCreatesParentDirectoriesAndOverwrites(@TempDir Path dir) throws IOException {
        var file = dir.resolve("src/org/example/New.java");
        var result = FileTools.writeToFile(file, "src/org/example/New.java", "class New {}\n");
        assertTrue(result.startsWith("Wrote "), result);
        assertEquals("class New {}\n", Files.readString(file, StandardCharsets.UTF_8));

        var second = FileTools.writeToFile(file, "src/org/example/New.java", "// replaced\n");
        assertTrue(second.startsWith("Wrote "), second);
        assertEquals("// replaced\n", Files.readString(file, StandardCharsets.UTF_8),
            "an existing file must be overwritten");
    }

    // ------------------------------------------------------------------ grep semantics

    @Test
    void grepReportsMatchingLinesWithPaths(@TempDir Path dir) throws IOException {
        Files.createDirectories(dir.resolve("src/org/example"));
        Files.writeString(dir.resolve("src/org/example/A.java"), "int x = 1;\nint y = 2;\n");
        Files.writeString(dir.resolve("src/org/example/B.java"), "int x = 3;\n");
        Files.writeString(dir.resolve("src/notes.txt"), "nothing here\n");

        var result = FileTools.searchTree(dir, dir, Pattern.compile("int x"), null, 100);
        assertTrue(result.contains("src/org/example/A.java:1: int x = 1;"), result);
        assertTrue(result.contains("src/org/example/B.java:1: int x = 3;"), result);
        assertFalse(result.contains("notes.txt"), result);
    }

    @Test
    void grepLiteralIgnoresRegexSpecialCharacters(@TempDir Path dir) throws IOException {
        Files.writeString(dir.resolve("f.java"), "a.b\naxb\n");
        var regex = FileTools.searchTree(dir, dir, Pattern.compile("a.b"), null, 100);
        assertTrue(regex.contains("f.java:1: a.b") && regex.contains("f.java:2: axb"), regex);
        var literal = FileTools.searchTree(dir, dir, Pattern.compile("a\\.b"), null, 100);
        assertTrue(literal.contains("f.java:1: a.b"), literal);
        assertFalse(literal.contains("axb"), literal);
    }

    @Test
    void grepCaseSensitivityIsOptOut(@TempDir Path dir) throws IOException {
        Files.writeString(dir.resolve("f.java"), "Foo\nfoo\n");
        var sensitive = FileTools.searchTree(dir, dir, Pattern.compile("foo"), null, 100);
        assertEquals(1, sensitive.lines().count(), sensitive);
        var insensitive = FileTools.searchTree(dir, dir,
            Pattern.compile("foo", Pattern.CASE_INSENSITIVE | Pattern.UNICODE_CASE), null, 100);
        assertEquals(2, insensitive.lines().count(), insensitive);
    }

    @Test
    void grepIncludeFiltersFilesByGlob(@TempDir Path dir) throws IOException {
        Files.writeString(dir.resolve("A.java"), "int x;\n");
        Files.writeString(dir.resolve("B.md"), "int x;\n");
        Files.createDirectories(dir.resolve("deep"));
        Files.writeString(dir.resolve("deep/C.java"), "int x;\n");
        // ripgrep-like: **/*.java matches top-level and nested files alike
        var include = FileTools.GlobFilter.of("**/*.java");
        var result = FileTools.searchTree(dir, dir, Pattern.compile("int x"), include, 100);
        assertTrue(result.contains("A.java"), result);
        assertTrue(result.contains("deep/C.java"), result);
        assertFalse(result.contains("B.md"), result);
        // a name-only glob applies at any depth
        var nameOnly = FileTools.GlobFilter.of("*.md");
        var mdOnly = FileTools.searchTree(dir, dir, Pattern.compile("int x"), nameOnly, 100);
        assertTrue(mdOnly.contains("B.md"), mdOnly);
        assertFalse(mdOnly.contains("A.java"), mdOnly);
    }

    @Test
    void grepLimitsMatchesAndReportsTruncation(@TempDir Path dir) throws IOException {
        var sb = new StringBuilder();
        for (int i = 0; i < 5; i++) {
            sb.append("hit ").append(i).append('\n');
        }
        Files.writeString(dir.resolve("f.java"), sb.toString());
        var result = FileTools.searchTree(dir, dir, Pattern.compile("hit"), null, 3);
        assertEquals(3, result.lines().filter(l -> l.matches("f\\.java:\\d+:.*")).count(), result);
        assertTrue(result.contains("showing 3 of 5 matches"), result);
    }

    @Test
    void grepEmptyTreeReportsNoMatches(@TempDir Path dir) throws IOException {
        var result = FileTools.searchTree(dir, dir, Pattern.compile("anything"), null, 100);
        assertEquals("(no matches)", result);
    }

    // ------------------------------------------------------------------ tool metadata

    @Test
    void writeToolMetadata() {
        var tools = new KeYAgentTools();
        var tool = tools.agent(KeYAgentTools.TOOL_WRITE);
        assertNotNull(tool, "write must be registered");
        assertEquals(ToolCategory.FILES, tool.category());
        assertEquals(Tool.ApprovalRequirement.ASK, tool.approval());
        assertFalse(tool.backgroundable());
        var parameters = tool.parameters();
        assertNotNull(parameters.properties().get("path"));
        assertNotNull(parameters.properties().get("content"));
        assertTrue(parameters.required().contains("path"));
        assertTrue(parameters.required().contains("content"));
    }

    @Test
    void grepToolMetadata() {
        var tools = new KeYAgentTools();
        var tool = tools.agent(KeYAgentTools.TOOL_GREP);
        assertNotNull(tool, "grep must be registered");
        assertEquals(ToolCategory.FILES, tool.category());
        assertEquals(Tool.ApprovalRequirement.AUTO, tool.approval());
        var parameters = tool.parameters();
        assertNotNull(parameters.properties().get("pattern"));
        assertNotNull(parameters.properties().get("path"));
        assertNotNull(parameters.properties().get("include"));
        assertNotNull(parameters.properties().get("literal"));
        assertNotNull(parameters.properties().get("caseSensitive"));
        assertNotNull(parameters.properties().get("limit"));
        assertTrue(parameters.required().contains("pattern"));
        var markdown = tool.toMarkdown();
        assertTrue(markdown.contains("`caseSensitive`"), markdown);
        assertTrue(markdown.contains("path:line: text"), markdown);
    }
}
