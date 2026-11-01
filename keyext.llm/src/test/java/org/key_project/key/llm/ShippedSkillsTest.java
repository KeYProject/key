/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.KeYAgentTools;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The example skills shipped in {@code keyext.llm/skills} must be loadable by the real
 * {@link SkillLibrary}: each file parses to a skill with a valid name and description, and every
 * {@code allowedTools} entry refers to a tool of the built-in tool set.
 */
class ShippedSkillsTest {

    private static final Path SKILLS_DIR = Path.of("skills");

    @Test
    void shippedSkillsParseAndReferenceRealTools() throws IOException {
        assertTrue(Files.isDirectory(SKILLS_DIR),
            "the shipped skill directory " + SKILLS_DIR.toAbsolutePath() + " is missing");
        try (Stream<Path> files = Files.list(SKILLS_DIR)) {
            var markdowns = files.filter(p -> p.toString().endsWith(".md")).sorted().toList();
            assertTrue(markdowns.size() >= 5, "expected a non-trivial set of shipped skills");

            var knownTools = new KeYAgentTools().agents().stream()
                    .map(AgentTool::name).collect(java.util.stream.Collectors.toSet());

            for (Path md : markdowns) {
                var skill = SkillLibrary.parse(Files.readString(md));
                assertNotNull(skill, md + " must parse to a skill (front matter)");
                assertTrue(SkillLibrary.INSTANCE.validate(skill) == null,
                    md + ": " + SkillLibrary.INSTANCE.validate(skill));
                assertNotNull(skill.description(), md + " needs a description");
                assertTrue(!skill.description().isBlank(), md + " needs a description");
                for (String tool : skill.allowedTools()) {
                    assertTrue(knownTools.contains(tool),
                        md + " whitelists unknown tool '" + tool + "'");
                }
            }
        }
    }

    @Test
    void shippedSkillsAreEnabledByDefault() throws IOException {
        try (Stream<Path> files = Files.list(SKILLS_DIR)) {
            var markdowns = files.filter(p -> p.toString().endsWith(".md")).sorted().toList();
            for (Path md : markdowns) {
                var skill = SkillLibrary.parse(Files.readString(md));
                assertNotNull(skill, md + " must parse to a skill");
                assertTrue(skill.enabled(), skill.name() + " must ship enabled");
            }
        }
    }

    @Test
    void serializationRoundTripMatchesTheShippedFormat() {
        var skill = new Skill("demo-name", "a description", "instructions body",
            List.of(KeYAgentTools.TOOL_READ_FILE, KeYAgentTools.TOOL_LIST_FILES), true);
        var markdown = SkillLibrary.serialize(skill);
        var parsed = SkillLibrary.parse(markdown);
        assertEquals(skill, parsed);
        assertTrue(markdown.startsWith("---\nname: demo-name"));
        assertTrue(markdown.contains("allowedTools:"));
        Set.of("read_file", "list_files").forEach(t -> assertTrue(markdown.contains("- " + t)));
    }
}
