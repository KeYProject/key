/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.KeYAgentTools;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The example skills shipped in {@code keyext.llm/skills} must be loadable by the real
 * {@link SkillLibrary}: each file parses to a skill with a valid name and description, every
 * {@code allowedTools} entry refers to a tool of the built-in tool set, and the bundled
 * {@code /skills.zip} resource (used to seed the default skill directory) stays in sync with the
 * source directory.
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

    // ------------------------------------------------------------------------ bundled archive

    /** Helper collecting the shipped {@code <name>.md -> content} map from the source directory. */
    private LinkedHashMap<String, String> sourceSkills() throws IOException {
        var entries = new LinkedHashMap<String, String>();
        try (Stream<Path> files = Files.list(SKILLS_DIR)) {
            files.filter(p -> p.toString().endsWith(".md")).sorted().forEach(p -> {
                try {
                    entries.put(p.getFileName().toString(), Files.readString(p));
                } catch (IOException e) {
                    throw new IllegalStateException(e);
                }
            });
        }
        return entries;
    }

    /** The bundled /skills.zip classpath resource must equal the source directory exactly. */
    @Test
    void bundledSkillsZipMatchesTheSourceDirectory() throws IOException {
        var bundled = SkillLibrary.readShippedSkills();
        var source = sourceSkills();
        assertFalse(source.isEmpty(), "the source skill directory must not be empty");
        assertEquals(source, bundled,
            "/skills.zip is out of sync with " + SKILLS_DIR.toAbsolutePath()
                + " (run :keyext.llm:bundleSkillsZip)");
    }

    /** Seeding extracts the bundled skills into an empty default directory. */
    @Test
    void seedingExtractsTheBundledSkills(@TempDir Path dir) throws IOException {
        SkillLibrary.INSTANCE.seedDefaultDirectory(dir);
        var seeded = new LinkedHashMap<String, String>();
        try (Stream<Path> files = Files.list(dir)) {
            files.filter(p -> p.toString().endsWith(".md")).sorted().forEach(p -> {
                try {
                    seeded.put(p.getFileName().toString(), Files.readString(p));
                } catch (IOException e) {
                    throw new IllegalStateException(e);
                }
            });
        }
        assertEquals(sourceSkills(), seeded, "seeding must materialize every shipped skill");
        for (String content : seeded.values()) {
            var skill = SkillLibrary.parse(content);
            assertNotNull(skill, "a seeded skill must parse");
            assertTrue(SkillLibrary.INSTANCE.validate(skill) == null);
        }
    }

    /** Seeding is a no-op when the default directory already holds skills. */
    @Test
    void seedingLeavesAnExistingDirectoryAlone(@TempDir Path dir) throws IOException {
        var own = dir.resolve("mine.md");
        Files.writeString(own, SkillLibrary.serialize(new Skill("mine", "", "body", List.of(),
            true)));
        SkillLibrary.INSTANCE.seedDefaultDirectory(dir);
        try (Stream<Path> files = Files.list(dir)) {
            assertEquals(List.of(own), files.toList(),
                "seeding must not touch a directory that already has skills");
        }
    }
}
