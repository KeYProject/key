/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import de.uka.ilkd.key.settings.PathConfig;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests the Markdown storage of the user libraries (skills and prompts): files are written as
 * {@code <name>.md} with a YAML front matter, legacy {@code <name>.json} files are migrated on
 * first access, and delete/save keep the two formats in sync.
 * <p>
 * The KeY config directory is redirected to a temporary directory for the duration of the test
 * and restored afterwards (the libraries are singletons, so the redirect is process-wide).
 */
class PromptSkillStorageTest {

    @TempDir
    Path tempDir;

    private PathConfig.KeyPaths savedPaths;

    @BeforeEach
    void redirectConfigDir() throws IOException {
        savedPaths = PathConfig.currentPaths;
        PathConfig.setBaseKeyConfigDir(tempDir);
    }

    @AfterEach
    void restoreConfigDir() {
        PathConfig.currentPaths = savedPaths;
    }

    private Path skillsDir() {
        return PathConfig.currentPaths.keyConfigDir.resolve("llm").resolve("skills");
    }

    private Path promptsDir() {
        return PathConfig.currentPaths.keyConfigDir.resolve("llm").resolve("prompts");
    }

    @Test
    void savesSkillsAsMarkdownFilesWithFrontMatter() throws IOException {
        var skill = new Skill("optics", "focus on overflow",
            "Pay attention to overflow.\nSecond paragraph.", List.of("read_file", "auto"), false);

        assertNull(SkillLibrary.INSTANCE.save(skill));

        var file = skillsDir().resolve("optics.md");
        assertTrue(Files.exists(file), "expected " + file);
        assertFalse(Files.exists(skillsDir().resolve("optics.json")));

        var text = Files.readString(file, StandardCharsets.UTF_8);
        assertTrue(text.startsWith("---\n"), "front matter must open the document:\n" + text);
        assertTrue(text.contains("name: optics")
                || text.contains("name: \"optics\""),
            "front matter must carry the name:\n" + text);
        assertTrue(text.contains("enabled: false"), "front matter must carry 'enabled'");
        assertTrue(text.contains("read_file"), "allowedTools must be serialized");
        assertTrue(text.contains("Pay attention to overflow."), "body must hold instructions");

        // the file is read back as the same skill
        assertEquals(skill, SkillLibrary.INSTANCE.get("optics"));
        assertEquals(List.of(skill), SkillLibrary.INSTANCE.all());
    }

    @Test
    void savesPromptsAsMarkdownFiles() throws IOException {
        var prompt =
            new Prompt("prove-method", "prove the postcondition", "Prove $seq with $goals.");

        assertNull(PromptLibrary.INSTANCE.save(prompt));

        var file = promptsDir().resolve("prove-method.md");
        assertTrue(Files.exists(file));
        var text = Files.readString(file, StandardCharsets.UTF_8);
        assertTrue(text.startsWith("---\n"));
        assertTrue(text.contains("Prove $seq with $goals."), "template must be the Markdown body");
        assertEquals(prompt, PromptLibrary.INSTANCE.get("prove-method"));
    }

    @Test
    void edgeCaseValuesRoundTripThroughYaml() {
        // values that YAML 1.1 would misread as booleans/numbers must survive verbatim
        var prompt = new Prompt("tricky", "on", "body with a\n---\nthematic break inside");
        var stored = PromptLibrary.serialize(prompt);
        assertEquals(prompt, PromptLibrary.parse(stored));
        assertTrue(stored.contains("\"on\""),
            "values that look like YAML booleans must be quoted:\n" + stored);

        var skill = new Skill("tricky", "123", "instructions\n\nsecond paragraph", List.of(), true);
        assertEquals(skill, SkillLibrary.parse(SkillLibrary.serialize(skill)));
    }

    @Test
    void migratesLegacyJsonFilesOnFirstAccess() throws IOException {
        Files.createDirectories(skillsDir());
        Files.writeString(skillsDir().resolve("legacy.json"),
            "{\"name\":\"legacy\",\"description\":\"old\",\"instructions\":\"old body\","
                + "\"allowedTools\":[],\"enabled\":true}",
            StandardCharsets.UTF_8);

        // the first read migrates the legacy file and reads the converted skill
        var skill = SkillLibrary.INSTANCE.get("legacy");
        assertEquals("old body", skill.instructions());
        assertTrue(Files.exists(skillsDir().resolve("legacy.md")),
            "legacy JSON must be converted to Markdown");
        assertFalse(Files.exists(skillsDir().resolve("legacy.json")),
            "legacy JSON must be removed after migration");
    }

    @Test
    void markdownFileWinsOverLegacyJsonOfTheSameName() throws IOException {
        Files.createDirectories(skillsDir());
        Files.writeString(skillsDir().resolve("both.md"),
            "---\nname: both\ndescription: new\nenabled: true\n---\nnew body",
            StandardCharsets.UTF_8);
        Files.writeString(skillsDir().resolve("both.json"),
            "{\"name\":\"both\",\"instructions\":\"old body\",\"enabled\":false}",
            StandardCharsets.UTF_8);

        var skill = SkillLibrary.INSTANCE.get("both");
        assertEquals("new body", skill.instructions(), "the Markdown file must win");
        assertFalse(Files.exists(skillsDir().resolve("both.json")));
    }

    @Test
    void saveRemovesStaleJsonAndDeleteRemovesBothFormats() throws IOException {
        var name = "roundtrip";
        assertNull(SkillLibrary.INSTANCE.save(new Skill(name, "", "", List.of(), true)));
        // planting a stale .json of the same name must be cleaned by the next save
        Files.writeString(skillsDir().resolve(name + ".json"), "{}", StandardCharsets.UTF_8);
        assertNull(SkillLibrary.INSTANCE.save(new Skill(name, "updated", "new instructions",
            List.of(), true)));
        assertFalse(Files.exists(skillsDir().resolve(name + ".json")));

        assertNull(SkillLibrary.INSTANCE.delete(name));
        assertFalse(Files.exists(skillsDir().resolve(name + ".md")));
        assertFalse(Files.exists(skillsDir().resolve(name + ".json")));
        assertTrue(SkillLibrary.INSTANCE.delete(name) != null, "second delete must report missing");
    }
}
