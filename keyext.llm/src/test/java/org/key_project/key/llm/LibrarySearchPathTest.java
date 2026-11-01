/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.io.IOException;
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
 * Tests the configurable multi-directory search path of the file-backed user libraries: entries
 * are collected from all directories along the search path (first occurrence of a name wins),
 * new files are created in the first directory, and {@code delete} removes a name from all
 * directories. The configured entries support {@code ~}, {@code $(pwd)} and relative paths.
 * <p>
 * The KeY config directory is redirected to a temporary directory and the settings entries are
 * restored afterwards (the libraries are singletons, so both are process-wide).
 */
class LibrarySearchPathTest {

    @TempDir
    Path tempDir;

    private PathConfig.KeyPaths savedPaths;
    private List<String> savedPromptPaths;
    private List<String> savedSkillPaths;

    @BeforeEach
    void redirectConfigDir() throws IOException {
        savedPaths = PathConfig.currentPaths;
        savedPromptPaths = LlmSettings.INSTANCE.getPromptLibraryPaths();
        savedSkillPaths = LlmSettings.INSTANCE.getSkillLibraryPaths();
        PathConfig.setBaseKeyConfigDir(tempDir);
    }

    @AfterEach
    void restoreConfigDir() {
        PathConfig.currentPaths = savedPaths;
        LlmSettings.INSTANCE.setPromptLibraryPaths(savedPromptPaths);
        LlmSettings.INSTANCE.setSkillLibraryPaths(savedSkillPaths);
    }

    private void setSkillPath(String... dirs) {
        LlmSettings.INSTANCE.setSkillLibraryPaths(List.of(dirs));
    }

    @Test
    void emptySearchPathFallsBackToTheDefaultDirectory() {
        assertTrue(SkillLibrary.INSTANCE.searchDirs()
                .contains(PathConfig.currentPaths.keyConfigDir.resolve("llm").resolve("skills")),
            "the default directory must be used when no search path is configured");
    }

    @Test
    void searchPathEntriesAreExpanded() {
        setSkillPath("$(pwd)/key-skills", "~/.key/skills", "relative/dir");
        var dirs = SkillLibrary.INSTANCE.searchDirs();
        assertEquals(Path.of(System.getProperty("user.dir"), "key-skills"), dirs.get(0));
        assertEquals(Path.of(System.getProperty("user.home"), ".key", "skills"), dirs.get(1));
        assertEquals(Path.of(System.getProperty("user.dir"), "relative", "dir"), dirs.get(2));
    }

    @Test
    void blankSearchPathEntriesAreIgnored() {
        setSkillPath("  ", "$(pwd)/key-skills");
        assertEquals(List.of(Path.of(System.getProperty("user.dir"), "key-skills")),
            SkillLibrary.INSTANCE.searchDirs());
    }

    @Test
    void entriesAreCollectedFromAllDirectoriesWithFirstWins() throws IOException {
        var dirA = Files.createDirectories(tempDir.resolve("skills-a"));
        var dirB = Files.createDirectories(tempDir.resolve("skills-b"));
        Files.writeString(dirA.resolve("shared.md"),
            "---\nname: shared\ndescription: from a\nenabled: true\n---\nfirst");
        Files.writeString(dirB.resolve("shared.md"),
            "---\nname: shared\ndescription: from b\nenabled: true\n---\nsecond");
        Files.writeString(dirB.resolve("only-b.md"),
            "---\nname: only-b\ndescription: b\nenabled: true\n---\nbody");
        setSkillPath(dirA.toString(), dirB.toString());

        var all = SkillLibrary.INSTANCE.all();
        assertEquals(List.of("only-b", "shared"), all.stream().map(Skill::name).toList(),
            "entries are sorted by name");
        assertEquals("first", SkillLibrary.INSTANCE.get("shared").instructions(),
            "the first directory in the search order wins");
        assertEquals(dirA.resolve("shared.md"), SkillLibrary.INSTANCE.fileOf("shared"));
        assertEquals(dirB.resolve("only-b.md"), SkillLibrary.INSTANCE.fileOf("only-b"));
        assertNull(SkillLibrary.INSTANCE.fileOf("missing"));
    }

    @Test
    void saveWritesIntoTheFirstDirectoryAndCreatesItIfMissing() throws IOException {
        var dirA = tempDir.resolve("skills-a");
        var dirB = Files.createDirectories(tempDir.resolve("skills-b"));
        setSkillPath(dirA.toString(), dirB.toString());

        assertNull(SkillLibrary.INSTANCE.save(new Skill("created", "", "body", List.of(), true)));
        assertTrue(Files.exists(dirA.resolve("created.md")), dirA + " must be created");
        assertFalse(Files.exists(dirB.resolve("created.md")));
        assertEquals("body", SkillLibrary.INSTANCE.get("created").instructions());
    }

    @Test
    void saveShadowsEntriesInLaterDirectories() throws IOException {
        var dirA = Files.createDirectories(tempDir.resolve("skills-a"));
        var dirB = Files.createDirectories(tempDir.resolve("skills-b"));
        setSkillPath(dirA.toString(), dirB.toString());
        Files.writeString(dirB.resolve("shared.md"),
            "---\nname: shared\ndescription: b\nenabled: true\n---\nsecond");

        assertNull(SkillLibrary.INSTANCE.save(new Skill("shared", "", "updated", List.of(), true)));

        assertTrue(Files.exists(dirA.resolve("shared.md")), "the new file must be written");
        assertTrue(Files.exists(dirB.resolve("shared.md")),
            "the shadowed file must be kept (it belongs to another directory)");
        assertEquals("updated", SkillLibrary.INSTANCE.get("shared").instructions());
    }

    @Test
    void deleteRemovesTheEntryFromAllDirectories() throws IOException {
        var dirA = Files.createDirectories(tempDir.resolve("skills-a"));
        var dirB = Files.createDirectories(tempDir.resolve("skills-b"));
        setSkillPath(dirA.toString(), dirB.toString());
        Files.writeString(dirA.resolve("gone.md"),
            "---\nname: gone\ndescription: a\nenabled: true\n---\na");
        Files.writeString(dirB.resolve("gone.md"),
            "---\nname: gone\ndescription: b\nenabled: true\n---\nb");

        assertNull(SkillLibrary.INSTANCE.delete("gone"));
        assertFalse(Files.exists(dirA.resolve("gone.md")));
        assertFalse(Files.exists(dirB.resolve("gone.md")));
        assertTrue(SkillLibrary.INSTANCE.all().isEmpty());
        assertTrue(SkillLibrary.INSTANCE.delete("gone") != null, "second delete reports missing");
    }
}
