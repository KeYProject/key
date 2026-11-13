/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.List;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The search paths of the prompt/skill libraries must ignore blank entries: the string-list
 * parser yields {@code [""]} for the empty default value, and a stored blank entry would show
 * up as an invisible row in the settings' search-path list and hide the default-directory
 * pseudo-entry.
 */
class LibrarySearchPathSettingsTest {

    private final LlmSettings settings = LlmSettings.INSTANCE;
    private List<String> savedSkillPaths;
    private List<String> savedPromptPaths;

    @BeforeEach
    void savePaths() {
        savedSkillPaths = settings.getSkillLibraryPaths();
        savedPromptPaths = settings.getPromptLibraryPaths();
    }

    @AfterEach
    void restorePaths() {
        settings.setSkillLibraryPaths(savedSkillPaths);
        settings.setPromptLibraryPaths(savedPromptPaths);
    }

    @Test
    void blankEntriesAreDropped() {
        settings.setSkillLibraryPaths(List.of("", "/home/x/skills"));
        assertEquals(List.of("/home/x/skills"), settings.getSkillLibraryPaths());

        settings.setPromptLibraryPaths(List.of("", " ", "\t"));
        assertTrue(settings.getPromptLibraryPaths().isEmpty(),
            "a path list of only blanks behaves like the unconfigured default path");
    }

    @Test
    void configuredDirectoriesRoundTrip() {
        settings.setSkillLibraryPaths(List.of("~/skills", "$(pwd)/more"));
        assertEquals(List.of("~/skills", "$(pwd)/more"), settings.getSkillLibraryPaths());
    }
}
