/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.List;

import de.uka.ilkd.key.gui.settings.SettingsProvider;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Smoke tests for the prompt/skill editors and the tools panel that are shown as separate nodes
 * under "LLM Settings" in the settings dialog. They only read the file-backed libraries (empty
 * when the config directory does not exist), so they are safe to construct headless.
 */
class LibraryEditorPanelsTest {

    @Test
    void promptEditorCanBeConstructed() {
        assertDoesNotThrow(() -> {
            var editor = new PromptLibraryEditor();
            assertNotNull(editor.getComponentCount());
        });
    }

    @Test
    void skillEditorCanBeConstructed() {
        assertDoesNotThrow(() -> {
            var editor = new SkillLibraryEditor();
            assertNotNull(editor.getComponentCount());
        });
    }

    @Test
    void promptEditorForwardsToThePromptLibrary() {
        var editor = new PromptLibraryEditor();
        // reload must not throw and the list stays consistent with the (possibly empty) library
        assertEquals(PromptLibrary.INSTANCE.all().size(), editor.entryCount());
    }

    @Test
    void skillEditorForwardsToTheSkillLibrary() {
        var editor = new SkillLibraryEditor();
        assertEquals(SkillLibrary.INSTANCE.all().size(), editor.entryCount());
    }

    @Test
    void promptMarkdownRoundTrip() {
        var editor = new PromptLibraryEditor();
        var original = List.of(new Prompt("p1", "First prompt", "Do $seq"),
            new Prompt("p2", "With markup", "Read @file and reply with \"quotes\"."),
            new Prompt("p3", "empty body", ""));
        for (var p : original) {
            assertEquals(p, editor.fromMarkdown(editor.toMarkdown(p)));
        }
    }

    @Test
    void skillMarkdownRoundTrip() {
        var editor = new SkillLibraryEditor();
        var original = List.of(
            new Skill("s1", "A skill", "instructions and $goals", List.of("auto", "tryclose"),
                true),
            new Skill("s2", "", "", List.of(), false),
            new Skill("s3", "multi-line",
                "line one\n\nline two\n```\ncode\n```\n", List.of(), true));
        for (var s : original) {
            assertEquals(s, editor.fromMarkdown(editor.toMarkdown(s)));
        }
    }

    @Test
    void invalidMarkdownParsesToNull() {
        var editor = new SkillLibraryEditor();
        assertEquals(null, editor.fromMarkdown("no front matter here"));
        assertEquals(null, editor.fromMarkdown("---\nname:\n---\nbody")); // blank name
    }

    @Test
    void toolsPanelCanBeConstructed() {
        assertDoesNotThrow(() -> {
            var panel = new LlmToolsPanel(new LlmSettings(LlmSettings.INSTANCE));
            assertNotNull(panel.getComponentCount());
            assertEquals(LlmSettings.INSTANCE.getToolsDisabled(),
                panel.getModel().getToolsDisabled());
        });
    }

    @Test
    void settingsTreeHasToolsPromptsAndSkillsChildren() {
        var children = LlmExtension.LlmSettingsProvider.INSTANCE.getChildren();
        assertEquals(List.of("Tools", "Prompts", "Skills"),
            children.stream().map(SettingsProvider::getDescription).toList());
    }
}
