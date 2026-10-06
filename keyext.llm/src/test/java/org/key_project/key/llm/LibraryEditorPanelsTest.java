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
        // reload must not throw and the table stays consistent with the (possibly empty) library
        assertEquals(PromptLibrary.INSTANCE.all().size(), editor.tableRowCount());
    }

    @Test
    void skillEditorForwardsToTheSkillLibrary() {
        var editor = new SkillLibraryEditor();
        assertEquals(SkillLibrary.INSTANCE.all().size(), editor.tableRowCount());
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
