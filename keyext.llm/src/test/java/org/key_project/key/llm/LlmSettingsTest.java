/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests the {@link LlmSettings} copy constructor: the settings panels edit a copy of the model,
 * so every persisted value must be carried over (this pins the web and scripting settings).
 *
 * @author Alexander Weigl
 */
class LlmSettingsTest {

    @AfterEach
    void restoreDefaults() {
        LlmSettings.INSTANCE.setUnrestrictedExecute(false);
        LlmSettings.INSTANCE.setExecuteTimeoutSeconds(60);
        LlmSettings.INSTANCE.setExecuteMaxOutputChars(65536);
        LlmSettings.INSTANCE.setWebSearchEndpoint(LlmSettings.DEFAULT_WEB_SEARCH_ENDPOINT);
    }

    @Test
    void copyConstructorCopiesTheWebAndScriptingSettings() {
        var source = new LlmSettings();
        source.setUnrestrictedExecute(true);
        source.setExecuteTimeoutSeconds(7);
        source.setExecuteMaxOutputChars(1234);
        source.setWebSearchEndpoint("https://search.example.test/?");

        var copy = new LlmSettings(source);
        assertTrue(copy.getUnrestrictedExecute());
        assertEquals(7, copy.getExecuteTimeoutSeconds());
        assertEquals(1234, copy.getExecuteMaxOutputChars());
        assertEquals("https://search.example.test/?", copy.getWebSearchEndpoint());

        // the copy is independent of its source
        copy.setExecuteTimeoutSeconds(9);
        assertEquals(7, source.getExecuteTimeoutSeconds());
    }
}
