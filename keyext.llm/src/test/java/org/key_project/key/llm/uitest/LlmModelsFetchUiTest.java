/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.uitest;

import java.util.List;
import java.util.function.BooleanSupplier;
import javax.swing.AbstractButton;

import org.key_project.key.llm.LlmSettings;
import org.key_project.key.llm.LlmSettingsUI;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.fail;

/**
 * UI test that feeds mock server responses into the LLM settings panel: the "Fetch Models" button
 * performs an HTTP round trip against {@link MockModelsServer} and the received model list must
 * appear in the settings model.
 */
class LlmModelsFetchUiTest {

    @Test
    void mockServerResponseDrivesTheFetchModelsButton() throws Exception {
        try (var models = new MockModelsServer()) {
            var settings = new LlmSettings(LlmSettings.INSTANCE);
            settings.setApiEndpoint(models.getBaseUrl());

            var panel = new LlmSettingsUI(settings);
            McpUiTestHarness.onEdt(() -> {
                var button = McpUiTestHarness.all(panel, AbstractButton.class).stream()
                        .filter(b -> "Fetch Models".equals(b.getText())).findFirst().orElseThrow();
                button.doClick();
            });

            // the SwingWorker fetches asynchronously; poll the working copy of the panel
            await(() -> panel.getModel().getAvailableModels()
                    .containsAll(List.of(MockModelsServer.MOCK_MODELS)));
        }
    }

    /** Polls the condition on the test thread, pumping the EDT, until it holds. */
    private static void await(BooleanSupplier condition) throws InterruptedException {
        long deadline = System.currentTimeMillis() + 10_000;
        while (System.currentTimeMillis() < deadline) {
            if (condition.getAsBoolean()) {
                return;
            }
            // allow the SwingWorker's done() callback to run on the EDT
            McpUiTestHarness.onEdt(() -> {
            });
            Thread.sleep(50);
        }
        fail("condition did not hold within 10 s");
    }
}
