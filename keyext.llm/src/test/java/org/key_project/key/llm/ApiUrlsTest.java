/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * {@link ApiUrls} must derive working operation URLs for the different OpenAI-compatible gateways
 * (e.g. the KIT Open WebUI at {@code ki-toolbox.scc.kit.edu} serving {@code /openai/…} and the
 * LiteLLM proxy at {@code litellm.scc.kit.edu} serving {@code /v1/…}) from whatever base URL the
 * user configured.
 */
class ApiUrlsTest {

    // ---------------------------------------------------------------- bare hosts → /openai/…

    @Test
    void bareHostGetsTheOpenAiPrefix() {
        assertEquals("https://ki-toolbox.scc.kit.edu/openai/chat/completions",
            ApiUrls.chatCompletions("https://ki-toolbox.scc.kit.edu"));
        assertEquals("https://ki-toolbox.scc.kit.edu/openai/models",
            ApiUrls.models("https://ki-toolbox.scc.kit.edu"));
    }

    @Test
    void liteLlmBareHostUsesItsOpenAiCatchAll() {
        // LiteLLM serves /openai/{endpoint} as well, so the bare host behaves like Open WebUI
        assertEquals("https://litellm.scc.kit.edu/openai/chat/completions",
            ApiUrls.chatCompletions("https://litellm.scc.kit.edu"));
        assertEquals("https://litellm.scc.kit.edu/openai/models",
            ApiUrls.models("https://litellm.scc.kit.edu"));
    }

    // ---------------------------------------------------------------- versioned API roots

    @Test
    void liteLlmV1BaseAppendsOnlyTheOperation() {
        assertEquals("https://litellm.scc.kit.edu/v1/chat/completions",
            ApiUrls.chatCompletions("https://litellm.scc.kit.edu/v1"));
        assertEquals("https://litellm.scc.kit.edu/v1/models",
            ApiUrls.models("https://litellm.scc.kit.edu/v1"));
    }

    @Test
    void openWebUiApiRootsAppendOnlyTheOperation() {
        assertEquals("https://ki-toolbox.scc.kit.edu/api/v1/chat/completions",
            ApiUrls.chatCompletions("https://ki-toolbox.scc.kit.edu/api/v1"));
        assertEquals("https://ki-toolbox.scc.kit.edu/api/v1/models",
            ApiUrls.models("https://ki-toolbox.scc.kit.edu/api/v1"));
        assertEquals("https://ki-toolbox.scc.kit.edu/api/chat/completions",
            ApiUrls.chatCompletions("https://ki-toolbox.scc.kit.edu/api"));
        assertEquals("https://ki-toolbox.scc.kit.edu/api/models",
            ApiUrls.models("https://ki-toolbox.scc.kit.edu/api"));
        assertEquals("https://ki-toolbox.scc.kit.edu/openai/chat/completions",
            ApiUrls.chatCompletions("https://ki-toolbox.scc.kit.edu/openai"));
    }

    @Test
    void legacyDefaultEndingInV1UsesTheOpenAiConvention() {
        // stored settings from before the derivation existed end in /v1
        assertEquals("https://ki-toolbox.scc.kit.edu/v1/chat/completions",
            ApiUrls.chatCompletions("https://ki-toolbox.scc.kit.edu/v1"));
    }

    // ---------------------------------------------------------------- bases with a full path

    @Test
    void baseWithTheFullOperationPathIsUsedAsIs() {
        assertEquals("https://litellm.scc.kit.edu/v1/chat/completions",
            ApiUrls.chatCompletions("https://litellm.scc.kit.edu/v1/chat/completions"));
        assertEquals("https://litellm.scc.kit.edu/v1/models",
            ApiUrls.models("https://litellm.scc.kit.edu/v1/models"));
    }

    @Test
    void siblingOperationIsDerivedFromTheOtherPath() {
        assertEquals("https://litellm.scc.kit.edu/v1/models",
            ApiUrls.models("https://litellm.scc.kit.edu/v1/chat/completions"));
        assertEquals("https://ki-toolbox.scc.kit.edu/openai/chat/completions",
            ApiUrls.chatCompletions("https://ki-toolbox.scc.kit.edu/openai/models"));
    }

    // ---------------------------------------------------------------- robustness

    @Test
    void trailingSlashesAndWhitespaceAreIgnored() {
        assertEquals("https://litellm.scc.kit.edu/v1/chat/completions",
            ApiUrls.chatCompletions("  https://litellm.scc.kit.edu/v1/  "));
        assertEquals("https://ki-toolbox.scc.kit.edu/openai/models",
            ApiUrls.models("https://ki-toolbox.scc.kit.edu///"));
    }

    @Test
    void localhostMockServerKeepsTheOpenAiConvention() {
        // the mock server of the UI tests serves /openai/models on a bare base
        assertEquals("http://127.0.0.1:44711/openai/models",
            ApiUrls.models("http://127.0.0.1:44711"));
    }
}
