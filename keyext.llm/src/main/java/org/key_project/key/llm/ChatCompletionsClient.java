/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import java.util.Map;

/**
 * Abstraction over a single chat-completion HTTP call. The default implementation talks to an
 * OpenAI-compatible endpoint; tests may substitute a fake.
 */
public interface ChatCompletionsClient {
    /**
     * Sends one request and returns the parsed JSON response document.
     *
     * @param session the session carrying endpoint and authentication
     * @param request the fully assembled request
     * @return the parsed response (contains a {@code choices} array on success)
     * @throws Exception on transport or protocol errors; non-2xx status codes throw as well
     */
    Map<String, Object> complete(LlmSession session, AgentRequest request) throws Exception;
}
