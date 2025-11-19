/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import java.util.ArrayList;
import java.util.List;

/**
 *
 * @author Alexander Weigl
 * @version 1 (11/19/25)
 */
public class LlmContext {
    private final List<LlmMessage> messages = new ArrayList<>();

    public void addMessage(LlmMessage message) {
        messages.add(message);
    }

    public List<LlmMessage> getMessages() {
        return messages;
    }

    public record LlmMessage(String role, String content) {
    }
}
