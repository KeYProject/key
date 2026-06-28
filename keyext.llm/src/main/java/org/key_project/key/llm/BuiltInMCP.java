/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.List;
import java.util.Map;

/**
 *
 * @author Alexander Weigl
 * @version 1 (28.06.26)
 */
public class BuiltInMCP implements LlmClientExtended.McpClient {
    private boolean isClosed = false;

    @Override
    public List<Map<String, Object>> getToolsAsOpenAiFormat() {
        return List.of(
            Map.of("type", "function",
                "function", Map.of(
                    "name", "echo",
                    "description", "returns the given string",
                    "parameters", Map.of("type", "object", "properties", Map.of()))));
    }

    @Override
    public Object callTool(String toolName, String arguments) throws Exception {
        System.out.println("Calling tool " + toolName + " with arguments " + arguments);
        return null;
    }

    @Override
    public boolean isClosed() {
        return isClosed;
    }

    @Override
    public void close() {
        isClosed = true;
    }
}
