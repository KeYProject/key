/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.stream.Collectors;

import io.modelcontextprotocol.client.transport.ServerParameters;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * End-to-end test of the SDK-backed {@link McpClientStdio}: it spawns a real MCP server
 * ({@link TestMcpStdioServerMain}, built on the SDK's stdio server transport) in a separate JVM
 * and drives the full client lifecycle over stdin/stdout.
 */
class McpClientStdioTest {

    @Test
    void talksToAnSdkStdioServer() throws Exception {
        var java = ProcessHandle.current().info().command().orElse("java");
        var cp = System.getProperty("java.class.path");
        var client = new McpClientStdio(ServerParameters.builder(java)
                .args("-cp", cp, TestMcpStdioServerMain.class.getName()).build());
        try {
            client.initialize();
            assertTrue(client.isInitialized());

            var names = client.getTools().stream().map(t -> t.function().name())
                    .collect(Collectors.toSet());
            assertTrue(names.contains(TestMcpStdioServerMain.ECHO_TOOL),
                "expected the echo tool, got " + names);

            var result = client.callTool(TestMcpStdioServerMain.ECHO_TOOL, "{\"x\":\"hi\"}");
            assertEquals("stdio:hi", result);

            // capabilities were captured during the handshake
            assertTrue(client.getServerCapabilities().containsKey("tools"));
        } finally {
            client.close();
        }
        assertTrue(client.isClosed());
    }
}
