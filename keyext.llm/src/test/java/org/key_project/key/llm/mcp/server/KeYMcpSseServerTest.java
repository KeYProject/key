/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.server;

import java.net.URI;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

import org.key_project.key.llm.LlmSettings;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.tools.TestAgentToolProvider;

import io.modelcontextprotocol.client.transport.HttpClientSseClientTransport;
import io.modelcontextprotocol.spec.McpSchema;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * End-to-end tests of the KeY MCP server: an actual MCP client (the SDK's
 * {@code HttpClientSseClientTransport}) connects over SSE, performs the handshake, lists the
 * exported tools and invokes one of them.
 */
class KeYMcpSseServerTest {

    private KeYMcpSseServer server;

    @BeforeEach
    void resetSettings() {
        LlmSettings.INSTANCE.setToolsDisabled(new TreeSet<>());
        LlmSettings.INSTANCE.setAllowedToolsWithApproval(new TreeSet<>());
        LlmSettings.INSTANCE.setAllowedToolsWithoutApproval(new TreeSet<>());
        LlmSettings.INSTANCE.setMcpExportedTools(new TreeSet<>());
        LlmSettings.INSTANCE.setMcpNotExportedTools(new TreeSet<>());
    }

    @AfterEach
    void stopServer() {
        if (server != null) {
            server.stop();
            server = null;
        }
    }

    @Test
    void handshakeListAndCallToolOverSse() throws Exception {
        server = new KeYMcpSseServer("127.0.0.1", 0, null, new KeYAgentTools());
        server.start();
        String endpoint = server.getSseEndpoint();
        assertNotNull(endpoint);
        assertTrue(endpoint.startsWith("http://127.0.0.1:") && endpoint.endsWith("/sse"),
            "endpoint " + endpoint);

        var transport = HttpClientSseClientTransport.builder(endpoint).build();
        var client = io.modelcontextprotocol.client.McpClient.sync(transport)
                .clientInfo(new McpSchema.Implementation("KeYMcpSseServerTest", "1.0"))
                .build();
        try {
            var init = client.initialize();
            assertNotNull(init);
            assertFalse(init.protocolVersion().isBlank());

            // the test-only AUTO tool is exported (it is a KeY-specific tool), built-in
            // KeY-specific tools follow their metadata default; standard tools stay private
            var names = client.listTools().tools().stream().map(McpSchema.Tool::name)
                    .collect(Collectors.toSet());
            assertTrue(names.contains(TestAgentToolProvider.EXTRA_TOOL),
                "auto-approved agents must be exported by default, got " + names);
            assertTrue(names.contains(KeYAgentTools.TOOL_GET_PROOF_CONTEXT),
                "auto-approved proof tools must be exported by default, got " + names);
            assertFalse(names.contains(KeYAgentTools.TOOL_READ),
                "standard tools must never be exported, got " + names);
            assertFalse(names.contains(KeYAgentTools.TOOL_SHELL),
                "ASK tools must not be exported by default");

            var result = client.callTool(McpSchema.CallToolRequest
                    .builder(TestAgentToolProvider.EXTRA_TOOL).arguments(Map.of("x", "hello"))
                    .build());
            assertNotNull(result);
            assertTrue(result.isError() == null || !result.isError());
            assertTrue(result.content().get(0) instanceof McpSchema.TextContent);
            assertEquals("echo-agent:hello",
                ((McpSchema.TextContent) result.content().get(0)).text());
        } finally {
            client.close();
        }
    }

    @Test
    void requiresBearerToken() throws Exception {
        server = new KeYMcpSseServer("127.0.0.1", 0, "s3cret", new KeYAgentTools());
        server.start();
        String endpoint = server.getSseEndpoint();

        var http = HttpClient.newHttpClient();
        HttpResponse<String> anon =
            http.send(HttpRequest.newBuilder(URI.create(endpoint)).GET().build(),
                HttpResponse.BodyHandlers.ofString());
        assertEquals(401, anon.statusCode());
        HttpResponse<String> wrong =
            http.send(HttpRequest.newBuilder(URI.create(endpoint))
                    .header("Authorization", "Bearer nope").GET().build(),
                HttpResponse.BodyHandlers.ofString());
        assertEquals(401, wrong.statusCode());

        // an SDK client carrying the token can complete the handshake
        var transport = HttpClientSseClientTransport.builder(endpoint)
                .requestBuilder(HttpRequest.newBuilder().header("Authorization", "Bearer s3cret"))
                .build();
        var client = io.modelcontextprotocol.client.McpClient.sync(transport).build();
        try {
            client.initialize();
            assertFalse(client.listTools().tools().isEmpty());
        } finally {
            client.close();
        }
    }

    @Test
    void exportCoversOnlyKeySpecificToolsAndHonorsSettingsOverrides() {
        var tools = new KeYAgentTools();
        var tryClose = tools.agents().stream()
                .filter(t -> t.name().equals(KeYAgentTools.TOOL_TRYCLOSE)).findFirst()
                .orElseThrow();
        var addTaclet = tools.agents().stream()
                .filter(t -> t.name().equals(KeYAgentTools.TOOL_ADD_TACLET)).findFirst()
                .orElseThrow();
        var readFile = tools.agents().stream()
                .filter(t -> t.name().equals(KeYAgentTools.TOOL_READ)).findFirst()
                .orElseThrow();

        // metadata default for KeY-specific tools: AUTO tools are exported, ASK tools are not
        assertTrue(KeYMcpSseServer.isExported(tryClose));
        assertFalse(KeYMcpSseServer.isExported(addTaclet));

        // standard tools are private to the chat panel and can never be exported
        assertFalse(KeYMcpSseServer.isExported(readFile));
        LlmSettings.INSTANCE
                .setMcpExportedTools(new TreeSet<>(Set.of(KeYAgentTools.TOOL_READ)));
        assertFalse(KeYMcpSseServer.isExported(readFile),
            "a standard tool must stay off the MCP server even when explicitly selected");
        LlmSettings.INSTANCE.setMcpExportedTools(new TreeSet<>());

        // explicit exclusion wins over the metadata default for KeY-specific tools
        LlmSettings.INSTANCE
                .setMcpNotExportedTools(new TreeSet<>(Set.of(KeYAgentTools.TOOL_TRYCLOSE)));
        assertFalse(KeYMcpSseServer.isExported(tryClose));

        // explicit inclusion wins over the metadata default for KeY-specific tools
        LlmSettings.INSTANCE.setMcpNotExportedTools(new TreeSet<>());
        LlmSettings.INSTANCE
                .setMcpExportedTools(new TreeSet<>(Set.of(KeYAgentTools.TOOL_ADD_TACLET)));
        assertTrue(KeYMcpSseServer.isExported(addTaclet));
        LlmSettings.INSTANCE.setMcpExportedTools(new TreeSet<>());
    }

    @Test
    void bindingToUsedPortFails() {
        // occupy a port, then bind the server to it: start() must report the failed bind
        try (var blocker = new java.net.ServerSocket(0)) {
            int port = blocker.getLocalPort();
            server = new KeYMcpSseServer("127.0.0.1", port);
            try {
                server.start();
                throw new AssertionError("expected start() to fail on an occupied port");
            } catch (java.io.IOException expected) {
                assertFalse(server.isRunning());
            }
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }
}
