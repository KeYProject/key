/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.io.PrintStream;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CountDownLatch;

import io.modelcontextprotocol.json.McpJsonDefaults;
import io.modelcontextprotocol.server.McpServer;
import io.modelcontextprotocol.server.transport.StdioServerTransportProvider;
import io.modelcontextprotocol.spec.McpSchema;

/**
 * A minimal MCP server over stdio, launched as a separate JVM by {@link McpClientStdioTest}. It is
 * built on the SDK's {@link StdioServerTransportProvider} and serves a single echo tool until the
 * process is terminated by the client.
 */
public final class TestMcpStdioServerMain {

    /** The single tool this server advertises. */
    public static final String ECHO_TOOL = "stdio_echo";

    private TestMcpStdioServerMain() {
    }

    public static void main(String[] args) throws Exception {
        // Stdout is the JSON-RPC wire channel, so nothing else may write to it. The classpath
        // logback.xml binds its console appender to System.out on first LoggerFactory use, hence
        // the real stdout is captured and System.out redirected to stderr before any logger is
        // touched; the transport then writes its responses to the explicitly passed stdout stream.
        PrintStream stdioOut = System.out;
        System.setOut(System.err);
        var transport =
            new StdioServerTransportProvider(McpJsonDefaults.getMapper(), System.in, stdioOut);
        McpServer.sync(transport)
                .serverInfo("KeY Test Stdio MCP Server", "1.0")
                .capabilities(McpSchema.ServerCapabilities.builder().tools(true).build())
                .toolCall(
                    McpSchema.Tool.builder(ECHO_TOOL)
                            .description("echoes its x argument")
                            .inputSchema(Map.of("type", "object",
                                "properties", Map.of("x", Map.of("type", "string"))))
                            .build(),
                    (exchange, request) -> {
                        Object x = request.arguments().get("x");
                        return McpSchema.CallToolResult.builder()
                                .content(List.of(new McpSchema.TextContent("stdio:" + x)))
                                .build();
                    })
                .build();
        new CountDownLatch(1).await();
    }
}
