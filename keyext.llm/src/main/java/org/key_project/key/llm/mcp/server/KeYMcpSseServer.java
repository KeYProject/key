/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.server;

import java.io.IOException;
import java.net.InetSocketAddress;
import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import org.key_project.key.llm.AgentLoop;
import org.key_project.key.llm.LlmSettings;
import org.key_project.key.llm.ToolDispatcher;
import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.Tool;

import com.sun.net.httpserver.HttpServer;
import io.modelcontextprotocol.json.McpJsonDefaults;
import io.modelcontextprotocol.server.McpServer;
import io.modelcontextprotocol.server.McpServerFeatures;
import io.modelcontextprotocol.server.McpSyncServer;
import io.modelcontextprotocol.spec.McpSchema;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Exposes the KeY-Agent tool set as an MCP (Model Context Protocol) server over HTTP with
 * Server-Sent Events (SSE), so other processes (MCP clients such as Claude Desktop, IDEs or
 * scripts) can discover and invoke KeY's proof tools.
 * <p>
 * The server is built on the MCP Java SDK: {@link McpServer} provides all protocol state (version
 * negotiation, JSON-RPC framing, tool dispatch), while {@link SseHttpServerTransportProvider}
 * implements the SSE transport on the JDK's {@link HttpServer}. Every tool of the
 * {@link KeYAgentTools} registry that is currently exported (see the per-tool export permission
 * in {@link LlmSettings}) is registered as an MCP tool; tool calls are executed through the shared
 * {@link ToolDispatcher}, i.e. serialized against tool calls of the GUI agent.
 * <p>
 * The server binds to a host/port (default {@code 127.0.0.1} on an ephemeral port) and can
 * optionally require a static bearer token on every request. Lifecycle observers are notified via
 * {@link Listener}; the GUI uses that to reflect the server state in the status line.
 *
 * @author Alexander Weigl
 */
public class KeYMcpSseServer {

    /** The server name reported to MCP clients. */
    public static final String SERVER_NAME = "KeY MCP server";

    /** The server version reported to MCP clients. */
    public static final String SERVER_VERSION = "1.0";

    private static final Logger logger = LoggerFactory.getLogger(KeYMcpSseServer.class);

    private final String host;
    private final int port;
    private final @Nullable String token;
    private final KeYAgentTools tools;
    private final List<Listener> listeners = new CopyOnWriteArrayList<>();

    private HttpServer httpServer;
    private McpSyncServer mcpServer;
    private SseHttpServerTransportProvider transport;
    private ExecutorService executor;

    /**
     * Creates the server bound to the loopback interface on an ephemeral port, without
     * authentication.
     *
     * @param host the host interface to bind to ({@code 127.0.0.1} recommended)
     * @param port the port to bind to, or {@code 0} for a free ephemeral port
     */
    public KeYMcpSseServer(String host, int port) {
        this(host, port, null);
    }

    /**
     * Creates the server with the given host, port and optional bearer token.
     *
     * @param host the host interface to bind to ({@code 127.0.0.1} recommended)
     * @param port the port to bind to, or {@code 0} for a free ephemeral port
     * @param token optional static bearer token, or {@code null} for unauthenticated access
     */
    public KeYMcpSseServer(String host, int port, @Nullable String token) {
        this(host, port, token, new KeYAgentTools());
    }

    /**
     * Creates the server over the given tool registry (used by tests to register test-only tools).
     *
     * @param host the host interface to bind to ({@code 127.0.0.1} recommended)
     * @param port the port to bind to, or {@code 0} for a free ephemeral port
     * @param token optional static bearer token, or {@code null} for unauthenticated access
     * @param tools the tool registry to expose
     */
    public KeYMcpSseServer(String host, int port, @Nullable String token, KeYAgentTools tools) {
        this.host = host;
        this.port = port;
        this.token = token;
        this.tools = tools;
    }

    /** Convenience factory reading the current {@link LlmSettings}. */
    public static KeYMcpSseServer fromSettings() {
        var s = LlmSettings.INSTANCE;
        return new KeYMcpSseServer(s.getMcpServerHost(), s.getMcpServerPort(),
            s.getMcpServerToken());
    }

    /**
     * Starts the server: binds the HTTP server, builds the MCP server(s) from the currently
     * exported tools and notifies the listeners.
     *
     * @throws IOException if binding the HTTP server fails (e.g. the port is already in use)
     */
    public synchronized void start() throws IOException {
        if (isRunning()) {
            return;
        }
        transport = new SseHttpServerTransportProvider(McpJsonDefaults.getMapper(), token);
        mcpServer = McpServer.sync(transport)
                .serverInfo(SERVER_NAME, SERVER_VERSION)
                .capabilities(McpSchema.ServerCapabilities.builder().tools(true).build())
                .tools(buildToolSpecs())
                .build();
        httpServer = HttpServer.create(new InetSocketAddress(host, port), 0);
        executor = Executors.newCachedThreadPool(r -> {
            var t = new Thread(r, "key-mcp-sse");
            t.setDaemon(true);
            return t;
        });
        httpServer.setExecutor(executor);
        httpServer.createContext(SseHttpServerTransportProvider.SSE_ENDPOINT, transport);
        httpServer.createContext(SseHttpServerTransportProvider.MESSAGE_ENDPOINT, transport);
        httpServer.start();
        logger.info("KeY MCP server listening on {}", getSseEndpoint());
        for (var listener : listeners) {
            listener.started(this);
        }
    }

    /** Stops the server, closes all sessions and releases the bound port. Idempotent. */
    public synchronized void stop() {
        if (!isRunning()) {
            return;
        }
        var hs = httpServer;
        var ms = mcpServer;
        var tr = transport;
        var ex = executor;
        httpServer = null;
        mcpServer = null;
        transport = null;
        executor = null;
        try {
            tr.closeGracefully().block(Duration.ofSeconds(1));
        } catch (Exception e) {
            logger.debug("Graceful MCP shutdown did not complete in time", e);
        }
        try {
            ms.close();
        } catch (Exception e) {
            logger.warn("Failed to close the MCP server cleanly", e);
        }
        if (hs != null) {
            hs.stop(0);
        }
        if (ex != null) {
            ex.shutdownNow();
        }
        logger.info("KeY MCP server stopped");
        for (var listener : listeners) {
            listener.stopped(this);
        }
    }

    /** Whether the server is currently running. */
    public synchronized boolean isRunning() {
        return httpServer != null && mcpServer != null;
    }

    /**
     * The SSE endpoint clients connect to, e.g. {@code http://127.0.0.1:12345/sse}, or
     * {@code null} while the server is not running.
     */
    public @Nullable String getSseEndpoint() {
        if (!isRunning()) {
            return null;
        }
        String h = host == null || host.isBlank() || "0.0.0.0".equals(host) ? "127.0.0.1" : host;
        return "http://" + h + ":" + httpServer.getAddress().getPort()
            + SseHttpServerTransportProvider.SSE_ENDPOINT;
    }

    // ---------------------------------------------------------------- tool registry mapping

    private List<McpServerFeatures.SyncToolSpecification> buildToolSpecs() {
        var specs = new ArrayList<McpServerFeatures.SyncToolSpecification>();
        for (var tool : tools.agents()) {
            if (!isExported(tool)) {
                continue;
            }
            specs.add(new McpServerFeatures.SyncToolSpecification(tool.mcpTool(),
                (exchange, request) -> call(tool, request)));
        }
        logger.info("Exporting {} of {} tools to the MCP server", specs.size(),
            tools.agents().size());
        return specs;
    }

    /**
     * Effective export permission of a tool: the per-tool user overrides in {@link LlmSettings}
     * win, otherwise a tool is exported when it runs without user approval by default.
     */
    static boolean isExported(AgentTool tool) {
        return LlmSettings.INSTANCE.isExportedToMCP(tool.name(), isAutoApproved(tool));
    }

    private static boolean isAutoApproved(AgentTool tool) {
        var settings = LlmSettings.INSTANCE;
        if (settings.getToolsDisabled().contains(tool.name())) {
            return false;
        }
        if (settings.getAllowedToolsWithApproval().contains(tool.name())) {
            return false;
        }
        if (settings.getAllowedToolsWithoutApproval().contains(tool.name())) {
            return true;
        }
        return tool.approval() == Tool.ApprovalRequirement.AUTO;
    }

    /** Invokes a tool under the shared tool-dispatch lock and maps the outcome to an MCP result. */
    private static McpSchema.CallToolResult call(AgentTool tool,
            McpSchema.CallToolRequest request) {
        Object result;
        boolean isError = false;
        try {
            result = ToolDispatcher.INSTANCE.callSynchronized(() -> {
                try {
                    return tool.call(request.arguments());
                } catch (Exception e) {
                    throw new RuntimeException(e);
                }
            });
        } catch (Exception e) {
            isError = true;
            Throwable cause = e.getCause() != null ? e.getCause() : e;
            result = "Tool '" + tool.name() + "' failed: " + cause.getMessage();
        }
        return McpSchema.CallToolResult.builder()
                .content(List.of(new McpSchema.TextContent(AgentLoop.stringify(result))))
                .isError(isError)
                .build();
    }

    // ---------------------------------------------------------------- lifecycle listeners

    /** Observer of the server lifecycle (used by the status-line indicator of the GUI). */
    public interface Listener {
        /** Called when the server has started and is reachable. */
        void started(KeYMcpSseServer server);

        /** Called when the server has stopped and the port has been released. */
        void stopped(KeYMcpSseServer server);
    }

    /** Adds a lifecycle listener. */
    public void addListener(Listener listener) {
        listeners.add(listener);
    }

    /** Removes a lifecycle listener. */
    public void removeListener(Listener listener) {
        listeners.remove(listener);
    }
}
