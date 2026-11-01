/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicBoolean;

import org.key_project.key.llm.mcp.FunctionDefinition;
import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.mcp.McpClient;
import org.key_project.key.llm.mcp.Tool;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import io.modelcontextprotocol.client.transport.ServerParameters;
import io.modelcontextprotocol.client.transport.StdioClientTransport;
import io.modelcontextprotocol.json.McpJsonDefaults;
import io.modelcontextprotocol.json.McpJsonMapper;
import io.modelcontextprotocol.json.TypeRef;
import io.modelcontextprotocol.spec.McpSchema;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * A standard I/O-based MCP (Model Context Protocol) client implementation.
 * <p>
 * This client communicates with an external MCP server via stdin/stdout using JSON-RPC 2.0. It is
 * a thin wrapper around the MCP Java SDK: {@link StdioClientTransport} owns the server process
 * (built from a {@link ServerParameters} command) and its protocol state, while this class keeps
 * the KeY-side {@link McpClient} view: tool discovery via {@code tools/list}, tool invocation via
 * {@code tools/call}, capability introspection and lifecycle management.
 * <p>
 * <b>Usage Example:</b>
 * <pre>{@code
 * // Start an MCP server process (e.g., a filesystem server)
 * var params = ServerParameters.builder("npx")
 *         .args("-y", "@modelcontextprotocol/server-filesystem", "/home/user/docs")
 *         .build();
 *
 * // Create the MCP client
 * McpClientStdio mcpClient = new McpClientStdio(params);
 * mcpClient.initialize();
 *
 * // Use with the agent loop
 * AgentLoop loop = new AgentLoop(session, new DefaultChatCompletionsClient());
 *
 * // Cleanup
 * mcpClient.close();
 * }</pre>
 *
 * @author Alexander Weigl
 * @version 1.0 (6/28/26)
 * @see McpClient
 * @see <a href="https://modelcontextprotocol.io/">Model Context Protocol Specification</a>
 */
public class McpClientStdio implements McpClient {
    private static final Logger logger = LoggerFactory.getLogger(McpClientStdio.class);
    private static final Gson GSON = new GsonBuilder().create();

    private final McpJsonMapper jsonMapper = McpJsonDefaults.getMapper();
    private final StdioClientTransport transport;
    private final io.modelcontextprotocol.client.McpSyncClient client;
    private final AtomicBoolean closed = new AtomicBoolean(false);

    private volatile List<Tool> tools = List.of();
    private volatile Map<String, Object> serverCapabilities = Map.of();
    private volatile boolean initialized;

    /**
     * Creates a new MCP client that communicates with the given command via stdio.
     * <p>
     * The server process is started lazily by the SDK transport on {@link #initialize()}.
     *
     * @param parameters the command (and arguments/environment) of the MCP server process
     */
    public McpClientStdio(ServerParameters parameters) {
        this.transport = new StdioClientTransport(parameters, jsonMapper);
        this.client = io.modelcontextprotocol.client.McpClient.sync(transport).build();
    }

    /**
     * Initializes the connection to the MCP server by sending an initialize request and
     * discovering available tools.
     *
     * @throws IOException if communication with the server fails
     * @throws InterruptedException if interrupted during initialization
     */
    public void initialize() throws IOException, InterruptedException {
        if (initialized) {
            return;
        }

        logger.debug("Initializing MCP connection...");

        McpSchema.InitializeResult init = client.initialize();
        McpSchema.ServerCapabilities caps = init.capabilities();
        serverCapabilities = caps == null ? Map.of()
                : jsonMapper.convertValue(caps, new TypeRef<Map<String, Object>>() {
                });
        logger.debug("Server capabilities: {}", serverCapabilities);

        var listResult = client.listTools();
        var converted = new ArrayList<Tool>(listResult.tools().size());
        for (McpSchema.Tool mcpTool : listResult.tools()) {
            try {
                converted.add(toTool(mcpTool));
            } catch (Exception e) {
                logger.warn("Could not convert discovered MCP tool '{}'", mcpTool.name(), e);
            }
        }
        tools = List.copyOf(converted);

        initialized = true;
        logger.info("MCP client initialized successfully with {} tools", tools.size());
    }

    /** Converts an SDK {@link McpSchema.Tool} into the KeY OpenAI-format {@link Tool} view. */
    private Tool toTool(McpSchema.Tool mcpTool) {
        Map<String, Object> inputSchema = mcpTool.inputSchema();
        JsonSchema schema = parseSchema(inputSchema == null ? Map.of() : inputSchema);
        return new Tool(new FunctionDefinition(mcpTool.name(), mcpTool.description(), schema));
    }

    @SuppressWarnings("unchecked")
    private static JsonSchema parseSchema(Map<String, Object> map) {
        if (map.isEmpty()) {
            return new JsonSchema("object");
        }
        var builder = JsonSchema.builder();
        Object type = map.get("type");
        builder.withType(type == null ? "object" : String.valueOf(type));
        Object properties = map.get("properties");
        if (properties instanceof Map<?, ?> props) {
            for (Map.Entry<?, ?> entry : props.entrySet()) {
                if (entry.getValue() instanceof Map<?, ?> value) {
                    builder.addProperty(String.valueOf(entry.getKey()),
                        parseSchema((Map<String, Object>) value));
                }
            }
        }
        Object required = map.get("required");
        if (required instanceof List<?> list) {
            for (Object item : list) {
                builder.addRequired(String.valueOf(item));
            }
        }
        Object description = map.get("description");
        if (description != null) {
            builder.withDescription(String.valueOf(description));
        }
        return builder.build();
    }

    @Override
    public List<Tool> getTools() {
        return tools;
    }

    @Override
    public Object callTool(String toolName, String argumentsJson) throws Exception {
        if (!initialized) {
            throw new IllegalStateException("MCP client not initialized");
        }

        logger.debug("Calling tool '{}' with args: {}", toolName, argumentsJson);

        Map<String, Object> args;
        try {
            args = GSON.fromJson(argumentsJson, Map.class);
        } catch (Exception e) {
            args = new HashMap<>();
        }
        if (args == null) {
            args = new HashMap<>();
        }

        McpSchema.CallToolResult result = client.callTool(
            McpSchema.CallToolRequest.builder(toolName).arguments(args).build());

        if (result.isError() != null && result.isError()) {
            throw new RuntimeException(
                "MCP tool call '" + toolName + "' failed: " + contentText(result));
        }
        return contentText(result);
    }

    /** Renders the content list of an MCP tool result as a plain string for the agent. */
    private static String contentText(McpSchema.CallToolResult result) {
        var content = result.content();
        if (content == null || content.isEmpty()) {
            Object structured = result.structuredContent();
            return structured == null ? "" : String.valueOf(structured);
        }
        StringBuilder sb = new StringBuilder();
        for (McpSchema.Content item : content) {
            if (item instanceof McpSchema.TextContent text) {
                sb.append(text.text());
            } else if (item instanceof McpSchema.ImageContent) {
                sb.append("[Image data]");
            } else if (item instanceof McpSchema.EmbeddedResource) {
                sb.append("[Resource data]");
            } else {
                sb.append(item);
            }
            sb.append('\n');
        }
        return sb.toString().trim();
    }

    @Override
    public boolean isClosed() {
        return closed.get();
    }

    @Override
    public void close() {
        if (!closed.compareAndSet(false, true)) {
            return;
        }
        try {
            client.close();
        } catch (Exception e) {
            logger.warn("Failed to close the MCP client cleanly", e);
        }
        try {
            transport.closeGracefully().block();
        } catch (Exception e) {
            logger.warn("Failed to close the MCP transport cleanly", e);
        }
        logger.info("MCP client closed");
    }

    /**
     * Returns the server capabilities received during initialization.
     *
     * @return a map of capability names to their values
     */
    public Map<String, Object> getServerCapabilities() {
        return new HashMap<>(serverCapabilities);
    }

    /**
     * Checks if the client has been successfully initialized.
     *
     * @return true if initialized, false otherwise
     */
    public boolean isInitialized() {
        return initialized;
    }
}
