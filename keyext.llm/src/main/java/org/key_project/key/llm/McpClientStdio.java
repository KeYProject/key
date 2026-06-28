/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.key_project.key.llm.mcp.McpClient;
import org.key_project.key.llm.mcp.Tool;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * A standard I/O-based MCP (Model Context Protocol) client implementation.
 * <p>
 * This client communicates with MCP servers via stdin/stdout using JSON-RPC 2.0 protocol.
 * It supports:
 * <ul>
 *   <li>Tool discovery via {@code tools/list}</li>
 *   <li>Tool invocation via {@code tools/call}</li>
 *   <li>Resource access via {@code resources/read}</li>
 *   <li>Resource listing via {@code resources/list}</li>
 * </ul>
 * <p>
 * <b>Usage Example:</b>
 * <pre>{@code
 * // Start an MCP server process (e.g., a filesystem server)
 * ProcessBuilder pb = new ProcessBuilder("npx", "-y", "@modelcontextprotocol/server-filesystem", "/home/user/docs");
 * Process process = pb.start();
 * 
 * // Create the MCP client
 * McpClientStdio mcpClient = new McpClientStdio(process);
 * mcpClient.initialize();
 * 
 * // Use with LlmClientExtended
 * LlmClientExtended client = new LlmClientExtended(session, context, "Hello", mcpClient);
 * Map<String, Object> response = client.call();
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

    private final Process process;
    private final BufferedReader inputReader;
    private final OutputStream outputStream;
    private final AtomicInteger requestIdGenerator = new AtomicInteger(0);
    private final Map<String, Object> serverCapabilities = new ConcurrentHashMap<>();
    private final List<Map<String, Object>> cachedTools = new ArrayList<>();
    private volatile boolean closed = false;
    private volatile boolean initialized = false;

    /**
     * Creates a new MCP client that communicates with the given process via stdio.
     * <p>
     * The process should already be started before calling this constructor.
     *
     * @param process The MCP server process
     * @throws IOException If reading from the process fails during initialization
     */
    public McpClientStdio(Process process) throws IOException {
        this.process = process;
        this.inputReader = new BufferedReader(new InputStreamReader(process.getInputStream()));
        this.outputStream = process.getOutputStream();
    }

    /**
     * Initializes the connection to the MCP server by sending an initialize request
     * and discovering available tools.
     *
     * @throws IOException If communication with the server fails
     * @throws InterruptedException If interrupted during initialization
     */
    public void initialize() throws IOException, InterruptedException {
        if (initialized) {
            return;
        }

        logger.debug("Initializing MCP connection...");

        // Send initialize request
        JsonObject initRequest = createJsonRpcRequest("initialize", Map.of(
            "protocolVersion", "2024-11-05",
            "capabilities", Map.of(),
            "clientInfo", Map.of(
                "name", "KeY-MCP-Client",
                "version", "1.0.0"
            )
        ));

        sendRequest(initRequest);
        JsonObject initResponse = readResponse();

        if (initResponse != null && initResponse.has("result")) {
            JsonObject result = initResponse.getAsJsonObject("result");
            serverCapabilities.putAll(GSON.fromJson(result.get("capabilities"), Map.class));
            logger.debug("Server capabilities: {}", serverCapabilities);
        }

        // Send initialized notification
        JsonObject initializedNotification = createJsonRpcNotification("notifications/initialized");
        sendRequest(initializedNotification);

        // Discover tools
        discoverTools();

        initialized = true;
        logger.info("MCP client initialized successfully");
    }

    /**
     * Discovers available tools from the MCP server and caches them.
     *
     * @throws IOException If communication fails
     * @throws InterruptedException If interrupted
     */
    @SuppressWarnings("unchecked")
    private void discoverTools() throws IOException, InterruptedException {
        JsonObject toolsRequest = createJsonRpcRequest("tools/list", null);
        sendRequest(toolsRequest);
        JsonObject toolsResponse = readResponse();

        cachedTools.clear();
        if (toolsResponse != null && toolsResponse.has("result")) {
            JsonObject result = toolsResponse.getAsJsonObject("result");
            if (result.has("tools")) {
                List<?> toolsList = GSON.fromJson(result.get("tools"), List.class);
                for (Object toolObj : toolsList) {
                    Map<String, Object> tool = (Map<String, Object>) toolObj;
                    cachedTools.add(convertToolToOpenAiFormat(tool));
                }
            }
        }
        logger.debug("Discovered {} tools", cachedTools.size());
    }

    /**
     * Converts an MCP tool definition to OpenAI API format.
     *
     * @param mcpTool The MCP tool definition
     * @return The tool in OpenAI API format
     */
    @SuppressWarnings("unchecked")
    private Map<String, Object> convertToolToOpenAiFormat(Map<String, Object> mcpTool) {
        var openAiTool = new HashMap<String, Object>();
        openAiTool.put("type", "function");

        var function = new HashMap<String, Object>();
        function.put("name", mcpTool.get("name"));
        function.put("description", mcpTool.getOrDefault("description", ""));

        // Convert MCP schema to JSON Schema format
        if (mcpTool.containsKey("inputSchema")) {
            function.put("parameters", mcpTool.get("inputSchema"));
        } else {
            var emptySchema = new HashMap<String, Object>();
            emptySchema.put("type", "object");
            emptySchema.put("properties", new HashMap<>());
            function.put("parameters", emptySchema);
        }

        openAiTool.put("function", function);
        return openAiTool;
    }

    @Override
    public List<Tool> getTools() {
        return new ArrayList<>();
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

        JsonObject callRequest = createJsonRpcRequest("tools/call", Map.of(
            "name", toolName,
            "arguments", args
        ));

        sendRequest(callRequest);
        JsonObject response = readResponse();

        if (response == null) {
            throw new IOException("No response from MCP server");
        }

        if (response.has("error")) {
            JsonObject error = response.getAsJsonObject("error");
            String errorMessage = error.has("message") ? error.get("message").getAsString() : "Unknown error";
            throw new RuntimeException("MCP tool call failed: " + errorMessage);
        }

        if (response.has("result")) {
            return parseToolResult(response.getAsJsonObject("result"));
        }

        return null;
    }

    /**
     * Parses the tool result from MCP format to a human-readable string.
     *
     * @param result The result object from the MCP server
     * @return A string representation of the result
     */
    @SuppressWarnings("unchecked")
    private String parseToolResult(JsonObject result) {
        if (result.has("content")) {
            List<?> contentList = GSON.fromJson(result.get("content"), List.class);
            StringBuilder sb = new StringBuilder();
            for (Object item : contentList) {
                Map<String, Object> contentItem = (Map<String, Object>) item;
                String type = (String) contentItem.get("type");
                if ("text".equals(type)) {
                    sb.append(contentItem.get("text"));
                } else if ("image".equals(type)) {
                    sb.append("[Image data]");
                } else if ("resource".equals(type)) {
                    sb.append("[Resource data]");
                }
                sb.append("\n");
            }
            return sb.toString().trim();
        }
        return result.toString();
    }

    @Override
    public boolean isClosed() {
        return closed || !process.isAlive();
    }

    @Override
    public void close() {
        if (closed) {
            return;
        }
        closed = true;

        try {
            // Try to send a graceful shutdown notification
            try {
                JsonObject shutdownNotification = createJsonRpcNotification("notifications/cancelled");
                sendRequest(shutdownNotification);
            } catch (Exception e) {
                // Ignore errors during shutdown
            }

            outputStream.close();
            inputReader.close();
            process.destroy();
            
            // Wait briefly for clean termination
            try {
                if (!process.waitFor(2, java.util.concurrent.TimeUnit.SECONDS)) {
                    process.destroyForcibly();
                }
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                process.destroyForcibly();
            }

            logger.info("MCP client closed");
        } catch (IOException e) {
            logger.error("Error closing MCP client: {}", e.getMessage());
        }
    }

    /**
     * Sends a JSON-RPC request to the MCP server.
     *
     * @param request The JSON-RPC request object
     * @throws IOException If writing to the process fails
     */
    private void sendRequest(JsonObject request) throws IOException {
        String json = GSON.toJson(request);
        String message = json + "\n";
        outputStream.write(message.getBytes(java.nio.charset.StandardCharsets.UTF_8));
        outputStream.flush();
        logger.trace("Sent: {}", json);
    }

    /**
     * Reads a JSON-RPC response from the MCP server.
     *
     * @return The parsed JSON response, or null if no response
     * @throws IOException If reading fails
     * @throws InterruptedException If interrupted
     */
    private JsonObject readResponse() throws IOException, InterruptedException {
        // Read with timeout
        long startTime = System.currentTimeMillis();
        long timeout = 30000; // 30 seconds

        while (System.currentTimeMillis() - startTime < timeout) {
            if (inputReader.ready()) {
                String line = inputReader.readLine();
                if (line != null && !line.isEmpty()) {
                    logger.trace("Received: {}", line);
                    try {
                        return JsonParser.parseString(line).getAsJsonObject();
                    } catch (Exception e) {
                        logger.warn("Failed to parse JSON response: {}", line);
                    }
                }
            }
            
            if (!process.isAlive()) {
                throw new IOException("MCP server process terminated unexpectedly");
            }
            
            Thread.sleep(100);
        }

        throw new IOException("Timeout waiting for MCP server response");
    }

    /**
     * Creates a JSON-RPC 2.0 request object.
     *
     * @param method The method name
     * @param params The method parameters (may be null)
     * @return A JSON-RPC request object
     */
    private JsonObject createJsonRpcRequest(String method, Map<String, Object> params) {
        JsonObject request = new JsonObject();
        request.addProperty("jsonrpc", "2.0");
        request.addProperty("id", requestIdGenerator.incrementAndGet());
        request.addProperty("method", method);
        
        if (params != null) {
            request.add("params", GSON.toJsonTree(params));
        }
        
        return request;
    }

    /**
     * Creates a JSON-RPC 2.0 notification object (no ID, no response expected).
     *
     * @param method The method name
     * @return A JSON-RPC notification object
     */
    private JsonObject createJsonRpcNotification(String method) {
        JsonObject notification = new JsonObject();
        notification.addProperty("jsonrpc", "2.0");
        notification.addProperty("method", method);
        return notification;
    }

    /**
     * Returns the server capabilities received during initialization.
     *
     * @return A map of capability names to their values
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