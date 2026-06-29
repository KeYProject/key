package org.key_project.key.llm.mcp;

import java.util.List;

/**
 * MCP client interface for tool and resource access.
 * <p>
 * Implementations should handle communication with MCP servers,
 * including tool discovery, invocation, and resource retrieval.
 */
public interface McpClient {
    /**
     * Returns available tools in OpenAI API format.
     *
     * @return List of tool definitions
     */
    List<Tool> getTools();

    /**
     * Calls a tool with the given arguments.
     *
     * @param toolName  The name of the tool to call
     * @param arguments JSON string of arguments
     * @return The tool result
     * @throws Exception If the tool call fails
     */
    Object callTool(String toolName, String arguments) throws Exception;

    /**
     * Checks if the MCP client is still connected.
     *
     * @return true if connected, false otherwise
     */
    boolean isClosed();

    /**
     * Closes the MCP client and releases resources.
     */
    void close();
}
