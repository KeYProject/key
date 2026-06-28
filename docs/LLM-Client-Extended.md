# LlmClientExtended - Extended LLM Client with File Attachments and MCP Support

## Overview

`LlmClientExtended` is an enhanced version of the `LlmClient` class that adds support for:
1. **File Attachments** - Automatically include files from the session as multi-modal content
2. **MCP (Model Context Protocol)** - Integrate with MCP servers for tool calls and resource access

## Package

```java
package org.key_project.key.llm;
```

## Class Hierarchy

```
LlmClientExtended implements Callable<Map<String, Object>>
    └── McpClient (interface) - MCP client interface for tool/resource access
```

## Features

### 1. File Attachments

The extended client automatically includes files selected in the `LlmSession` as part of the message content. Files are formatted according to their type:

| File Type | Format | Example |
|-----------|--------|---------|
| Text files (.java, .txt, .md, .key) | Code block with filename | ```` ```filename.java\n...content...\n``` ```` |
| Images (.png, .jpg, .jpeg, .gif, .webp) | Base64 encoded data URL | `data:image/png;base64,...` |

### 2. MCP Support

When an `McpClient` is provided, the extended client can:
- Discover available tools from MCP servers
- Send tool definitions to the LLM API
- Execute tool calls returned by the LLM
- Inject tool results back into the conversation
- Make follow-up API calls with results

## Constructors

### Without MCP Support

```java
/**
 * Creates a new extended LLM client without MCP support.
 */
public LlmClientExtended(LlmSession llmSession, LlmContext context, String message)
```

**Parameters:**
- `llmSession` - The LLM session containing API endpoint, authentication, and selected files
- `context` - The conversation context containing previous messages
- `message` - The user message to send

### With MCP Support

```java
/**
 * Creates a new extended LLM client with optional MCP support.
 */
public LlmClientExtended(LlmSession llmSession, LlmContext context, String message, McpClient mcpClient)
```

**Parameters:**
- `llmSession` - The LLM session containing API endpoint, authentication, and selected files
- `context` - The conversation context containing previous messages
- `message` - The user message to send
- `mcpClient` - Optional MCP client for tool/resource access (may be null)

## Usage Examples

### Basic Usage with File Attachments

```java
import org.key_project.key.llm.*;
import java.net.URI;
import java.util.Set;

// Create session with API credentials
LlmSession session = new LlmSession("https://api.openai.com/v1", "sk-your-api-key");
session.setModel("gpt-4-vision-preview");

// Add files to the session
Set<URI> files = session.getSelectedFiles();
files.add(URI.create("file:///path/to/MyClass.java"));
files.add(URI.create("file:///path/to/diagram.png"));
session.setSelectedFiles(files);

// Create context and add initial messages
LlmContext context = new LlmContext();
context.addMessage(new LlmContext.LlmMessage("system", "You are a helpful coding assistant."));

// Create and execute the client
LlmClientExtended client = new LlmClientExtended(session, context, "Explain this code");
Map<String, Object> response = client.call();

// Process response
var choices = (List<?>) response.get("choices");
var firstChoice = (Map<?, ?>) choices.get(0);
var message = (Map<?, ?>) firstChoice.get("message");
String content = (String) message.get("content");
System.out.println(content);
```

### Usage with MCP Server

```java
import org.key_project.key.llm.*;

// Start an MCP server process
ProcessBuilder pb = new ProcessBuilder(
    "npx", "-y", "@modelcontextprotocol/server-filesystem", "/home/user/docs"
);
Process mcpServer = pb.start();

// Create and initialize MCP client
McpClientStdio mcpClient = new McpClientStdio(mcpServer);
mcpClient.initialize();

// Create session (no files needed when using MCP)
LlmSession session = new LlmSession("https://api.openai.com/v1", "sk-your-api-key");
LlmContext context = new LlmContext();

// Create client with MCP support
LlmClientExtended client = new LlmClientExtended(session, context, 
    "List the files in my documents folder", mcpClient);

// Execute and handle tool calls automatically
Map<String, Object> response = client.call();

// Cleanup
mcpClient.close();
```

### Combined Usage (Files + MCP)

```java
// Setup session with both files and MCP
LlmSession session = new LlmSession("https://api.openai.com/v1", "sk-your-api-key");
session.setSelectedFiles(Set.of(URI.create("file:///path/to/code.java")));

// Initialize MCP client for additional capabilities
ProcessBuilder pb = new ProcessBuilder("npx", "-y", "@modelcontextprotocol/server-git", "/path/to/repo");
McpClientStdio mcpClient = new McpClientStdio(pb.start());
mcpClient.initialize();

// Use both features together
LlmContext context = new LlmContext();
LlmClientExtended client = new LlmClientExtended(session, context, 
    "Review this code and check the git history for recent changes", mcpClient);

Map<String, Object> response = client.call();
mcpClient.close();
```

## McpClient Interface

The `McpClient` interface defines the contract for MCP implementations:

```java
public interface McpClient {
    /** Returns available tools in OpenAI API format. */
    List<Map<String, Object>> getToolsAsOpenAiFormat();
    
    /** Calls a tool with the given arguments. */
    Object callTool(String toolName, String arguments) throws Exception;
    
    /** Checks if the MCP client is still connected. */
    boolean isClosed();
    
    /** Closes the MCP client and releases resources. */
    void close();
}
```

## McpClientStdio Class

`McpClientStdio` is a reference implementation that communicates with MCP servers via stdin/stdout using JSON-RPC 2.0.

### Constructor

```java
public McpClientStdio(Process process) throws IOException
```

### Methods

| Method | Description |
|--------|-------------|
| `initialize()` | Initializes connection and discovers tools |
| `isInitialized()` | Returns true if successfully initialized |
| `getServerCapabilities()` | Returns server capabilities map |
| `close()` | Closes the connection and terminates the process |

### Supported MCP Operations

- `tools/list` - Discover available tools
- `tools/call` - Invoke a tool
- `resources/list` - List available resources
- `resources/read` - Read resource content

## Architecture

### Message Flow with File Attachments

```
┌─────────────┐     ┌──────────────────┐     ┌───────────────┐
│ LlmSession  │────▶│ LlmClientExtended│────▶│ OpenAI API    │
│ - files     │     │ - attachments    │     │ - gpt-4-vision│
└─────────────┘     │ - multipart msg  │     └───────────────┘
                    └──────────────────┘
```

### Message Flow with MCP

```
┌─────────────┐     ┌──────────────────┐     ┌───────────────┐
│ McpClient   │◀───▶│ LlmClientExtended│◀───▶│ OpenAI API    │
│ - tools     │     │ - tool handling  │     │ - tool_calls  │
└─────────────┘     └──────────────────┘     └───────────────┘
       │                    │                        │
       │                    └────────────────────────┘
       │                           (follow-up)
       ▼
  Execute Tool
  Return Result
```

## Thread Safety

- `LlmClientExtended` is thread-safe for concurrent `call()` invocations
- Each call creates a new HTTP client instance
- The `McpClient` implementation should be thread-safe if used concurrently
- `ConcurrentHashMap` is used for internal data structures

## Error Handling

| Scenario | Behavior |
|----------|----------|
| File not found | Warning logged, file skipped |
| Unsupported file type | Treated as text content |
| MCP server timeout | IOException after 30 seconds |
| Tool execution failure | Error message returned to LLM |
| MCP process terminated | `isClosed()` returns true, tools disabled |

## Dependencies

The following libraries are required:

- Apache HttpClient 5.x (`org.apache.httpcomponents.client5`)
- Gson (`com.google.gson`)
- SLF4J (`org.slf4j`)

## Best Practices

1. **Always close MCP clients** - Use try-with-resources or finally blocks
2. **Limit file count** - Too many attachments increase token usage
3. **Initialize before use** - Call `mcpClient.initialize()` before first use
4. **Check isClosed()** - Verify MCP connection before operations
5. **Handle exceptions** - Tool calls may fail; errors are gracefully returned to LLM

## Related Classes

- `LlmClient` - Original basic LLM client
- `LlmSession` - Session configuration (API endpoint, auth, files)
- `LlmContext` - Conversation history management
- `McpClientStdio` - Reference MCP implementation

## Author

@author Alexander Weigl

## Version

@version 1.0 (6/28/26)

## License

This file is part of KeY and is licensed under the GNU General Public License Version 2 (GPL-2.0-only).