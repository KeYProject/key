/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import java.io.IOException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Base64;
import java.util.List;
import java.util.Map;
import java.util.concurrent.Callable;
import java.util.concurrent.ConcurrentHashMap;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonObject;
import org.apache.hc.client5.http.classic.methods.HttpPost;
import org.apache.hc.client5.http.impl.classic.AbstractHttpClientResponseHandler;
import org.apache.hc.client5.http.impl.classic.HttpClients;
import org.apache.hc.core5.http.HttpEntity;
import org.apache.hc.core5.http.ParseException;
import org.apache.hc.core5.http.io.entity.EntityUtils;
import org.apache.hc.core5.http.io.entity.StringEntity;
import org.key_project.key.llm.mcp.McpClient;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Extended LLM client that supports file attachments and MCP (Model Context Protocol).
 * <p>
 * This class extends {@link LlmClient} with the following capabilities:
 * <ul>
 *   <li><b>File Attachments:</b> Automatically includes attached files from {@link LlmSession#getSelectedFiles()}
 *       as multi-modal content in messages. Supports text files and images (base64 encoded).</li>
 *   <li><b>MCP Support:</b> Integrates with MCP servers for tool calls and resource access.
 *       Handles tool result injection back into the conversation.</li>
 * </ul>
 * <p>
 * <b>Thread Safety:</b> This class is thread-safe for concurrent calls. However, the underlying
 * HTTP client is created per call to ensure proper resource management.
 *
 * @author Alexander Weigl
 * @version 1.0 (6/28/26)
 * @see LlmClient
 * @see LlmSession
 * @see LlmContext
 */
public class LlmClientExtended implements Callable<Map<String, Object>> {
    private static final Logger logger = LoggerFactory.getLogger(LlmClientExtended.class);

    private final LlmSession llmSession;
    private final LlmContext context;
    private final LlmContext.LlmMessage prompt;
    private final McpClient mcpClient;

    /**
     * Creates a new extended LLM client without MCP support.
     *
     * @param llmSession The LLM session containing API endpoint, authentication, and selected files
     * @param context The conversation context containing previous messages
     * @param message The user message to send
     */
    public LlmClientExtended(LlmSession llmSession, LlmContext context, String message) {
        this(llmSession, context, message, null);
    }

    /**
     * Creates a new extended LLM client with optional MCP support.
     *
     * @param llmSession The LLM session containing API endpoint, authentication, and selected files
     * @param context The conversation context containing previous messages
     * @param message The user message to send
     * @param mcpClient Optional MCP client for tool/resource access. May be null.
     */
    public LlmClientExtended(LlmSession llmSession, LlmContext context, String message, McpClient mcpClient) {
        this.llmSession = llmSession;
        this.context = context;
        this.prompt = new LlmContext.LlmMessage("user", message);
        this.mcpClient = mcpClient;
    }

    @Override
    public Map<String, Object> call() throws Exception {
        var url = llmSession.getApiEndpoint() + "/openai/chat/completions";
        var request = new HttpPost(url);

        request.addHeader("Authorization", "Bearer " + llmSession.getAuthToken());
        request.addHeader("Content-Type", "application/json");
        request.addHeader("Accept", "application/json");

        // Build messages with file attachments
        var messages = buildMessagesWithAttachments();

        // Build request payload
        var data = new ConcurrentHashMap<String, Object>();
        data.put("model", llmSession.getModel());
        data.put("messages", messages);

        // Add MCP tools if available
        if (mcpClient != null && !mcpClient.isClosed()) {
            var tools = mcpClient.getTools();
            if (!tools.isEmpty()) {
                data.put("tools", tools);
                data.put("tool_choice", "auto");
            }
        }

        var gson = new GsonBuilder().create();
        var stringBody = gson.toJson(data);
        request.setEntity(new StringEntity(stringBody));


        logger.debug("Sending request to: {}", url);

        try (var client = HttpClients.createDefault()) {
            var response = client.execute(request, new GsonHttpClientResponseHandler());

            // Handle tool calls if present in response
            return handleToolCallsIfPresent(response);
        }
    }
  
    /**
     * Builds the complete message list including file attachments as multi-modal content.
     * <p>
     * For each message, if there are selected files in the session, they are added as
     * additional content parts to the user message.
     *
     * @return List of messages formatted for the OpenAI API, including file attachments
     */
    private List<Map<String, Object>> buildMessagesWithAttachments() {
        var messages = new ArrayList<Map<String, Object>>();
        var allMessages = new ArrayList<>(context.getMessages());
        allMessages.add(prompt);

        boolean isFirstUserMessage = true;

        for (var msg : allMessages) {
            var messageMap = new ConcurrentHashMap<String, Object>();
            messageMap.put("role", msg.role());

            // Only add file attachments to the first user message (the prompt)
            if (isFirstUserMessage && "user".equals(msg.role()) && !llmSession.getSelectedFiles().isEmpty()) {
                var contentList = new ArrayList<Map<String, Object>>();
                
                // Add text content
                var textPart = new ConcurrentHashMap<String, Object>();
                textPart.put("type", "text");
                textPart.put("text", msg.content());
                contentList.add(textPart);

                // Add file attachments
                for (URI fileUri : llmSession.getSelectedFiles()) {
                    try {
                        var filePart = readFileAsContentPart(fileUri);
                        if (filePart != null) {
                            contentList.add(filePart);
                        }
                    } catch (IOException e) {
                        logger.warn("Could not read file {}: {}", fileUri, e.getMessage());
                    }
                }

                messageMap.put("content", contentList);
                isFirstUserMessage = false;
            } else {
                // Regular text-only message
                messageMap.put("content", msg.content());
            }

            messages.add(messageMap);
        }

        return messages;
    }

    /**
     * Reads a file from the given URI and formats it as a content part for the API.
     * <p>
     * Supports:
     * <ul>
     *   <li>Text files (.java, .txt, .md, .key, etc.) - sent as plain text</li>
     *   <li>Image files (.png, .jpg, .jpeg, .gif) - sent as base64 encoded data</li>
     * </ul>
     *
     * @param uri The URI of the file to read
     * @return A map representing the content part, or null if the file type is unsupported
     * @throws IOException If reading the file fails
     */
    private Map<String, Object> readFileAsContentPart(URI uri) throws IOException {
        var path = Path.of(uri);
        if (!Files.exists(path)) {
            logger.warn("File does not exist: {}", uri);
            return null;
        }

        String fileName = path.getFileName().toString().toLowerCase();
        byte[] content = Files.readAllBytes(path);

        // Determine file type and format accordingly
        if (isImageFile(fileName)) {
            return createImageContentPart(content, fileName);
        } else {
            // Default to text content
            return createTextContentPart(new String(content), fileName);
        }
    }

    /**
     * Checks if the given filename corresponds to a supported image file.
     */
    private boolean isImageFile(String fileName) {
        return fileName.endsWith(".png") || fileName.endsWith(".jpg") || 
               fileName.endsWith(".jpeg") || fileName.endsWith(".gif") ||
               fileName.endsWith(".webp");
    }

    /**
     * Creates a content part for an image file.
     */
    private Map<String, Object> createImageContentPart(byte[] imageData, String fileName) {
        String mimeType = getImageMimeType(fileName);
        String base64Data = Base64.getEncoder().encodeToString(imageData);
        
        var imagePart = new ConcurrentHashMap<String, Object>();
        imagePart.put("type", "image_url");
        var imageUrl = new ConcurrentHashMap<String, Object>();
        imageUrl.put("url", "data:" + mimeType + ";base64," + base64Data);
        imagePart.put("image_url", imageUrl);
        
        return imagePart;
    }

    /**
     * Gets the MIME type for an image file based on its extension.
     */
    private String getImageMimeType(String fileName) {
        if (fileName.endsWith(".png")) return "image/png";
        if (fileName.endsWith(".jpg") || fileName.endsWith(".jpeg")) return "image/jpeg";
        if (fileName.endsWith(".gif")) return "image/gif";
        if (fileName.endsWith(".webp")) return "image/webp";
        return "application/octet-stream";
    }

    /**
     * Creates a content part for a text file.
     */
    private Map<String, Object> createTextContentPart(String textContent, String fileName) {
        var textPart = new ConcurrentHashMap<String, Object>();
        textPart.put("type", "text");
        textPart.put("text", "```" + fileName + "\n" + textContent + "\n```");
        return textPart;
    }

    /**
     * Handles tool calls in the LLM response by executing them via MCP and continuing the conversation.
     * <p>
     * If the response contains tool calls and an MCP client is available, this method:
     * <ol>
     *   <li>Executes each tool call via the MCP client</li>
     *   <li>Adds the assistant's message and tool results to the context</li>
     *   <li>Makes a follow-up API call with the tool results</li>
     * </ol>
     *
     * @param response The initial response from the LLM API
     * @return The final response after handling any tool calls
     * @throws Exception If tool execution or follow-up call fails
     */
    private Map<String, Object> handleToolCallsIfPresent(Map<String, Object> response) throws Exception {
        if (mcpClient == null || mcpClient.isClosed()) {
            return response;
        }

        var choices = (List<?>) response.get("choices");
        if (choices == null || choices.isEmpty()) {
            return response;
        }

        var firstChoice = (Map<?, ?>) choices.get(0);
        var message = (Map<?, ?>) firstChoice.get("message");
        if (message == null) {
            return response;
        }

        var toolCalls = (List<?>) message.get("tool_calls");
        if (toolCalls == null || toolCalls.isEmpty()) {
            return response;
        }

        logger.info("Handling {} tool calls", toolCalls.size());

        // Add assistant's message to context
        var assistantContent = (String) message.get("content");
        if (assistantContent != null) {
            context.addMessage(new LlmContext.LlmMessage("assistant", assistantContent));
        }

        // Execute each tool call and collect results
        var toolResults = new ArrayList<Map<String, Object>>();
        for (Object toolCallObj : toolCalls) {
            var toolCall = (Map<?, ?>) toolCallObj;
            var id = (String) toolCall.get("id");
            var function = (Map<?, ?>) toolCall.get("function");
            var name = (String) function.get("name");
            var argumentsStr = (String) function.get("arguments");

            logger.debug("Executing tool: {} with args: {}", name, argumentsStr);

            try {
                var result = mcpClient.callTool(name, argumentsStr);
                var toolResult = new ConcurrentHashMap<String, Object>();
                toolResult.put("role", "tool");
                toolResult.put("tool_call_id", id);
                toolResult.put("content", result.toString());
                toolResults.add(toolResult);
                
                logger.debug("Tool {} returned: {}", name, result);
            } catch (Exception e) {
                logger.error("Tool {} failed: {}", name, e.getMessage());
                var errorResult = new ConcurrentHashMap<String, Object>();
                errorResult.put("role", "tool");
                errorResult.put("tool_call_id", id);
                errorResult.put("content", "Error: " + e.getMessage());
                toolResults.add(errorResult);
            }
        }

        // Add tool results to context
        for (var result : toolResults) {
            var content = (String) result.get("content");
            context.addMessage(new LlmContext.LlmMessage("tool", content));
        }

        // Make follow-up call with tool results
        logger.debug("Making follow-up call with tool results");
        return call();
    }

    /**
     * Simple HTTP-based response handler that parses JSON into a Map.
     */
    public static class GsonHttpClientResponseHandler
            extends AbstractHttpClientResponseHandler<Map<String, Object>> {
        @Override
        public Map<String, Object> handleEntity(HttpEntity entity) throws IOException {
            String content = null;
            try {
                content = EntityUtils.toString(entity);
            } catch (ParseException e) {
                throw new RuntimeException(e);
            }
            try {
                return new GsonBuilder().create().fromJson(content, Map.class);
            } catch (Exception e) {
                throw new RuntimeException(e);
            }
        }
    }

    public static class GsonHttpClientResponseHandlerObj
            extends AbstractHttpClientResponseHandler<JsonObject> {
        @Override
        public JsonObject handleEntity(HttpEntity entity) throws IOException {
            String content = null;
            try {
                content = EntityUtils.toString(entity);
            } catch (ParseException e) {
                throw new RuntimeException(e);
            }
            try {
                return new GsonBuilder().create().fromJson(content, JsonObject.class);
            } catch (Exception e) {
                throw new RuntimeException(e);
            }
        }
    }
}