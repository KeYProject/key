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

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.key.llm.mcp.Tool;

import org.jspecify.annotations.Nullable;

/**
 * Builds the complete KeY-Agent request from the current session, proof state and user message.
 * <p>
 * This replaces the ad-hoc message assembly that used to live in the chat panel. The panel only
 * collects the raw input; everything the model needs is assembled here:
 * <ul>
 * <li>the system prompt (plus instructions of the active skill)</li>
 * <li>the proof-context block, when {@link LlmSession#isAttachProofContext()} is enabled</li>
 * <li>attached text files and multi-modal image attachments</li>
 * <li>the (capped) conversation history from the per-proof {@link LlmSession} context</li>
 * <li>the resolved user prompt</li>
 * </ul>
 *
 * @author Alexander Weigl
 */
public final class ExtendedPrompt {
    private ExtendedPrompt() {
    }

    /**
     * Assembles one chat-completion request.
     *
     * @param session the session holding endpoint/model/config and history
     * @param proof the currently selected proof (may be {@code null})
     * @param selectedNode the currently selected proof node (may be {@code null})
     * @param resolvedUserText the user message with {@code $}, {@code @} and {@code /} markup
     *        already
     *        resolved (see {@link PromptResolver})
     * @param skill an active skill whose instructions are appended to the system prompt
     */
    public static AgentRequest build(LlmSession session, @Nullable Proof proof,
            @Nullable Node selectedNode, String resolvedUserText, @Nullable Skill skill) {
        var settings = LlmSettings.INSTANCE;
        var messages = new ArrayList<Map<String, Object>>();

        messages.add(system(session, skill));
        if (session.isAttachProofContext()) {
            messages.add(contextBlock(proof, selectedNode));
        }
        List<Map<String, Object>> imageParts = new ArrayList<>();
        var attachments = buildAttachments(session, imageParts);
        if (!attachments.isEmpty()) {
            messages.add(systemBlock("Attached files", attachments));
        }

        addHistory(messages, session, settings);

        if (imageParts.isEmpty()) {
            messages.add(user(resolvedUserText));
        } else {
            messages.add(userWithImagesAndText(resolvedUserText, imageParts));
        }

        var tools = session.getMcpClient().getTools().stream().map(Tool::toMap).toList();

        Double temperature = settings.getSendTemperature() ? settings.getTemperature() : null;
        Integer maxTokens =
            settings.getSendMaxOutputTokens() ? settings.getMaxOutputTokens() : null;

        return new AgentRequest(session.getModel(), messages, tools, temperature, maxTokens,
            settings.getMaxToolRounds());
    }

    private static Map<String, Object> system(LlmSession session, @Nullable Skill skill) {
        var sb = new StringBuilder(LlmSettings.INSTANCE.getSystemPrompt());
        if (skill != null) {
            sb.append("\n\n# Active skill: ").append(skill.name()).append('\n');
            if (!skill.description().isBlank()) {
                sb.append(skill.description()).append('\n');
            }
            if (!skill.instructions().isBlank()) {
                sb.append("\nInstructions:\n").append(skill.instructions());
            }
        }
        return Map.of("role", "system", "content", sb.toString());
    }

    private static Map<String, Object> systemBlock(String title, String content) {
        return Map.of("role", "system", "content", "## " + title + "\n" + content);
    }

    private static Map<String, Object> contextBlock(@Nullable Proof proof, @Nullable Node node) {
        return Map.of("role", "system", "content",
            ProofContextCollector.contextBlock(proof, node));
    }

    private static Map<String, Object> user(String text) {
        return Map.of("role", "user", "content", text);
    }

    private static Map<String, Object> userWithImagesAndText(String text,
            List<Map<String, Object>> imageParts) {
        var parts = new ArrayList<Map<String, Object>>();
        parts.add(Map.of("type", "text", "text", text));
        parts.addAll(imageParts);
        return Map.of("role", "user", "content", parts);
    }

    /**
     * Serializes the attached text files as one block and collects image attachments as
     * base64 data-URL content parts. Bounded by the file settings.
     */
    private static String buildAttachments(LlmSession session,
            List<Map<String, Object>> imageParts) {
        var settings = LlmSettings.INSTANCE;
        int max = Math.max(0, settings.getMaxFileAttachments());
        var sb = new StringBuilder();
        int used = 0;
        for (URI uri : session.getSelectedFiles()) {
            if (used >= max) {
                sb.append("... (further attachments omitted)\n");
                break;
            }
            Path path;
            try {
                path = Path.of(uri);
            } catch (IllegalArgumentException e) {
                continue;
            }
            if (!Files.isRegularFile(path)) {
                continue;
            }
            String fileName = path.getFileName().toString();
            if (isImage(fileName)) {
                try {
                    byte[] data = Files.readAllBytes(path);
                    imageParts.add(Map.of("type", "image_url",
                        "image_url", Map.of("url",
                            "data:" + mimeType(fileName) + ";base64," + Base64.getEncoder()
                                    .encodeToString(data))));
                } catch (IOException e) {
                    sb.append("  - ").append(fileName)
                            .append(" (could not be read: ").append(e.getMessage()).append(")\n");
                }
                used++;
                continue;
            }
            if (FileAccess.isBinary(fileName)) {
                continue;
            }
            if (Files.isDirectory(path)) {
                continue;
            }
            try {
                var content = FileAccess.readText(path);
                sb.append("#### ").append(uri.getPath()).append('\n');
                sb.append("```\n").append(content).append("\n```\n");
                used++;
            } catch (IOException e) {
                sb.append("  - ").append(uri).append(" (could not be read: ").append(e.getMessage())
                        .append(")\n");
            }
        }
        return sb.toString();
    }

    private static boolean isImage(String fileName) {
        var lower = fileName.toLowerCase();
        return lower.endsWith(".png") || lower.endsWith(".jpg") || lower.endsWith(".jpeg")
                || lower.endsWith(".gif") || lower.endsWith(".webp");
    }

    private static String mimeType(String fileName) {
        var lower = fileName.toLowerCase();
        if (lower.endsWith(".png")) {
            return "image/png";
        }
        if (lower.endsWith(".jpg") || lower.endsWith(".jpeg")) {
            return "image/jpeg";
        }
        if (lower.endsWith(".gif")) {
            return "image/gif";
        }
        if (lower.endsWith(".webp")) {
            return "image/webp";
        }
        return "application/octet-stream";
    }

    /**
     * Appends the conversation history from the session context, capped by the history settings.
     */
    private static void addHistory(List<Map<String, Object>> messages, LlmSession session,
            LlmSettings settings) {
        var history = new ArrayList<>(session.getContext().getMessages());
        int maxChars = settings.getMaxHistoryChars();
        int maxMsgs = settings.getMaxHistoryMessages();

        // drop oldest messages until we stay within message and character budget
        int start = 0;
        int totalChars = 0;
        for (int i = history.size() - 1; i >= 0; i--) {
            totalChars += history.get(i).content().length();
            if (history.size() - i > maxMsgs || totalChars > maxChars) {
                start = i + 1;
                break;
            }
        }
        for (int i = start; i < history.size(); i++) {
            messages.add(history.get(i).toOpenAiMap());
        }
    }
}
