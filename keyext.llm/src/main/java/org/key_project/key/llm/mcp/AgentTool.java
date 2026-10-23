/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp;

import java.util.Map;
import java.util.Objects;

import com.google.gson.GsonBuilder;
import org.jspecify.annotations.Nullable;

/**
 * The modular unit of the KeY-Agent tool set: one tool with its metadata (name, description,
 * parameter schema, approval requirement) and the logic that executes a call.
 * <p>
 * Tools are contributed by {@link AgentToolProvider}s that are discovered through the Java
 * {@link java.util.ServiceLoader} (service file {@code META-INF/services/...AgentToolProvider}).
 * This keeps the tool set dynamic: plugins and test suites can register additional tools, and
 * every registered tool is picked up automatically by {@link KeYAgentTools}.
 * <p>
 * The metadata of a tool is available programmatically - {@link #name()}, {@link #description()},
 * {@link #parameters()}, {@link #approval()} as well as the serialized forms {@link #asTool()}
 * (OpenAI tool format, used by the MCP clients) and {@link #toMarkdown()} (human-readable, used
 * by the {@code list_tools} documentation tool).
 *
 * @author Alexander Weigl
 */
public interface AgentTool {

    /** The unique tool name as advertised to the model. */
    String name();

    /** A short explanation of what the tool does, shown to the model and in the settings UI. */
    String description();

    /** The JSON schema of the tool's {@code arguments} object (empty object when no parameters). */
    default JsonSchema parameters() {
        return JsonSchema.builder().withType("object").build();
    }

    /** The default approval requirement of this tool (AUTO = run without asking). */
    default Tool.ApprovalRequirement approval() {
        return Tool.ApprovalRequirement.AUTO;
    }

    /**
     * Executes the tool with the parsed {@code arguments}.
     *
     * @param arguments the tool arguments (already parsed from JSON)
     * @return the tool result (usually a {@link String}; may be any object the outer loop
     *         serializes into the chat)
     * @throws Exception when the call fails
     */
    Object call(Map<String, Object> arguments) throws Exception;

    /** Converts this tool to the OpenAI tool format used by the MCP clients. */
    default Tool asTool() {
        return new Tool(new FunctionDefinition(name(), description(), parameters()), approval());
    }

    /** Renders this tool as a Markdown block for the tools documentation. */
    default String toMarkdown() {
        var sb = new StringBuilder();
        sb.append("### `").append(name()).append("` (").append(approval()).append(")\n\n");
        sb.append(description()).append('\n');
        var parameters = parameters();
        if (parameters != null && parameters.properties() != null
                && !parameters.properties().isEmpty()) {
            sb.append("\n**Parameters:**\n");
            parameters.properties().forEach((n, s) -> {
                sb.append("- `").append(n).append('`');
                if (s != null) {
                    sb.append(" (").append(s.schemaType() == null ? "object" : s.schemaType())
                            .append(')');
                    if (s.description() != null) {
                        sb.append(" - ").append(s.description());
                    }
                }
                sb.append('\n');
            });
        }
        if (parameters != null && parameters.required() != null
                && !parameters.required().isEmpty()) {
            sb.append("\nRequired: ").append(String.join(", ", parameters.required())).append('\n');
        }
        return sb.toString().stripTrailing();
    }

    // ------------------------------------------------------------------- factory and helpers

    /**
     * Creates a tool from a plain call body - the typical way a provider defines its tools.
     *
     * @param name the unique tool name
     * @param description the tool explanation
     * @param approval the default approval requirement
     * @param parameters the argument schema
     * @param body the call implementation
     */
    static AgentTool tool(String name, String description, Tool.ApprovalRequirement approval,
            JsonSchema parameters, ToolCall body) {
        Objects.requireNonNull(name, "tool name");
        Objects.requireNonNull(body, "tool body");
        Objects.requireNonNull(description, "tool description");
        return new AgentTool() {
            @Override
            public String name() {
                return name;
            }

            @Override
            public String description() {
                return description;
            }

            @Override
            public JsonSchema parameters() {
                return parameters;
            }

            @Override
            public Tool.ApprovalRequirement approval() {
                return approval;
            }

            @Override
            public Object call(Map<String, Object> arguments) throws Exception {
                return body.call(arguments);
            }
        };
    }

    /**
     * Like {@link #tool(String, String, Tool.ApprovalRequirement, JsonSchema, ToolCall)} with
     * AUTO approval.
     */
    static AgentTool tool(String name, String description, JsonSchema parameters, ToolCall body) {
        return tool(name, description, Tool.ApprovalRequirement.AUTO, parameters, body);
    }

    /** Like {@link #tool(String, String, JsonSchema, ToolCall)} with an empty parameter schema. */
    static AgentTool tool(String name, String description, ToolCall body) {
        return tool(name, description, Tool.ApprovalRequirement.AUTO,
            JsonSchema.builder().withType("object").build(), body);
    }

    /** Builds an object-typed parameter schema from alternating key/value pairs. */
    static JsonSchema schema(Object... keyValue) {
        var builder = JsonSchema.builder().withType("object");
        for (int i = 0; i + 1 < keyValue.length; i += 2) {
            builder.addProperty((String) keyValue[i], (JsonSchema) keyValue[i + 1]);
        }
        return builder.build();
    }

    // ------------------------------------------------------------- argument parsing helpers

    /** Parses the JSON {@code arguments} string of a tool call into a map. */
    static Map<String, Object> parseArgs(String arguments) {
        if (arguments == null || arguments.isBlank()) {
            return Map.of();
        }
        try {
            var parsed = new GsonBuilder().create().fromJson(arguments, Map.class);
            return parsed == null ? Map.of() : parsed;
        } catch (Exception e) {
            return Map.of();
        }
    }

    @SuppressWarnings("unchecked")
    static @Nullable String stringArg(Map<String, Object> args, String key) {
        Object v = args.get(key);
        return v == null ? null : String.valueOf(v);
    }

    static boolean boolArg(Map<String, Object> args, String key) {
        Object v = args.get(key);
        return (v instanceof Boolean b && b) || "true".equals(v);
    }

    static @Nullable Integer intArg(Map<String, Object> args, String key) {
        Object v = args.get(key);
        if (v instanceof Number n) {
            return n.intValue();
        }
        if (v != null) {
            try {
                return Integer.parseInt(String.valueOf(v).trim());
            } catch (NumberFormatException e) {
                return null;
            }
        }
        return null;
    }

    /** The body of a tool call: receives the parsed arguments and returns the result. */
    @FunctionalInterface
    interface ToolCall {
        Object call(Map<String, Object> arguments) throws Exception;
    }
}
