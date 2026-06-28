package org.key_project.key.llm.mcp;

import com.fasterxml.jackson.annotation.JsonProperty;

/**
 * Represents a tool definition in OpenAI API format.
 *
 * @param type     The type of the tool (e.g., "function")
 * @param function The function definition
 * @author Alexander Weigl
 * @version 1 (28.06.26)
 */
public record Tool(
        @JsonProperty("type") String type,
        @JsonProperty("function") FunctionDefinition function
) {
    /**
     * Creates a new Tool with type "function".
     *
     * @param function The function definition
     */
    public Tool(FunctionDefinition function) {
        this("function", function);
    }

    /**
     * Converts this Tool to a Map representation.
     *
     * @return Map containing the tool definition
     */
    public java.util.Map<String, Object> toMap() {
        return java.util.Map.of(
                "type", type,
                "function", function.toMap()
        );
    }
}