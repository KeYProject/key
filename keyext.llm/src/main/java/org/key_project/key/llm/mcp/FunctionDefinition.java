package org.key_project.key.llm.mcp;

import com.fasterxml.jackson.annotation.JsonProperty;

import java.util.Map;

/**
 * Represents a function definition in OpenAI tool specification.
 *
 * @param name        The name of the function
 * @param description Optional description of what the function does
 * @param parameters  JSON Schema object defining the function's parameters
 * @author Alexander Weigl
 * @version 1 (28.06.26)
 */
public record FunctionDefinition(
        @JsonProperty("name") String name,
        @JsonProperty("description") String description,
        @JsonProperty("parameters") JsonSchema parameters
) {
    /**
     * Creates a new FunctionDefinition with minimal required fields.
     *
     * @param name The name of the function
     */
    public FunctionDefinition(String name) {
        this(name, null, new JsonSchema());
    }

    /**
     * Creates a new FunctionDefinition with name and description.
     *
     * @param name        The name of the function
     * @param description Description of what the function does
     */
    public FunctionDefinition(String name, String description) {
        this(name, description, new JsonSchema());
    }

    /**
     * Converts this FunctionDefinition to a Map representation.
     *
     * @return Map containing the function definition
     */
    public Map<String, Object> toMap() {
        var mapBuilder = new java.util.HashMap<String, Object>();
        mapBuilder.put("name", name);
        if (description != null) {
            mapBuilder.put("description", description);
        }
        mapBuilder.put("parameters", parameters.toMap());
        return mapBuilder;
    }
}