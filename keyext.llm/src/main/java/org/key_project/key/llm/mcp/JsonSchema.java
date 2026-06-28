package org.key_project.key.llm.mcp;

import com.fasterxml.jackson.annotation.JsonProperty;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Represents a JSON Schema object for function parameters in OpenAI tool specification.
 * <p>
 * This follows the JSON Schema specification as used by OpenAI's API.
 *
 * @param schemaType The type of the value (e.g., "object", "string", "number", "array")
 * @param properties Map of property names to their schema definitions (for type "object")
 * @param required   List of required property names (for type "object")
 * @param items      Schema for array items (for type "array")
 * @param enumValues List of allowed values (for enum constraints)
 * @param description Optional description of the parameter
 * @author Alexander Weigl
 * @version 1 (28.06.26)
 */
public record JsonSchema(
        @JsonProperty("type") String schemaType,
        @JsonProperty("properties") Map<String, JsonSchema> properties,
        @JsonProperty("required") List<String> required,
        @JsonProperty("items") JsonSchema items,
        @JsonProperty("enum") List<String> enumValues,
        @JsonProperty("description") String description
) {
    /**
     * Creates an empty JSON Schema (defaults to an object type).
     */
    public JsonSchema() {
        this(null, null, null, null, null, null);
    }

    /**
     * Creates a JSON Schema with the specified type.
     *
     * @param schemaType The type of the value
     */
    public JsonSchema(String schemaType) {
        this(schemaType, null, null, null, null, null);
    }

    /**
     * Creates a JSON Schema for an object type with properties.
     *
     * @param properties Map of property names to their schema definitions
     * @param required   List of required property names
     */
    public JsonSchema(Map<String, JsonSchema> properties, List<String> required) {
        this("object", properties, required, null, null, null);
    }

    /**
     * Converts this JsonSchema to a Map representation.
     *
     * @return Map containing the JSON Schema definition
     */
    public Map<String, Object> toMap() {
        var map = new LinkedHashMap<String, Object>();

        if (schemaType != null) {
            map.put("type", schemaType);
        }
        if (properties != null && !properties.isEmpty()) {
            var propsMap = new LinkedHashMap<String, Object>();
            properties.forEach((k, v) -> propsMap.put(k, v.toMap()));
            map.put("properties", propsMap);
        }
        if (required != null && !required.isEmpty()) {
            map.put("required", required);
        }
        if (items != null) {
            map.put("items", items.toMap());
        }
        if (enumValues != null && !enumValues.isEmpty()) {
            map.put("enum", enumValues);
        }
        if (description != null) {
            map.put("description", description);
        }

        return map;
    }

    /**
     * Creates a builder for JsonSchema.
     *
     * @return A new Builder instance
     */
    public static Builder builder() {
        return new Builder();
    }

    /**
     * Builder class for creating JsonSchema instances.
     */
    public static class Builder {
        private String schemaType;
        private Map<String, JsonSchema> properties;
        private List<String> required;
        private JsonSchema items;
        private List<String> enumValues;
        private String description;

        /**
         * Sets the schema type.
         *
         * @param type The type (e.g., "object", "string", "number", "array", "boolean")
         * @return this builder
         */
        public Builder withType(String type) {
            this.schemaType = type;
            return this;
        }

        /**
         * Sets the properties map.
         *
         * @param properties Map of property names to their schema definitions
         * @return this builder
         */
        public Builder withProperties(Map<String, JsonSchema> properties) {
            this.properties = properties;
            return this;
        }

        /**
         * Adds a property to the schema.
         *
         * @param name   The property name
         * @param schema The property schema
         * @return this builder
         */
        public Builder addProperty(String name, JsonSchema schema) {
            if (this.properties == null) {
                this.properties = new LinkedHashMap<>();
            }
            this.properties.put(name, schema);
            return this;
        }

        /**
         * Sets the required properties list.
         *
         * @param required List of required property names
         * @return this builder
         */
        public Builder withRequired(List<String> required) {
            this.required = required;
            return this;
        }

        /**
         * Adds a required property.
         *
         * @param propertyName The name of the required property
         * @return this builder
         */
        public Builder addRequired(String propertyName) {
            if (this.required == null) {
                this.required = new java.util.ArrayList<>();
            }
            this.required.add(propertyName);
            return this;
        }

        /**
         * Sets the items schema for array types.
         *
         * @param items The schema for array items
         * @return this builder
         */
        public Builder withItems(JsonSchema items) {
            this.items = items;
            return this;
        }

        /**
         * Sets the enum values.
         *
         * @param enumValues List of allowed values
         * @return this builder
         */
        public Builder withEnum(List<String> enumValues) {
            this.enumValues = enumValues;
            return this;
        }

        /**
         * Sets the description.
         *
         * @param description The description
         * @return this builder
         */
        public Builder withDescription(String description) {
            this.description = description;
            return this;
        }

        /**
         * Builds the JsonSchema instance.
         *
         * @return A new JsonSchema
         */
        public JsonSchema build() {
            return new JsonSchema(schemaType, properties, required, items, enumValues, description);
        }
    }
}