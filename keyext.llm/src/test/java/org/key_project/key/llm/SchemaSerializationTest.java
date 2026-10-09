/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.List;
import java.util.Map;

import org.key_project.key.llm.mcp.FunctionDefinition;
import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.mcp.Tool;

import com.google.gson.GsonBuilder;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The tool schemas are serialized with Gson on the wire; every structural class therefore needs a
 * Gson-safe {@code toMap()} (records serialized directly would emit Jackson-style key names such as
 * {@code schemaType}). These tests lock the exact OpenAI key names in.
 */
class SchemaSerializationTest {

    @Test
    void jsonSchemaTypeIsSerializedAsType() {
        var map = new JsonSchema("object").toMap();
        assertEquals("object", map.get("type"));
    }

    @Test
    void jsonSchemaBuilderEmitsOpenAiKeys() {
        var schema = JsonSchema.builder()
                .withType("object")
                .addProperty("path", JsonSchema.builder().withType("string").build())
                .addProperty("verbose", JsonSchema.builder().withType("boolean").build())
                .addRequired("path")
                .withDescription("read a file")
                .build();
        var map = schema.toMap();
        assertEquals("object", map.get("type"));
        assertEquals(List.of("path"), map.get("required"));
        assertEquals("read a file", map.get("description"));
        var props = (Map<?, ?>) map.get("properties");
        assertEquals("string", ((Map<?, ?>) props.get("path")).get("type"));
        assertEquals("boolean", ((Map<?, ?>) props.get("verbose")).get("type"));
    }

    @Test
    void functionDefinitionEmitsNameDescriptionParameters() {
        var fn = new FunctionDefinition("list_files", "lists files",
            new JsonSchema("object"));
        var map = fn.toMap();
        assertEquals("list_files", map.get("name"));
        assertEquals("lists files", map.get("description"));
        assertTrue(map.containsKey("parameters"));
    }

    @Test
    void toolMapDoesNotLeakApprovalMetadata() {
        var tool = new Tool(new FunctionDefinition("run_command", "runs a command",
            new JsonSchema("object")), Tool.ApprovalRequirement.ASK);
        var map = tool.toMap();
        assertEquals("function", map.get("type"));
        assertTrue(map.containsKey("function"));
        assertFalse(map.containsKey("defaultApproval"));
        assertFalse(map.containsKey("approvalRequirement"));
    }

    @Test
    void toolMapIsGsonSerializable() {
        var fn = new FunctionDefinition("get_proof_context", "proof state", JsonSchema.builder()
                .withType("object")
                .addProperty("include_compute_path",
                    JsonSchema.builder().withType("boolean").build())
                .build());
        var json = new GsonBuilder().create().toJson(new Tool(fn).toMap());
        assertTrue(json.contains("\"type\":\"function\""), json);
        assertTrue(json.contains("\"include_compute_path\""), json);
        assertFalse(json.contains("schemaType"), "Jackson-style keys must not leak: " + json);
    }
}
