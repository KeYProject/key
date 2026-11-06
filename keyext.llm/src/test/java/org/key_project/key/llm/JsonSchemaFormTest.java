/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.List;
import java.util.Map;

import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.uitest.McpUiTestHarness;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The generated parameter form of the tool console: editor mapping per schema type and the
 * round trips between the editors and the arguments JSON.
 */
class JsonSchemaFormTest {

    /** The schema of a tool exercising every supported editor type. */
    private static JsonSchema sampleSchema() {
        return JsonSchema.builder().withType("object")
                .addProperty("path", JsonSchema.builder().withType("string")
                        .withDescription("relative path inside the model").build())
                .addProperty("replace_all", JsonSchema.builder().withType("boolean").build())
                .addProperty("limit", JsonSchema.builder().withType("integer").build())
                .addProperty("ratio", JsonSchema.builder().withType("number").build())
                .addProperty("mode", JsonSchema.builder().withType("string")
                        .withEnum(List.of("fast", "safe")).build())
                .addProperty("names", JsonSchema.builder().withType("array").build())
                .addProperty("config", JsonSchema.builder().withType("object").build())
                .withRequired(List.of("path")).build();
    }

    @Test
    void editorsMatchTheSchemaTypes() {
        McpUiTestHarness.onEdt(() -> {
            var form = new JsonSchemaForm(sampleSchema());
            McpUiTestHarness.layoutRecursively(form);
            assertTrue(form.editorOf("path") instanceof javax.swing.JTextField);
            assertTrue(form.editorOf("replace_all") instanceof javax.swing.JCheckBox);
            assertTrue(form.editorOf("limit") instanceof javax.swing.JTextField);
            assertTrue(form.editorOf("ratio") instanceof javax.swing.JTextField);
            assertTrue(form.editorOf("mode") instanceof javax.swing.JComboBox<?>);
            assertTrue(form.editorOf("names") instanceof javax.swing.JTextArea);
            assertTrue(form.editorOf("config") instanceof javax.swing.JTextArea);
        });
    }

    @Test
    void requiredPropertiesAreMarked() {
        McpUiTestHarness.onEdt(() -> {
            var form = new JsonSchemaForm(sampleSchema());
            assertTrue(form.labelOf("path").getText().contains("*"), "required: path");
            assertFalse(form.labelOf("replace_all").getText().contains("*"), "optional");
            assertEquals("relative path inside the model", form.labelOf("path").getToolTipText());
        });
    }

    @Test
    void formValuesSerializeToArgumentsJson() {
        McpUiTestHarness.onEdt(() -> {
            var form = new JsonSchemaForm(sampleSchema());
            McpUiTestHarness.layoutRecursively(form);
            ((javax.swing.JTextField) form.editorOf("path")).setText("src/Main.java");
            ((javax.swing.JCheckBox) form.editorOf("replace_all")).setSelected(true);
            ((javax.swing.JTextField) form.editorOf("limit")).setText("4096");
            ((javax.swing.JTextField) form.editorOf("ratio")).setText("0.25");
            ((javax.swing.JComboBox<?>) form.editorOf("mode")).setSelectedItem("safe");
            ((javax.swing.JTextArea) form.editorOf("names"))
                    .setText("alpha\nbeta\n\n  \ngamma");
            ((javax.swing.JTextArea) form.editorOf("config"))
                    .setText("{\"nested\": [1, 2]}");

            var json = form.toArgumentsJson();
            var parsed = new com.google.gson.GsonBuilder().create().fromJson(json, Map.class);
            assertEquals("src/Main.java", parsed.get("path"));
            assertEquals(true, parsed.get("replace_all"));
            assertTrue(json.contains("\"limit\":4096"), "integer without fraction: " + json);
            assertTrue(json.contains("\"ratio\":0.25"), "number kept as written: " + json);
            assertEquals("safe", parsed.get("mode"));
            assertEquals(List.of("alpha", "beta", "gamma"), parsed.get("names"));
            assertEquals(Map.of("nested", List.of(1.0, 2.0)), parsed.get("config"));
        });
    }

    @Test
    void argumentsJsonFillsTheEditors() {
        McpUiTestHarness.onEdt(() -> {
            var form = new JsonSchemaForm(sampleSchema());
            assertNull(form.fromArgumentsJson("{\"path\": \"a.txt\", \"limit\": 42,"
                + " \"mode\": \"fast\", \"names\": [\"x\"], \"config\": {\"k\": true},"
                + " \"unknown\": [3]}"));
            assertEquals("a.txt", ((javax.swing.JTextField) form.editorOf("path")).getText());
            assertFalse(((javax.swing.JCheckBox) form.editorOf("replace_all")).isSelected(),
                "missing values keep the editor state");
            assertEquals("42", ((javax.swing.JTextField) form.editorOf("limit")).getText());
            assertEquals("fast", ((javax.swing.JComboBox<?>) form.editorOf("mode"))
                    .getSelectedItem());
            assertEquals("x", ((javax.swing.JTextArea) form.editorOf("names")).getText().strip());
            // schema-less keys are preserved for the next serialization
            var json = form.toArgumentsJson();
            assertTrue(json.contains("\"unknown\""), "expert edits survive: " + json);
        });
    }

    @Test
    void invalidInputIsReportedAndLeavesTheFormUntouched() {
        McpUiTestHarness.onEdt(() -> {
            var form = new JsonSchemaForm(sampleSchema());
            ((javax.swing.JTextField) form.editorOf("path")).setText("keep-me");

            assertNotNull(form.fromArgumentsJson("{not json"));
            assertEquals("keep-me", ((javax.swing.JTextField) form.editorOf("path")).getText(),
                "the editors are unchanged on error");

            // non-integer numbers are rejected at serialization time
            ((javax.swing.JTextField) form.editorOf("limit")).setText("4.5");
            var exception = assertThrows(IllegalStateException.class, form::toArgumentsJson);
            assertTrue(exception.getMessage().contains("limit"));
        });
    }

    @Test
    void absentSchemaFallsBackToTheJsonEditor() {
        McpUiTestHarness.onEdt(() -> {
            var form = new JsonSchemaForm(null);
            assertNotNull(form.jsonEditor(), "the whole arguments are edited as JSON");
            form.jsonEditor().setText("{\"path\": \"x\"}");
            assertEquals("{\"path\": \"x\"}", form.toArgumentsJson(),
                "the fallback editor is sent verbatim");
            assertNotNull(form.fromArgumentsJson("[1, 2]"), "non-objects are reported");
            assertEquals("[1, 2]", form.jsonEditor().getText(),
                "the text is adopted regardless");
        });
    }
}
