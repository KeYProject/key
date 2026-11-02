/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.awt.Dimension;
import java.awt.Font;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.stream.Collectors;
import javax.swing.BorderFactory;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JComponent;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.UIManager;

import org.key_project.key.llm.mcp.JsonSchema;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import net.miginfocom.swing.MigLayout;
import org.jspecify.annotations.Nullable;

/**
 * An editor form generated from a tool parameter {@link JsonSchema}: one labeled editor per
 * property (string → text field, boolean → checkbox, numbers → text field, enum → combo box,
 * array → one item per line, object → JSON text), used by the {@link ToolConsoleDialog}.
 * <p>
 * The form converts between the editors and the arguments JSON of a tool call: the values edited
 * in the form are serialized by {@link #toArgumentsJson()}, and
 * {@link #fromArgumentsJson(String)} fills the editors from a JSON object. When the schema is
 * absent or not an object schema, the whole arguments document is edited as raw JSON in a single
 * text area, which is then sent verbatim.
 * <p>
 * Property keys that are present in a parsed JSON document but have no editor (i.e. they are not
 * part of the schema) are remembered and included in the next serialization, so expert edits are
 * never silently dropped.
 *
 * @author Alexander Weigl
 */
public class JsonSchemaForm extends JPanel {
    private static final long serialVersionUID = 1L;

    /** Shared Gson instance; {@link GsonBuilder} only for the pretty-printed editor view. */
    private static final Gson GSON = new GsonBuilder().create();

    /** The parameter schema; {@code null} or non-object schemas switch to the JSON editor. */
    private final @Nullable JsonSchema schema;

    /** The editors per property name (in schema order); empty in the JSON fallback mode. */
    private final Map<String, JComponent> editors = new LinkedHashMap<>();

    /** The labels per property name. */
    private final Map<String, JLabel> labels = new LinkedHashMap<>();

    /** Schema-less keys of the last parsed JSON, preserved on the next serialization. */
    private final Map<String, Object> extraValues = new LinkedHashMap<>();

    /** The whole-arguments JSON editor of the fallback mode ({@code null} in form mode). */
    private final @Nullable JTextArea jsonEditor;

    /**
     * Creates the form for the given parameter schema.
     *
     * @param schema the parameters schema of a tool; may be {@code null} or a non-object schema,
     *        in which case the raw JSON fallback editor is used
     */
    public JsonSchemaForm(@Nullable JsonSchema schema) {
        this.schema = schema;
        var properties = schema == null ? null : schema.properties();
        if (properties == null || properties.isEmpty()) {
            jsonEditor = createJsonEditor();
            var scroll = new JScrollPane(jsonEditor);
            scroll.setPreferredSize(new Dimension(480, 220));
            setLayout(new MigLayout("ins 0, fillx, wrap 1", "[grow]"));
            add(scroll, "grow");
        } else {
            jsonEditor = null;
            setLayout(new MigLayout("ins 0, wrap 2", "[]8[grow]"));
            properties.forEach(this::addEditor);
        }
    }

    /** Adds the labeled editor row for one property of the object schema. */
    private void addEditor(String name, JsonSchema property) {
        var required = schema != null && schema.required() != null
                && schema.required().contains(name);
        var label = new JLabel(required ? name + " *" : name);
        if (property.description() != null && !property.description().isBlank()) {
            label.setToolTipText(property.description());
        }
        JComponent editor;
        if (property.enumValues() != null && !property.enumValues().isEmpty()) {
            editor = new JComboBox<>(property.enumValues().toArray(new String[0]));
        } else {
            editor = switch (property.schemaType() == null ? "string" : property.schemaType()) {
                case "boolean" -> new JCheckBox();
                case "array" -> createLinesEditor();
                case "object" -> createJsonEditor();
                // string, number, integer and anything unknown: a plain text field
                default -> new JTextField();
            };
        }
        editors.put(name, editor);
        labels.put(name, label);
        add(label);
        add(editor, editor instanceof JTextArea ? "grow, h 3::" : "growx");
    }

    /** The multi-line editor holding one array item per line. */
    private static JTextArea createLinesEditor() {
        var area = new JTextArea(3, 30);
        area.setBorder(border());
        return area;
    }

    /**
     * The JSON editor (whole arguments in fallback mode, single object properties in form mode).
     */
    private static JTextArea createJsonEditor() {
        var area = new JTextArea(6, 30);
        area.setFont(new Font(Font.MONOSPACED, Font.PLAIN, area.getFont().getSize()));
        area.setBorder(border());
        return area;
    }

    private static javax.swing.border.Border border() {
        var color = UIManager.getColor("Component.borderColor");
        return color == null ? BorderFactory.createLineBorder(java.awt.Color.GRAY)
                : BorderFactory.createLineBorder(color);
    }

    /**
     * Serializes the current editor values into the arguments JSON object. In the fallback mode
     * the JSON editor's content is returned verbatim (an empty document becomes <code>{}</code>).
     *
     * @return a JSON object document
     * @throws IllegalStateException if a number editor holds text that is not a number, or an
     *         object editor holds invalid JSON
     */
    public String toArgumentsJson() {
        if (jsonEditor != null) {
            var text = jsonEditor.getText().strip();
            return text.isEmpty() ? "{}" : text;
        }
        var values = new LinkedHashMap<String, Object>();
        editors.forEach((name, editor) -> values.put(name, editorValue(name, editor)));
        values.putAll(extraValues);
        return GSON.toJson(values);
    }

    /**
     * Fills the editors from the given arguments JSON document. In the fallback mode the text is
     * always adopted; an error is reported when it is not a JSON object.
     *
     * @param json a JSON object document (a blank document clears the editors)
     * @return an error text on invalid input, {@code null} on success; in form mode the editors
     *         are left untouched on error
     */
    public @Nullable String fromArgumentsJson(String json) {
        var stripped = json.strip();
        if (jsonEditor != null) {
            jsonEditor.setText(json);
            if (stripped.isEmpty()) {
                return null; // a blank document becomes {} on serialization
            }
            try {
                return GSON.fromJson(stripped, Object.class) instanceof Map<?, ?> ? null
                        : "not a JSON object";
            } catch (Exception e) {
                return "not valid JSON: " + e.getMessage();
            }
        }
        Map<String, Object> parsed;
        try {
            parsed = stripped.isEmpty() ? new LinkedHashMap<>()
                    : Objects.requireNonNullElse(GSON.fromJson(stripped, Map.class),
                        new LinkedHashMap<>());
        } catch (Exception e) {
            return "not a JSON object: " + e.getMessage();
        }
        editors.forEach((name, editor) -> setEditorValue(name, editor, parsed.get(name)));
        extraValues.clear();
        parsed.forEach((key, value) -> {
            if (!editors.containsKey(key)) {
                extraValues.put(key, value);
            }
        });
        return null;
    }

    /** The current value of one editor, in a JSON-serializable representation. */
    private @Nullable Object editorValue(String name, JComponent editor) {
        if (editor instanceof JCheckBox box) {
            return box.isSelected();
        }
        if (editor instanceof JComboBox<?> combo) {
            return combo.getSelectedItem();
        }
        if (editor instanceof JTextArea area) {
            var property = propertySchema(name);
            return property != null && "array".equals(property.schemaType())
                    ? linesOf(area.getText())
                    : parseJsonValue(name, area.getText());
        }
        var text = ((JTextField) editor).getText();
        var property = propertySchema(name);
        var type = property == null ? "string" : property.schemaType();
        if ("integer".equals(type)) {
            return parseNumber(name, text, true);
        }
        if ("number".equals(type)) {
            return parseNumber(name, text, false);
        }
        return text;
    }

    /** Parses a numeric editor value; {@code integer} fields yield whole numbers. */
    private static Object parseNumber(String name, String text, boolean integer) {
        if (text.isBlank()) {
            return "";
        }
        try {
            return integer ? Long.parseLong(text.strip()) : Double.parseDouble(text.strip());
        } catch (NumberFormatException e) {
            throw new IllegalStateException("'" + name + "' must be a number: " + text);
        }
    }

    /** The array editor's content: the non-blank lines, stripped. */
    private static List<String> linesOf(String text) {
        return Arrays.stream(text.split("\n")).map(String::strip)
                .filter(s -> !s.isEmpty()).collect(Collectors.toList());
    }

    /** Parses an object editor's JSON content; invalid JSON is an error (never a silent string). */
    private @Nullable Object parseJsonValue(String name, String text) {
        if (text.isBlank()) {
            return null;
        }
        try {
            return GSON.fromJson(text, Object.class);
        } catch (Exception e) {
            throw new IllegalStateException("'" + name + "' is not valid JSON: " + e.getMessage());
        }
    }

    /**
     * Fills one editor from a parsed JSON value (missing values keep the editor's state).
     */
    private void setEditorValue(String name, JComponent editor, @Nullable Object value) {
        if (value == null) {
            return;
        }
        if (editor instanceof JCheckBox box) {
            box.setSelected(Boolean.TRUE.equals(value));
        } else if (editor instanceof JComboBox<?> combo) {
            combo.setSelectedItem(String.valueOf(value));
        } else if (editor instanceof JTextArea area) {
            if (value instanceof List<?> list) {
                area.setText(list.stream().map(String::valueOf)
                        .collect(Collectors.joining("\n")));
            } else {
                area.setText(new GsonBuilder().setPrettyPrinting().create().toJson(value));
            }
        } else if (editor instanceof JTextField field) {
            field.setText(numberText(name, value));
        }
    }

    /**
     * Formats a parsed JSON value for a text editor: for integer properties, Gson's double
     * representation (e.g. {@code 42.0}) is shown without the fraction so that a round trip
     * keeps the text stable.
     */
    private String numberText(String name, Object value) {
        var property = propertySchema(name);
        if (property != null && "integer".equals(property.schemaType())
                && value instanceof Number n && !Double.isInfinite(n.doubleValue())
                && n.doubleValue() == Math.rint(n.doubleValue())) {
            return String.valueOf(n.longValue());
        }
        return String.valueOf(value);
    }

    /** The schema of a single property, or {@code null}. */
    private @Nullable JsonSchema propertySchema(String name) {
        var properties = schema == null ? null : schema.properties();
        return properties == null ? null : properties.get(name);
    }

    /** The label of the named property (for tests). */
    JLabel labelOf(String name) {
        return labels.get(name);
    }

    /** The editor of the named property (for tests). */
    @Nullable
    JComponent editorOf(String name) {
        return editors.get(name);
    }

    /** The fallback JSON editor, or {@code null} in form mode. */
    @Nullable
    JTextArea jsonEditor() {
        return jsonEditor;
    }
}
