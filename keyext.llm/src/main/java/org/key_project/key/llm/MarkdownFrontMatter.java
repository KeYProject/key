/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.dataformat.yaml.YAMLFactory;
import com.fasterxml.jackson.dataformat.yaml.YAMLGenerator;
import org.jspecify.annotations.Nullable;

/**
 * Parses and renders the Markdown storage format of the user libraries (skills and prompts): a
 * YAML front matter block with the metadata keys ({@code name}, {@code description}, and for
 * skills {@code enabled} and {@code allowedTools}) followed by the Markdown body (the prompt
 * template, respectively the skill instructions):
 * <pre>
 * ---
 * name: optics
 * description: focus on arithmetic overflow proofs
 * enabled: true
 * allowedTools: [read_file]
 * ---
 * Pay special attention to integer overflow; ...
 * </pre>
 * The format is deliberately simple ("forward matter, then body") so the files stay human
 * readable and editable by hand.
 *
 * @author Alexander Weigl
 */
public final class MarkdownFrontMatter {

    /** The parsed representation of one Markdown document. */
    public record Parsed(Map<String, Object> meta, String body) {
    }

    private static final ObjectMapper YAML_MAPPER;

    static {
        YAMLFactory factory = new YAMLFactory();
        // we add our own "---" delimiters around the block
        factory.disable(YAMLGenerator.Feature.WRITE_DOC_START_MARKER);
        // readable output: omit quotes where the value cannot be misread as another type
        // (strings that would be parsed as booleans/numbers are still quoted), indent lists
        factory.enable(YAMLGenerator.Feature.MINIMIZE_QUOTES);
        factory.enable(YAMLGenerator.Feature.INDENT_ARRAYS_WITH_INDICATOR);
        YAML_MAPPER = new ObjectMapper(factory);
    }

    private MarkdownFrontMatter() {
    }

    /**
     * Parses a Markdown document with a YAML front matter (leading line {@code ---}, a YAML
     * block, a closing line {@code ---}, then the body). Returns {@code null} when the document
     * is not in this format or the front matter cannot be parsed.
     */
    public static @Nullable Parsed parse(@Nullable String text) {
        if (text == null) {
            return null;
        }
        String[] lines = text.split("\n", -1);
        if (lines.length < 3 || !lines[0].strip().equals("---")) {
            return null;
        }
        int end = -1;
        for (int i = 1; i < lines.length; i++) {
            if (lines[i].strip().equals("---")) {
                end = i;
                break;
            }
        }
        if (end < 0) {
            return null;
        }
        var yamlText = String.join("\n", java.util.Arrays.copyOfRange(lines, 1, end));
        String body = String.join("\n", java.util.Arrays.copyOfRange(lines, end + 1,
            lines.length));
        // drop the blank separator line(s) between the closing "---" and the body
        body = body.replaceFirst("^(\r?\n)+", "");

        Map<String, Object> meta;
        try {
            meta = YAML_MAPPER.readValue(yamlText, Map.class);
        } catch (Exception e) {
            return null;
        }
        if (meta == null) {
            return null;
        }
        return new Parsed(meta, body);
    }

    /**
     * Renders a Markdown document from front-matter metadata and a body. String values are
     * serialized by Jackson in YAML 1.2 style; the map must be ordered (e.g.
     * {@link LinkedHashMap}) to control the key order.
     */
    public static String render(Map<String, Object> meta, @Nullable String body) {
        String yaml;
        try {
            yaml = YAML_MAPPER.writeValueAsString(meta);
        } catch (JsonProcessingException e) {
            throw new IllegalArgumentException("Could not serialize metadata: " + e.getMessage(),
                e);
        }
        return "---\n" + yaml + "---\n\n" + (body == null ? "" : body);
    }

    /** The metadata value as a string, or {@code null} when absent. */
    public static @Nullable String stringValue(Map<String, Object> meta, String key) {
        Object v = meta.get(key);
        return v == null ? null : String.valueOf(v);
    }

    /** The metadata value as a list of strings (empty when absent or not a list). */
    public static List<String> stringList(Map<String, Object> meta, String key) {
        Object v = meta.get(key);
        if (v instanceof List<?> list) {
            var result = new ArrayList<String>();
            for (Object item : list) {
                result.add(String.valueOf(item));
            }
            return result;
        }
        return List.of();
    }
}
