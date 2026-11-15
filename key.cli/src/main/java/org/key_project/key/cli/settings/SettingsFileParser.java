/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.settings;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

/**
 * Parses and validates a §5.2 settings file: a flat JSON object whose (only meaningful) keys are
 * the twelve documented strategy keys and whose values are one of the documented
 * {@code "category:value"} strings.
 * <p>
 * The parser is deliberately small and self-contained (the {@code key.cli} module does not depend
 * on a JSON library, and the format is a fixed flat object). It reads the file line by line so that
 * an unknown key or an undocumented value can be reported with the exact offending source line
 * (§5.3): {@code KEY_ERROR settings: '<LINE>' not understood}.
 * <p>
 * The returned map is keyed by the JSON key (the choice category, e.g. {@code intRules}) and maps
 * to the full documented value string (e.g. {@code intRules:javaSemantics}); the value is what
 * {@link de.uka.ilkd.key.settings.ChoiceSettings} stores in its default choices map. See
 * {@link HeadlessRunnerSettings} for how documented values are applied to KeY.
 */
public final class SettingsFileParser {

    /**
     * The documented §5.2 keys and, for each, the accepted values. The values are the choice names
     * that KeY actually declares in {@code optionsDeclarations.key}, plus the retained historical
     * shorthands {@code intRules:checked}/{@code intRules:unchecked}/{@code methodExpansion:full}
     * that {@link HeadlessRunnerSettings#normalize} maps to the real names.
     */
    private static final Map<String, Set<String>> ALLOWED = Map.ofEntries(
        Map.entry("intRules", Set.of(
            "intRules:arithmeticSemanticsIgnoringOF",
            "intRules:arithmeticSemanticsCheckingOF",
            "intRules:javaSemantics",
            "intRules:checked",
            "intRules:unchecked")),
        Map.entry("integerSimplificationRules", Set.of(
            "integerSimplificationRules:full",
            "integerSimplificationRules:minimal")),
        Map.entry("javaLoopTreatment", Set.of(
            "javaLoopTreatment:efficient",
            "javaLoopTreatment:teaching")),
        Map.entry("assertions", Set.of(
            "assertions:safe",
            "assertions:on",
            "assertions:off")),
        Map.entry("runtimeExceptions", Set.of(
            "runtimeExceptions:ban",
            "runtimeExceptions:allow",
            "runtimeExceptions:ignore")),
        Map.entry("bigint", Set.of(
            "bigint:on",
            "bigint:off")),
        Map.entry("programRules", Set.of(
            "programRules:Java",
            "programRules:None")),
        Map.entry("methodExpansion", Set.of(
            "methodExpansion:modularOnly",
            "methodExpansion:noRestriction",
            "methodExpansion:full")),
        Map.entry("Strings", Set.of(
            "Strings:on",
            "Strings:off")),
        Map.entry("sequences", Set.of(
            "sequences:on",
            "sequences:off")),
        Map.entry("reach", Set.of(
            "reach:on",
            "reach:off")),
        Map.entry("permissions", Set.of(
            "permissions:on",
            "permissions:off")));

    /**
     * Parses a settings file.
     *
     * @param file the settings file to read (UTF-8)
     * @return the parsed {@code category -> "category:value"} entries
     * @throws CliSettingsException if the file contains an unknown key or an undocumented value
     * @throws UncheckedIOException if the file cannot be read
     */
    public Map<String, String> parse(Path file) {
        String content;
        try {
            content = Files.readString(file, StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException("cannot read settings file: " + file, e);
        }
        return parse(content);
    }

    /**
     * Parses settings JSON from a string.
     *
     * @param json the settings JSON text
     * @return the parsed {@code category -> "category:value"} entries
     * @throws CliSettingsException if the text contains an unknown key or an undocumented value
     */
    public Map<String, String> parse(String json) {
        Map<String, String> settings = new LinkedHashMap<>();
        Reader reader = new Reader(json);
        reader.expect('{');
        reader.skipWhitespace();
        if (reader.peek() == '}') {
            reader.next();
            reader.expectEnd();
            return settings;
        }
        while (true) {
            String keyLine = reader.lineText();
            String key = reader.readString();
            reader.skipWhitespace();
            reader.expect(':');
            reader.skipWhitespace();
            String valueLine = reader.lineText();
            String value = reader.readString();
            checkKey(key, keyLine);
            checkValue(key, value, valueLine);
            settings.put(key, value);

            reader.skipWhitespace();
            char separator = reader.next();
            if (separator == '}') {
                break;
            }
            if (separator != ',') {
                throw notUnderstood(reader.lineText());
            }
            reader.skipWhitespace();
        }
        reader.expectEnd();
        return settings;
    }

    /**
     * Validates a single {@code --strategy-option <KEY>=<VALUE>} against the §5.2 vocabulary.
     *
     * @param key the option key (a §5.2 key)
     * @param value the option value (a documented {@code "category:value"} string)
     * @throws CliSettingsException if the key or value is not documented
     */
    public static void validateStrategyOption(String key, String value) {
        checkKey(key, key + "=" + value);
        checkValue(key, value, key + "=" + value);
    }

    private static void checkKey(String key, String offendingLine) {
        if (!ALLOWED.containsKey(key)) {
            throw notUnderstood(offendingLine);
        }
    }

    private static void checkValue(String key, String value, String offendingLine) {
        Set<String> allowed = ALLOWED.get(key);
        if (allowed == null || !allowed.contains(value)) {
            throw notUnderstood(offendingLine);
        }
    }

    private static CliSettingsException notUnderstood(String line) {
        return new CliSettingsException("settings: '" + line + "' not understood");
    }

    /**
     * A minimal cursor over the settings text that tracks the current line so violations can be
     * reported with their exact source line.
     */
    private static final class Reader {
        private final String text;
        private int pos;
        private int lineStart;

        Reader(String text) {
            this.text = text;
        }

        char peek() {
            return pos < text.length() ? text.charAt(pos) : '\0';
        }

        boolean atEnd() {
            return pos >= text.length();
        }

        char next() {
            char c = text.charAt(pos++);
            if (c == '\n') {
                lineStart = pos;
            }
            return c;
        }

        String lineText() {
            int end = text.indexOf('\n', lineStart);
            if (end < 0) {
                end = text.length();
            }
            return text.substring(lineStart, end);
        }

        void skipWhitespace() {
            while (!atEnd() && Character.isWhitespace(peek())) {
                next();
            }
        }

        void expect(char expected) {
            skipWhitespace();
            if (atEnd() || peek() != expected) {
                throw notUnderstood(lineText());
            }
            next();
        }

        void expectEnd() {
            skipWhitespace();
            if (!atEnd()) {
                throw notUnderstood(lineText());
            }
        }

        String readString() {
            expect('"');
            StringBuilder sb = new StringBuilder();
            while (true) {
                if (atEnd()) {
                    throw notUnderstood(lineText());
                }
                char c = next();
                if (c == '"') {
                    return sb.toString();
                }
                if (c == '\\') {
                    if (atEnd()) {
                        throw notUnderstood(lineText());
                    }
                    sb.append(next());
                } else {
                    sb.append(c);
                }
            }
        }
    }
}
