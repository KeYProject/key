/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.doc;

import java.util.Map;

import org.jspecify.annotations.Nullable;

/**
 * A minimal, dependency-free JSON serializer supporting the data structures used by the
 * documentation generators: {@link Map}s, {@link Iterable}s, strings, numbers, booleans, and
 * {@code null}. Other objects are serialized via their {@link Object#toString()}.
 *
 * @author Alexander Weigl
 * @version 1 (10.10.26)
 */
public final class JsonWriter {

    private JsonWriter() {
    }

    /**
     * Serializes the given value into a pretty-printed JSON string.
     *
     * @param value the value to serialize
     * @return the JSON representation of the value
     */
    public static String toJson(@Nullable Object value) {
        var sb = new StringBuilder();
        write(sb, value, 0);
        return sb.toString();
    }

    private static void write(StringBuilder sb, @Nullable Object value, int depth) {
        switch (value) {
            case null -> sb.append("null");
            case String s -> writeString(sb, s);
            case Boolean b -> sb.append(b);
            case Number n -> sb.append(n);
            case Map<?, ?> map -> writeObject(sb, map, depth);
            case Iterable<?> iterable -> writeArray(sb, iterable, depth);
            default -> writeString(sb, value.toString());
        }
    }

    private static void writeObject(StringBuilder sb, Map<?, ?> map, int depth) {
        sb.append("{\n");
        var it = map.entrySet().iterator();
        while (it.hasNext()) {
            var entry = it.next();
            indent(sb, depth + 1);
            writeString(sb, String.valueOf(entry.getKey()));
            sb.append(": ");
            write(sb, entry.getValue(), depth + 1);
            if (it.hasNext()) {
                sb.append(',');
            }
            sb.append('\n');
        }
        indent(sb, depth);
        sb.append('}');
    }

    private static void writeArray(StringBuilder sb, Iterable<?> iterable, int depth) {
        sb.append("[\n");
        var it = iterable.iterator();
        while (it.hasNext()) {
            indent(sb, depth + 1);
            write(sb, it.next(), depth + 1);
            if (it.hasNext()) {
                sb.append(',');
            }
            sb.append('\n');
        }
        indent(sb, depth);
        sb.append(']');
    }

    private static void writeString(StringBuilder sb, String s) {
        sb.append('"');
        for (var i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            switch (c) {
                case '"' -> sb.append("\\\"");
                case '\\' -> sb.append("\\\\");
                case '\n' -> sb.append("\\n");
                case '\r' -> sb.append("\\r");
                case '\t' -> sb.append("\\t");
                case '\b' -> sb.append("\\b");
                case '\f' -> sb.append("\\f");
                default -> {
                    if (c < 0x20) {
                        sb.append("\\u%04x".formatted((int) c));
                    } else {
                        sb.append(c);
                    }
                }
            }
        }
        sb.append('"');
    }

    private static void indent(StringBuilder sb, int depth) {
        sb.append("  ".repeat(depth));
    }
}
