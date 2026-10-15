/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.doc;

import java.io.IOException;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Map;

import org.jspecify.annotations.Nullable;

/**
 * Base class for the documentation generators of KeY's taclet language constructs, e.g., for the
 * variable conditions ({@link VarcondDoc}) and the proof script commands ({@link ScriptDoc}). It
 * provides the shared handling of the output target and the post-processing of javadoc text.
 *
 * @author Alexander Weigl
 * @version 1 (23.08.26)
 */
public abstract class AbstractDocGenerator {

    /// Runs this generator. If a command line argument is given, the markdown output is written
    /// to that file together with a JSON dump ([#generateJsonData()]) next to it; otherwise the
    /// markdown is printed to stdout.
    ///
    /// @param mdFile an optional single argument with the path of the output file
    /// @param jsonFile
    /// @throws IOException if the output file cannot be written
    protected void run(String mdFile, String jsonFile) throws IOException {
        Path mdPath = Path.of(mdFile);
        if (mdPath.getParent() != null) {
            Files.createDirectories(mdPath.getParent());
        }

        try (var out = new PrintStream(Files.newOutputStream(mdPath), false)) {
            generateDocumentation(out);
        }


        Object data = generateJsonData();

        if (data != null) {
            Path jsonPath = Paths.get(jsonFile);
            if (jsonPath.getParent() != null) {
                Files.createDirectories(jsonPath.getParent());
            }
            try (var out = new PrintWriter(Files.newOutputStream(jsonPath), false)) {
                JsonWriter.toJson(data, out);
            }
        }
    }

    /// Writes the documentation of this generator in markdown format.
    protected abstract void generateDocumentation(PrintStream out);

    /// Returns the documentation data of this generator in a structured form, which is serialized
    /// into a JSON dump next to the markdown file. Returns `null` if this generator does not
    /// support a JSON dump.
    ///
    /// @return the structured documentation data, or `null`
    protected @Nullable Object generateJsonData() {
        return null;
    }

    /// Converts a javadoc comment into markdown by replacing common HTML tags and inline tags
    /// with their markdown equivalents.
    ///
    /// @param it the javadoc comment, may be null
    /// @return the comment as markdown
    protected static String cleanJavadoc(@Nullable String it) {
        if (it == null) {
            it = "";
        }
        return it.replace("<tt>", "`")
                .replace("<ul>", "\n")
                .replace("</ul>", "\n")
                .replace("<ul>", "\n")
                .replace("<li>", "* ")
                .replace("</li>", "")
                .replace("{@link", "`")
                .replace("}", "`")
                .replace("<code>", "`")
                .replace("</tt>", "`")
                .replace("</code>", "`")
                .replace("<b>", "**")
                .replace("</b>", "**");
    }

    /// Indents each line of the given text by the given prefix.
    ///
    /// @param spaces the indentation prefix
    /// @param it the text to indent
    /// @return the indented text
    protected static String indent(String spaces, String it) {
        return spaces + it.replace("\n", "\n" + spaces);
    }
}


/**
 * A minimal, dependency-free JSON serializer supporting the data structures used by the
 * documentation generators: {@link Map}s, {@link Iterable}s, strings, numbers, booleans, and
 * {@code null}. Other objects are serialized via their {@link Object#toString()}.
 *
 * @author Alexander Weigl
 * @version 1 (10.10.26)
 */
final class JsonWriter {

    private JsonWriter() {
    }

    /**
     * Serializes the given value into a pretty-printed JSON string.
     *
     * @param value the value to serialize
     * @param out target to write into
     */
    public static void toJson(@Nullable Object value, PrintWriter out) {
        write(out, value, 0);
    }

    private static void write(PrintWriter sb, @Nullable Object value, int depth) {
        switch (value) {
            case null -> sb.append("null");
            case String s -> writeString(sb, s);
            case Boolean b -> sb.print(b);
            case Number n -> sb.print(n);
            case Map<?, ?> map -> writeObject(sb, map, depth);
            case Iterable<?> iterable -> writeArray(sb, iterable, depth);
            default -> writeString(sb, value.toString());
        }
    }

    private static void writeObject(PrintWriter sb, Map<?, ?> map, int depth) {
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

    private static void writeArray(PrintWriter sb, Iterable<?> iterable, int depth) {
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

    private static void writeString(PrintWriter sb, String s) {
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

    private static void indent(PrintWriter sb, int depth) {
        sb.append("  ".repeat(depth));
    }
}

