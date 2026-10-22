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
import java.util.regex.Pattern;

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
    protected abstract void generateDocumentation(PrintStream out) throws IOException;

    /// Returns the documentation data of this generator in a structured form, which is serialized
    /// into a JSON dump next to the markdown file. Returns `null` if this generator does not
    /// support a JSON dump.
    ///
    /// @return the structured documentation data, or `null`
    protected @Nullable Object generateJsonData() throws IOException {
        return null;
    }

    /// Converts a javadoc comment into markdown by replacing common HTML tags and entities and
    /// the inline tags `{@code ...}`, `{@literal ...}`, `{@link ...}`, `{@value ...}` and
    /// `{@snippet ...}` with their markdown equivalents.
    ///
    /// Inline tags are parsed with a brace-balanced scanner, so unbalanced curly braces in the
    /// surrounding text stay untouched and braces inside a tag (e.g. in `{@code new A[]{...} }`
    /// or in the body of a `{@snippet ...}`) are not mistaken for the closing brace.
    ///
    /// @param it the javadoc comment, may be null
    /// @return the comment as markdown
    protected static String cleanJavadoc(@Nullable String it) {
        if (it == null) {
            return "";
        }
        return cleanInlineTags(cleanHtml(it));
    }

    /// Replaces common HTML tags and entities with their markdown equivalents.
    private static String cleanHtml(String it) {
        return it.replace("<tt>", "`")
                .replace("</tt>", "`")
                .replace("<code>", "`")
                .replace("</code>", "`")
                .replace("<b>", "**")
                .replace("</b>", "**")
                .replace("<strong>", "**")
                .replace("</strong>", "**")
                .replace("<i>", "*")
                .replace("</i>", "*")
                .replace("<em>", "*")
                .replace("</em>", "*")
                .replace("<ul>", "\n")
                .replace("</ul>", "\n")
                .replace("<li>", "* ")
                .replace("</li>", "\n")
                .replace("<p>", "\n\n")
                .replace("</p>", "\n\n")
                .replace("<br>", "\n")
                .replace("<br/>", "\n")
                .replace("&lt;", "<")
                .replace("&gt;", ">")
                .replace("&quot;", "\"")
                .replace("&#39;", "'")
                .replace("&apos;", "'")
                .replace("&nbsp;", " ")
                .replace("&amp;", "&");
    }

    /// Replaces the javadoc inline tags in the given text with markdown. A tag starts with
    /// `{@` and its closing `}` is determined brace-balanced, i.e. nested braces inside the tag
    /// are not treated as its end. Braces that open no tag are left as they are. Fenced code
    /// blocks produced from `{@snippet}` tags are separated from the surrounding text by blank
    /// lines.
    private static String cleanInlineTags(String it) {
        StringBuilder sb = new StringBuilder(it.length());
        boolean afterBlock = false;
        int start = 0;
        for (int i = 0; i < it.length();) {
            if (it.charAt(i) != '{' || i + 1 >= it.length() || it.charAt(i + 1) != '@') {
                i++;
                continue;
            }
            int end = tagEnd(it, i);
            if (end < 0) {
                // an unclosed tag -- keep the rest of the text verbatim
                appendProse(sb, afterBlock, it, start, it.length());
                return sb.toString();
            }
            appendProse(sb, afterBlock, it, start, i);
            String formatted = formatInlineTag(it.substring(i + 2, end));
            boolean block = formatted.startsWith("```");
            afterBlock = block;
            if (block) {
                padBeforeBlock(sb);
            }
            sb.append(formatted);
            start = end + 1;
            i = start;
        }
        appendProse(sb, afterBlock, it, start, it.length());
        return sb.toString();
    }

    /// Appends the given slice of text, inserting a blank line first when the text directly
    /// follows a fenced code block.
    private static void appendProse(StringBuilder sb, boolean afterBlock, String it, int from,
            int to) {
        if (afterBlock && to > from && it.charAt(from) != '\n') {
            // the block already ends with a newline, so a single further newline
            // separates it from the following text by a blank line
            sb.append('\n');
        }
        sb.append(it, from, to);
    }

    /// Ensures that the content appended so far ends with a blank line so that a following
    /// fenced code block is not glued to preceding text.
    private static void padBeforeBlock(StringBuilder sb) {
        if (sb.isEmpty()) {
            return;
        }
        if (sb.charAt(sb.length() - 1) != '\n') {
            sb.append("\n\n");
        } else if (sb.length() < 2 || sb.charAt(sb.length() - 2) != '\n') {
            sb.append('\n');
        }
    }

    /// Returns the index of the `}` matching the `{` at the given index, or -1 if the opening
    /// brace is not closed. Nested braces are taken into account.
    private static int tagEnd(String it, int open) {
        int depth = 0;
        for (int i = open; i < it.length(); i++) {
            char c = it.charAt(i);
            if (c == '{') {
                depth++;
            } else if (c == '}' && --depth == 0) {
                return i;
            }
        }
        return -1;
    }

    /// Formats the body of a javadoc inline tag (i.e. the text between `{@` and the matching
    /// `}`) into markdown. Unknown tags are reduced to their content.
    private static String formatInlineTag(String body) {
        int sp = firstWhitespace(body);
        String tag = sp < 0 ? body : body.substring(0, sp);
        String arg = sp < 0 ? "" : body.substring(sp).trim();
        return switch (tag) {
            case "code" -> "`" + arg + "`";
            case "literal" -> arg;
            case "link", "linkplain" -> formatLink(arg);
            case "value" -> "`" + arg + "`";
            case "snippet" -> formatSnippet(body);
            case "inheritDoc", "docRoot" -> "";
            default -> arg;
        };
    }

    /// Formats the argument of a `{@link ...}` or `{@linkplain ...}` tag as a markdown link
    /// `[label](target)`. If no explicit label is given, the simple class or member name is used.
    private static String formatLink(String arg) {
        int end = referenceEnd(arg);
        String target = arg.substring(0, end);
        String label = arg.substring(end).trim();
        if (label.isEmpty()) {
            label = simpleName(target);
        }
        return "[%s](%s)".formatted(label, destination(target));
    }

    /// Returns the end index of the referenced part of a `{@link ...}` argument, i.e. of the
    /// method signature including its closing parenthesis (method references may contain spaces
    /// inside the parameter list) or, otherwise, of the first whitespace-separated token.
    private static int referenceEnd(String arg) {
        int whitespace = firstWhitespace(arg);
        int paren = arg.indexOf('(');
        if (paren < 0 || (whitespace >= 0 && whitespace < paren)) {
            // no signature, or the parenthesis already belongs to a following label
            return whitespace < 0 ? arg.length() : whitespace;
        }
        int depth = 0;
        for (int i = paren; i < arg.length(); i++) {
            char c = arg.charAt(i);
            if (c == '(') {
                depth++;
            } else if (c == ')' && --depth == 0) {
                return i + 1;
            }
        }
        return arg.length();
    }

    /// Returns the default label for a javadoc reference, i.e. the simple class or member name
    /// with any signature and package prefix dropped.
    private static String simpleName(String target) {
        int hash = target.lastIndexOf('#');
        String tail = hash < 0 ? target : target.substring(hash + 1);
        int paren = tail.lastIndexOf('(');
        String name = paren < 0 ? tail : tail.substring(0, paren);
        int dot = name.lastIndexOf('.');
        return dot < 0 ? name : name.substring(dot + 1);
    }

    /// Returns the given javadoc reference as a markdown link destination, wrapped in angle
    /// brackets when it contains characters that would otherwise break the link syntax.
    private static String destination(String target) {
        for (int i = 0; i < target.length(); i++) {
            char c = target.charAt(i);
            if (c == ' ' || c == '(' || c == ')' || c == '<' || c == '>') {
                return "<" + target + ">";
            }
        }
        return target;
    }

    /// Formats a `{@snippet ...}` tag. The inline form (`{@snippet lang="..." : ...}`) is
    /// rendered as a fenced code block with an optional language. The file-based form
    /// (`{@snippet file="..." region="..."}`) references external source that cannot be
    /// resolved here, so it is kept verbatim.
    private static String formatSnippet(String body) {
        int colon = unquotedColon(body);
        if (colon < 0) {
            return "{@" + body + "}";
        }
        String code = dedent(body.substring(colon + 1));
        String lang = attribute(body.substring(0, colon), "lang");
        return "```%s\n%s\n```\n".formatted(lang == null ? "" : lang, code);
    }

    /// Returns the index of the first colon that is not part of a quoted attribute value, or
    /// -1 if there is none.
    private static int unquotedColon(String s) {
        boolean quoted = false;
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (c == '"') {
                quoted = !quoted;
            } else if (c == ':' && !quoted) {
                return i;
            }
        }
        return -1;
    }

    /// Extracts the value of the named attribute from the attribute list of a `{@snippet}` tag,
    /// or `null` if the attribute is not present.
    private static @Nullable String attribute(String attributes, String name) {
        var matcher = Pattern.compile(name + "\\s*=\\s*\"([^\"]*)\"").matcher(attributes);
        return matcher.find() ? matcher.group(1) : null;
    }

    /// Removes the longest common leading indentation of the non-blank lines, which strips the
    /// layout indentation from the body of an inline snippet.
    private static String dedent(String it) {
        var lines = it.split("\n", -1);
        int min = Integer.MAX_VALUE;
        for (var line : lines) {
            if (line.isBlank()) {
                continue;
            }
            int indent = 0;
            while (indent < line.length()
                    && (line.charAt(indent) == ' ' || line.charAt(indent) == '\t')) {
                indent++;
            }
            min = Math.min(min, indent);
        }
        if (min == Integer.MAX_VALUE) {
            return it.trim();
        }
        var sb = new StringBuilder();
        for (var line : lines) {
            sb.append(line.length() >= min ? line.substring(min) : line).append('\n');
        }
        return sb.toString().strip();
    }

    /// Returns the index of the first whitespace character, or -1 if there is none.
    private static int firstWhitespace(String s) {
        for (int i = 0; i < s.length(); i++) {
            if (Character.isWhitespace(s.charAt(i))) {
                return i;
            }
        }
        return -1;
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
