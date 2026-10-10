/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.doc;

import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
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
    /// to that file; otherwise it is printed to stdout.
    ///
    /// @param args an optional single argument with the path of the output file
    /// @throws IOException if the output file cannot be written
    protected void run(@Nullable String... args) throws IOException {
        var config = new ParserConfiguration();
        config.setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_21);
        StaticJavaParser.setConfiguration(config);

        if (args != null && args.length > 0) {
            Path file = Path.of(args[0]);
            if (file.getParent() != null) {
                Files.createDirectories(file.getParent());
            }
            try (var out =
                new PrintStream(Files.newOutputStream(file), false, StandardCharsets.UTF_8)) {
                generateDocumentation(out);
            }
        } else {
            generateDocumentation(System.out);
        }
    }

    /// Writes the documentation of this generator in markdown format.
    protected abstract void generateDocumentation(PrintStream out);

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
