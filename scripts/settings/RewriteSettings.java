/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

import de.uka.ilkd.key.nparser.KeYLexer;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.settings.ProofSettings;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.misc.ParseCancellationException;

import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.Iterator;
import java.util.zip.GZIPInputStream;
import java.util.zip.GZIPOutputStream;

/// This is a java program for rewriting the settings of KeY files from the old format to the new format.
/// The old format was a string contain a properties file (`key=value`). The new format is JSON-like tree structure
/// with the advantage of type safety and structureness.
///
/// ## How to run the program
/// 1. Compile key to receive a fatjar
/// ```sh
/// key> gradle assemble
///```
///
/// 2. Run this program using the shadow jar. Requires a rather new JDK/JRE:
/// ```sh
/// java -cp ../../key.ui/build/libs/key-2.12.4-dev-exe.jar RewriteSettings.java <files>
///```
/// (no compilation needed)
///
/// @author Alexander Weigl
/// @version 1 (4/6/25)
public class RewriteSettings {
    public static void main(String[] args) throws IOException {
        if (args.length == 0) {
            args = new String[]{
                    "../../key.core/src/test/resources/testcase/parser/MultipleRecursion/MultipleRecursion[MultipleRecursion__a()]_JML_normal_behavior_operation_contract_0.proof"};
        }

        for (String arg : args) {
            var path = Paths.get(arg);
            var files = Files.isDirectory(
                    path) ? Files.walk(path).filter(it -> Files.isRegularFile(it)
                            && (it.getFileName().toString().endsWith(".key") ||
                            it.getFileName().toString().endsWith(".proof")))
                    .toList()
                    : Collections.singletonList(path);
            for (var file : files) {
                rewrite(file);
            }

        }
    }

    private static void rewrite(Path file) throws IOException {
        boolean isGzip = file.getFileName().toString().endsWith(".gz");
        KeYLexer lex;
        if (isGzip) {
            var input = CharStreams.fromStream(new GZIPInputStream(Files.newInputStream(file)));
            lex = ParsingFacade.createLexer(input);
        } else {
            lex = ParsingFacade.createLexer(file);
        }
        lex.setProofIsEOF(false);
        var ctx = lex.getAllTokens();
        var output = new StringBuilder();

        boolean hit = false;
        for (Iterator<? extends Token> iterator = ctx.iterator(); iterator.hasNext(); ) {
            var token = iterator.next();
            if (token.getType() == KeYLexer.KEYSETTINGS) {
                output.append(token.getText());

                while (iterator.hasNext() && token.getType() != KeYLexer.STRING_LITERAL) {
                    token = iterator.next();
                }

                if (token.getType() != KeYLexer.STRING_LITERAL) {
                    return;
                }

                hit = true;

                final var text = token.getText();
                var settings = new ProofSettings(ProofSettings.DEFAULT_SETTINGS);
                settings.loadSettingsFromPropertyString(text.substring(1, text.length() - 1));
                output.append(settings.settingsToString());

                while (iterator.hasNext() && token.getType() != KeYLexer.RBRACE) {
                    token = iterator.next();
                }
            } else {
                output.append(token.getText());
            }
        }

        if (!hit) {
            System.err.printf("No settings in file %s found%n", file);
            return;
        }

        try {
            ParsingFacade.parseFile(CharStreams.fromString(output.toString()));
            if (!isGzip) {
                Files.writeString(file, output.toString());
            } else {
                try (var out = new GZIPOutputStream(Files.newOutputStream(file))) {
                    out.write(output.toString().getBytes(Charset.defaultCharset()));
                }
            }
        } catch (ParseCancellationException e) {
            System.err.printf("Error parsing after rewrite file %s: %s", file, e.getMessage());
            System.err.println(output);
            System.exit(1);
        }
    }
}

