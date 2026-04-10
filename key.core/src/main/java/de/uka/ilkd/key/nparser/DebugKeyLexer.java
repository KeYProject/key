/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.util.*;
import java.util.stream.Collectors;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonToken;
import org.antlr.v4.runtime.Token;

/**
 * This program is a little for debugging KeY Lexer.
 * <p>
 * You can start this problem via gradle: <code>
 * <pre>
 * gradle debugLexer
 * </pre>
 * </code>
 * <p>
 * This program ask for input, lexes it and shows the found token.
 *
 * @author weigl
 * @version 2019-12-09
 */
public class DebugKeyLexer {
    private static final String DEFAULT_FORMAT = "%02d %20s %d:%-50s\n";
    private final PrintStream stream;
    private final String format;
    private final Collection<KeYLexer> lexer;

    public DebugKeyLexer(PrintStream stream, String format, Collection<KeYLexer> lexer) {
        this.stream = stream;
        this.format = format;
        this.lexer = lexer;
    }

    public DebugKeyLexer(List<File> files) {
        stream = System.out;
        lexer = files.stream().map(it -> {
            try {
                return ParsingFacade.createLexer(it.toPath());
            } catch (IOException e) {
                e.printStackTrace(stream);
            }
            return null;
        }).filter(Objects::nonNull).collect(Collectors.toList());
        format = DEFAULT_FORMAT;
    }

    public static void main(String[] args) {
        if (args.length > 0) {
            new DebugKeyLexer(Arrays.stream(args).map(File::new).collect(Collectors.toList()))
                    .run();
        } else {
            try (BufferedReader input =
                new BufferedReader(new InputStreamReader(System.in, StandardCharsets.UTF_8))) {
                String tmp;
                do {
                    System.out.print(">>> ");
                    tmp = input.readLine();
                    if (tmp != null) {
                        debug(tmp);
                    } else {
                        break;
                    }
                } while (true);
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    public static void debug(String content) {
        debug(ParsingFacade.createLexer(CharStreams.fromString(content)));
    }

    public static void debug(KeYLexer lexer) {
        DebugKeyLexer dkl =
            new DebugKeyLexer(System.out, DEFAULT_FORMAT, Collections.singleton(lexer));
        dkl.run();
    }

    public void run() {
        for (KeYLexer l : lexer) {
            run(l);
        }
    }

    private void run(KeYLexer toks) {
        Token t;
        do {
            t = toks.nextToken();
            stream.format(format, toks.getLine(), toks.getVocabulary().getSymbolicName(t.getType()),
                toks._mode, t.getText().replace("\n", "\\n"));
            if (t.getType() == KeYLexer.ERROR_CHAR) {
                stream.println("!!ERROR!!");
            }
        } while (t.getType() != CommonToken.EOF);
    }
}
