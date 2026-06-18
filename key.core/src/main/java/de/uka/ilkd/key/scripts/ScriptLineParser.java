/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.io.IOException;
import java.io.Reader;
import java.net.URI;
import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;

import org.jspecify.annotations.Nullable;

/**
 *
 * @author mattias ulbrich
 *
 */
class ScriptLineParser {

    /**
     * Under this key, the command of
     */
    public static final String COMMAND_KEY = "#1";

    public static final String LITERAL_KEY = "#literal";

    private static final String ADMISSIBLE_CHARS = "-_$@";

    /**
     * This is the source of characters
     */
    private final Reader reader;

    /**
     * current column number
     */
    private int col;

    /**
     * current line number
     */
    private int line = 1;

    private int pos = 0;

    /**
     * the file URL from which the script is taken.
     */
    private URI fileURI;

    /**
     * While within a string literal, this stores the character with which the string has started.
     */
    private int stringInitChar;

    /**
     * The state of the regular expression parser.
     */
    enum State {
        /* initial, between arguments, between commands */
        INIT,
        /* within an identifier */
        IN_ID,
        /* after having observed a "=" */
        AFTER_EQ,
        /* after having observed a "\"" and before seeing it again */
        IN_QUOTE,
        /* within an identifier after "=" (to distinguish from IN_ID) */
        IN_UNQUOTE,
        /* within a (single line) comment */
        IN_COMMENT
    }

    public ScriptLineParser(Reader reader, @Nullable Location initialLocation) {
        this.reader = reader;
        if (initialLocation != null) {
            this.fileURI = initialLocation.getFileURI().orElse(null);
            this.line = initialLocation.getPosition().line();
            this.col = initialLocation.getPosition().column();
        }
    }

    public ParsedCommand parseCommand() throws IOException, ScriptException {
        Map<String, String> result = new HashMap<>();

        StringBuilder cmdBuilder = new StringBuilder();
        StringBuilder sb = new StringBuilder();
        String key = null;
        State state = State.INIT;
        State stateBeforeComment = null;
        int impCounter = 1;
        Location start = null;

        while (true) {
            int c = reader.read();

            if (c == '\n') {
                line++;
                col = 1;
            } else {
                col++;
            }
            pos++;

            if (start == null && !Character.isWhitespace(c)) {
                start = getLocation();
            }

            switch (c) {
                case -1 -> {
                    if (!sb.isEmpty() || key != null || !result.isEmpty()) {
                        throw new ScriptException(
                            "Trailing characters at end of script (missing ';'?)",
                            getLocation());
                    }
                    return null;
                }
                case '=' -> {
                    switch (state) {
                        case IN_ID -> {
                            state = State.AFTER_EQ;
                            key = sb.toString();
                            sb.setLength(0);
                        }
                        case IN_QUOTE -> sb.append((char) c);
                        case IN_COMMENT -> {
                        }
                        default -> exc(c);
                    }
                }
                case ' ', '\t', '\n' -> {
                    switch (state) {
                        case IN_ID -> {
                            state = State.INIT;
                            result.put("#" + (impCounter++), sb.toString());
                            sb.setLength(0);
                        }
                        case IN_QUOTE -> sb.append((char) c);
                        case IN_UNQUOTE -> {
                            state = State.INIT;
                            result.put(key, sb.toString());
                            sb.setLength(0);
                        }
                        case IN_COMMENT -> {
                            if (c == '\n') {
                                state = stateBeforeComment;
                            }
                        }
                        default -> {
                        }
                    }
                }
                case '\r' -> {
                }
                case '"', '\'' -> {
                    switch (state) {
                        case INIT -> {
                            state = State.IN_QUOTE;
                            stringInitChar = c;
                            key = "#" + (impCounter++);
                        }
                        case AFTER_EQ -> {
                            state = State.IN_QUOTE;
                            stringInitChar = c;
                        }
                        case IN_QUOTE -> {
                            if (stringInitChar == c) {
                                state = State.INIT;
                                result.put(key, sb.toString());
                                sb.setLength(0);
                            } else {
                                sb.append((char) c);
                            }
                        }
                        case IN_COMMENT -> {
                        }
                        default -> exc(c);
                    }
                }
                case '#' -> {
                    switch (state) {
                        case IN_QUOTE -> sb.append((char) c);
                        case IN_COMMENT -> {
                        }
                        default -> {
                            stateBeforeComment = state;
                            state = State.IN_COMMENT;
                        }
                    }
                }
                case ';' -> {
                    switch (state) {
                        case IN_QUOTE -> sb.append((char) c);
                        case IN_COMMENT, INIT -> {
                        }
                        case IN_ID -> result.put("#" + (impCounter++), sb.toString());
                        case IN_UNQUOTE -> result.put(key, sb.toString());
                        default -> exc(c);
                    }
                    if (state != State.IN_COMMENT && state != State.IN_QUOTE) {
                        result.put(LITERAL_KEY, cmdBuilder.toString().trim());
                        var end = getLocation();
                        return new ParsedCommand(result, start, end);
                    }
                }
                default -> {
                    switch (state) {
                        case INIT, IN_ID -> {
                            state = State.IN_ID; // fallthru intended!
                            if (!isIDChar(c)) {
                                exc(c);
                            }
                            sb.append((char) c);
                        }
                        case IN_UNQUOTE, AFTER_EQ -> {
                            state = State.IN_UNQUOTE;
                            if (!isIDChar(c)) {
                                exc(c);
                            }
                            sb.append((char) c);
                        }
                        case IN_QUOTE -> sb.append((char) c);
                        case IN_COMMENT -> {
                        }
                        default -> {
                            assert false;
                        }
                    }
                }
            }
            if (state != State.IN_COMMENT) {
                cmdBuilder.append((char) c);
            }
        }
    }

    private static boolean isIDChar(int c) {
        return Character.isLetterOrDigit(c) || ADMISSIBLE_CHARS.indexOf((char) c) > -1;
    }

    private void exc(int c) throws ScriptException {
        throw new ScriptException(
            String.format("Unexpected char '%s' at %d:%d", (char) c, line, col), getLocation());
    }

    private Location getLocation() {
        return new Location(fileURI, Position.newOneBased(line, col));
    }

    public int getOffset() {
        return pos;
    }

    public record ParsedCommand(Map<String, String> args, Location start, Location end) {
    }
}
