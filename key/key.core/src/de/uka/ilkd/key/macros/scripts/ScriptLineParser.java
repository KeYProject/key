package de.uka.ilkd.key.macros.scripts;

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.util.HashMap;
import java.util.Map;

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

    private static final String ADMISSIBLE_CHARS = "-_$";

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

    /**
     * number of characters read so far
     */
    private int readChars;

    private String file;

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
        /* within an identifier after "=" (to distinguish from IN_ID)*/
        IN_UNQUOTE,
        /* within a (single line) comment */
        IN_COMMENT
    }

    public ScriptLineParser(Reader reader) {
        this.reader = reader;
        this.file = null;
    }

    public ScriptLineParser(String filename) throws IOException {
        this.reader = new FileReader(filename);
        this.file = filename;
    }

    public Map<String, String> parseCommand() throws IOException, ScriptException {
        Map<String, String> result = new HashMap<String, String>();

        StringBuilder cmdBuilder = new StringBuilder();
        StringBuilder sb = new StringBuilder();
        String key = null;
        State state = State.INIT;
        State stateBeforeComment = null;
        int impCounter = 1;

        while(true) {
            int c = reader.read();

            if(c == '\n') {
                line++;
                col = 1;
            } else {
                col ++;
            }

            switch(c) {
            case -1:
                if(sb.length() > 0 || key != null || !result.isEmpty()) {
                    throw new ScriptException("Trailing characters at end of script (missing ';'?)",
                            file, line, col);
                }
                return null;
            case '=':
                switch(state) {
                case IN_ID: state = State.AFTER_EQ; key = sb.toString(); sb.setLength(0); break;
                case IN_QUOTE: sb.append((char)c); break;
                case IN_COMMENT: break;
                default: exc(c);
                }
                break;
            case ' ':
            case '\t':
            case '\n':
                switch(state) {
                case IN_ID: state = State.INIT;
                    result.put("#" + (impCounter++), sb.toString());
                    sb.setLength(0); break;
                case IN_QUOTE: sb.append((char)c); break;
                case IN_UNQUOTE: state = State.INIT;
                    result.put(key, sb.toString()); sb.setLength(0); break;
                case IN_COMMENT: if(c=='\n') { state = stateBeforeComment; } break;
                default: break;
                }
                break;
            case '\r': break;
            case '"':
                switch(state) {
                case INIT: state = State.IN_QUOTE; key = "#" + (impCounter++); break;
                case AFTER_EQ: state = State.IN_QUOTE; break;
                case IN_QUOTE: state = State.INIT;
                    result.put(key, sb.toString()); sb.setLength(0); break;
                case IN_COMMENT: break;
                default: exc(c);
                }
                break;
            case '#':
                switch(state) {
                case IN_QUOTE: sb.append((char)c); break;
                case IN_COMMENT: break;
                default: stateBeforeComment = state; state = State.IN_COMMENT;
                }
                break;
            case ';':
                switch(state) {
                case IN_QUOTE: sb.append((char)c); break;
                case IN_COMMENT: break;
                case IN_ID: result.put("#" + (impCounter++), sb.toString()); break;
                case INIT: break;
                case IN_UNQUOTE: result.put(key, sb.toString()); break;
                default: exc(c);
                }
                if(state != State.IN_COMMENT) {
                    result.put(LITERAL_KEY, cmdBuilder.toString().trim());
                    return result;
                }
                break;
            default:
                switch(state) {
                case INIT:
                case IN_ID: state = State.IN_ID; // fallthru intended!
                    if(!isIDChar(c)) {
                        exc(c);
                    }
                    sb.append((char)c); break;
                case IN_UNQUOTE:
                case AFTER_EQ: state = State.IN_UNQUOTE;
                    if(!isIDChar(c)) {
                        exc(c);
                    }
                    sb.append((char)c); break;
                case IN_QUOTE: sb.append((char)c); break;
                case IN_COMMENT: break;
                default: assert false;
                }
            }
            if(state != State.IN_COMMENT) {
                cmdBuilder.append((char)c);
            }
            readChars ++;
        }
    }

    private boolean isIDChar(int c) {
        return Character.isLetterOrDigit(c) || ADMISSIBLE_CHARS.indexOf((char)c) > -1;
    }

    private void exc(int c) throws ScriptException {
        throw new ScriptException("Unexpected char '" + (char)c + "' at " + line + ":" + col,
                file, line, col);
    }

    // TODO make this a testcase
    public static void main(String[] args) throws Exception {

        String arg = "macro key1=value1 key2=\"value two\" defval3 \"long defvalue\"; " +
                "command ; \n\n" +
                "# some comment\n" +
                "multiline #comment internal\n command \n with=\"line breaks in \n values\"; \n" +
                "hyphened-command;\n" +
                "ignored ";

        ScriptLineParser mlp = new ScriptLineParser(new StringReader(arg));
        Map<String, String> str;
        while((str = mlp.parseCommand()) != null) {
            System.err.println(str);
        }
    }

    /**
     * Get the number of characters read so far.
     *
     * @return a non-negative integer
     */
    public int getReadChars() {
        return readChars;
    }

    public int getLine() {
        return line;
    }

    public int getColumn() {
        return col;
    }

}
