

package java.io;

public class StreamTokenizer {
    public static final int TT_EOF = -1;
    public static final int TT_EOL = '\n';
    public static final int TT_NUMBER = -2;
    public static final int TT_WORD = -3;
    public int ttype;
    public String sval;
    public double nval;
    public StreamTokenizer(InputStream is) {}
    public StreamTokenizer(Reader r) {}
    public void commentChar(int ch) {}
    public void eolIsSignificant(boolean flag) {}
    public int lineno() {}
    public void lowerCaseMode(boolean flag) {}

    private boolean isWhitespace(int ch) {}

    private boolean isAlphabetic(int ch) {}

    private boolean isNumeric(int ch) {}

    private boolean isQuote(int ch) {}

    private boolean isComment(int ch) {}
    public int nextToken() throws IOException {}

    private void resetChar(int ch) {}
    public void ordinaryChar(int ch) {}
    public void ordinaryChars(int low, int hi) {}
    public void parseNumbers() {}
    public void pushBack() {}
    public void quoteChar(int ch) {}
    public void resetSyntax() {}
    public void slashSlashComments(boolean flag) {}
    public void slashStarComments(boolean flag) {}
    public String toString() {}
    public void whitespaceChars(int low, int hi) {}
    public void wordChars(int low, int hi) {}
}
