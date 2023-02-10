package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.declaration.modifier.Final;
import de.uka.ilkd.key.java.declaration.modifier.Private;
import de.uka.ilkd.key.java.declaration.modifier.Protected;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.expression.*;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.expression.operator.adt.SeqGet;
import de.uka.ilkd.key.java.expression.operator.adt.SeqLength;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.key.util.Debug;
import org.key_project.util.collection.ImmutableArray;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.*;

/**
 * A configurable pretty printer for Java source elements originally from COMPOST.
 *
 * @author AL
 *
 *         CHANGED FOR KeY. Comments are not printed!
 */
public class PrettyPrinter {
    private static final Logger LOGGER = LoggerFactory.getLogger(PrettyPrinter.class);

    /**
     * Line number, not directly used.
     */
    private int line = 0;

    /**
     * Column number. Used to keep track of indentations.
     */
    private int column = 0;

    /**
     * Level.
     */
    protected int level = 0;
    protected StringBuilder out;
    protected StringBuffer outBuf;
    protected boolean noLinefeed = false;
    protected boolean noSemicolons = false;

    protected int firstStatementStart = -1;
    protected int firstStatementEnd = -1;
    protected boolean startAlreadyMarked = false;
    protected boolean endAlreadyMarked = false;
    protected Object firstStatement = null;
    protected SVInstantiations instantiations = SVInstantiations.EMPTY_SVINSTANTIATIONS;

    /** Remembers the start of a keyword to create a range. */
    private final Stack<Integer> keywordStarts = new Stack<>();

    /** Contains the java keyword ranges. */
    private ArrayList<Range> keywordRanges = new ArrayList<>();

    /** creates a new PrettyPrinter */
    public PrettyPrinter(StringBuilder out) {
        setWriter(out);
        outBuf = new StringBuffer();
    }

    public PrettyPrinter(StringBuilder o, SVInstantiations svi) {
        this(o);
        this.instantiations = svi;
    }

    public PrettyPrinter(StringBuilder o, boolean noLinefeed) {
        this(o);
        this.noLinefeed = noLinefeed;
    }

    public PrettyPrinter(StringBuilder o, boolean noLinefeed, SVInstantiations svi) {
        this(o, noLinefeed);
        this.instantiations = svi;
    }


    /** The number of charcters that have been send to the writer */
    protected int writtenCharacters = 0;

    protected void output() {
        if (noSemicolons)
            removeChar(outBuf, ';');
        if (noLinefeed)
            removeChar(outBuf, '\n');
        String toWrite = outBuf.toString();
        writtenCharacters += toWrite.length();
        out.append(toWrite);
        outBuf = new StringBuffer();

    }

    /** Numbers of generated characters */
    protected int getCurrentPos() {
        return writtenCharacters + outBuf.length();
    }

    /**
     * Marks the start of the first executable statement ...
     *
     * @param n offset from the current position
     * @param stmt current statement;
     */
    protected void markStart(int n, Object stmt) {
        if (!startAlreadyMarked) {
            firstStatementStart = getCurrentPos() + n;
            firstStatement = stmt;
            startAlreadyMarked = true;
        }
    }

    /**
     * Marks the end of the first executable statement ...
     *
     * @param n offset from the current position
     */
    protected void markEnd(int n, Object stmt) {
        if (!endAlreadyMarked && (firstStatement == stmt)) {
            firstStatementEnd = getCurrentPos() + n;
            endAlreadyMarked = true;
        }
    }

    /**
     * @return the range of the first executable statement that means the corresponding start and
     *         end position in the string representation
     */
    public Range getRangeOfFirstExecutableStatement() {
        return new Range(firstStatementStart, firstStatementEnd);
    }

    /**
     * Marks the start of a java keyword.
     */
    protected final void markKeywordStart() {
        keywordStarts.push(getCurrentPos());
    }

    /**
     * Marks the end of a java keyword and creates a keyword range.
     */
    protected final void markKeywordEnd() {
        keywordRanges.add(new Range(keywordStarts.pop(), getCurrentPos()));
    }

    /**
     * @return ranges of all java keywords printed.
     */
    public final Range[] getKeywordRanges() {
        return keywordRanges.toArray(new Range[0]);
    }

    /**
     * Resets the state of this pretty printer ...
     */
    public void reset() {
        firstStatementStart = -1;
        firstStatementEnd = -1;
        firstStatement = null;
        startAlreadyMarked = false;
        endAlreadyMarked = false;
        writtenCharacters = 0;
        outBuf = new StringBuffer();
        keywordRanges = new ArrayList<>();
    }


    /**
     * Flag to indicate if a single line comment is being put out. Needed to disable the worklist
     * meanwhile.
     */
    private final boolean isPrintingSingleLineComments = false;


    protected HashMap<SourceElement, Position> indentMap = new LinkedHashMap<>();

    /**
     * Set a new stream to write to. Useful to redirect the output while retaining all other
     * settings. Resets the current source positions and comments.
     */
    public void setWriter(StringBuilder out) {
        this.out = out;
        column = 0;
        line = 0;
    }

    /**
     * Get current line number.
     *
     * @return the line number, starting with 0.
     */
    public int getLine() {
        return line;
    }

    /**
     * Get current column number.
     *
     * @return the column number, starting with 0.
     */
    public int getColumn() {
        return column;
    }

    /**
     * Set indentation level.
     *
     * @param level an int value.
     */
    public void setIndentationLevel(int level) {
        this.level = level;
    }

    /**
     * Get total indentation.
     *
     * @return the int value.
     */
    public int getTotalIndentation() {
        return INDENTATION * level;
    }

    /**
     * Change level.
     *
     * @param delta an int value.
     */
    public void changeLevel(int delta) {
        level += delta;
    }

    private static final char[] BLANKS = new char[128];

    private static final char[] FEEDS = new char[8];

    static {
        Arrays.fill(FEEDS, '\n');
        Arrays.fill(BLANKS, ' ');
    }

    /**
     * Convenience method to write indentation chars.
     */
    protected void writeIndentation(int lf, int blanks) {
        if (!noLinefeed) {
            if (lf > 0) {
                do {
                    int n = Math.min(lf, FEEDS.length);
                    write(FEEDS, 0, n);
                    lf -= n;
                } while (lf > 0);
            }
            while (blanks > 0) {
                int n = Math.min(blanks, BLANKS.length);
                write(BLANKS, 0, n);
                blanks -= n;
            }
        }
    }

    /**
     * Convenience method to write indentation chars.
     */
    protected void writeIndentation(Position relative) {
        writeIndentation(relative.getLine(), relative.getColumn());
    }

    /**
     * Write indentation.
     *
     * @param elem a source element.
     */
    protected void writeIndentation(SourceElement elem) {
        writeIndentation(getRelativePosition(elem.getFirstElement()));
    }

    /**
     * Write internal indentation.
     *
     * @param elem a source element.
     */
    protected void writeInternalIndentation(SourceElement elem) {
        writeIndentation(getRelativePosition(elem));
    }


    /**
     * Write symbol.
     *
     * @param lf an int value.
     * @param levelChange an int value.
     * @param symbol a string.
     */
    protected void writeSymbol(int lf, int levelChange, String symbol) {
        level += levelChange;
        writeIndentation(lf, getTotalIndentation());
        boolean isKey = (symbol.equals("int") || symbol.equals("float") || symbol.equals("char")
                || symbol.equals("short") || symbol.equals("long") || symbol.equals("boolean"));
        if (isKey) {
            markKeywordStart();
        }
        write(symbol);
        if (isKey) {
            markKeywordEnd();
        }
    }

    /**
     * Replace all unicode characters above ? by their explicit representation.
     *
     * @param str the input string.
     * @return the encoded string.
     */
    protected static String encodeUnicodeChars(String str) {
        int len = str.length();
        StringBuilder buf = new StringBuilder(len + 4);
        for (int i = 0; i < len; i += 1) {
            char c = str.charAt(i);
            if (c >= 0x0100) {
                if (c < 0x1000) {
                    buf.append("\\u0").append(Integer.toString(c, 16));
                } else {
                    buf.append("\\u").append(Integer.toString(c, 16));
                }
            } else {
                buf.append(c);
            }
        }
        return buf.toString();
    }

    /**
     * Store the given comment until the next line feed is written.
     *
     * @param slc the comment to delay.
     */
    protected void scheduleComment(SingleLineComment slc) {
    }

    /**
     * Adds indentation for a program element if necessary and if required, but does not print the
     * indentation itself.
     */
    protected void writeElement(int lf, int levelChange, int blanks, SourceElement elem) {
        level += levelChange;
        if (lf > 0) {
            blanks += getTotalIndentation();
        }
        SourceElement first = elem.getFirstElement();
        Position indent = getRelativePosition(first);
        if (indent == Position.UNDEFINED) {
            indent = new Position(lf, blanks);
        } else {
            if (lf > indent.getLine()) {
                indent = new Position(lf, indent.getColumn());
            }
            if (blanks > indent.getColumn()) {
                indent = new Position(indent.getLine(), blanks);
            }
        }
        indentMap.put(first, indent);
        elem.prettyPrint(this);
    }

    protected Position getRelativePosition(SourceElement first) {
        if (indentMap.containsKey(first)) {
            return indentMap.get(first);
        } else {
            if (first != null)
                return first.getRelativePosition();

        }

        return Position.UNDEFINED;
    }

    /**
     * Writes an implicit terminal token of a NonTerminal, including its indentation. Sets the
     * indentation if it is necessary or required.
     *
     * @see SourceElement#prettyPrint
     */
    protected void writeToken(int lf, int blanks, String image, NonTerminalProgramElement parent) {
        if (lf > 0) {
            blanks += getTotalIndentation();
        }
        Position indent = getRelativePosition(parent);
        if (indent == Position.UNDEFINED) {
            indent = new Position(lf, blanks);
        } else {
            if (lf > indent.getLine()) {
                indent = new Position(lf, indent.getColumn());
            }
            if (blanks > indent.getColumn()) {
                indent = new Position(indent.getLine(), blanks);
            }
        }
        indentMap.put(parent.getFirstElement(), indent); // needed ?????
        writeIndentation(indent);
        // if (overwriteParsePositions) {
        // parent.setInternalParsedLine(line);
        // parent.setInternalParsedColumn(column);
        // }
        if (image.equals("catch")) {
            markKeywordStart();
            // XXX space before image is a dirty fix for bug where c of catch would not be
            // highlighted
            write(" ");
        }
        write(image);
        if (image.equals("catch")) {
            markKeywordEnd();
        }
    }

    protected final void writeToken(int blanks, String image, NonTerminalProgramElement parent) {
        writeToken(0, blanks, image, parent);
    }

    protected final void writeToken(String image, NonTerminalProgramElement parent) {
        writeToken(0, 0, image, parent);
    }

    /**
     * Write a source element.
     *
     * @param lf an int value.
     * @param blanks an int value.
     * @param elem a source element.
     */
    protected void writeElement(int lf, int blanks, SourceElement elem) {
        writeElement(lf, 0, blanks, elem);
    }

    /**
     * Write source element.
     *
     * @param blanks an int value.
     * @param elem a source element.
     */
    protected void writeElement(int blanks, SourceElement elem) {
        writeElement(0, 0, blanks, elem);
    }

    /**
     * Write source element.
     *
     * @param elem a source element.
     */
    protected void writeElement(SourceElement elem) {
        writeElement(0, 0, 0, elem);
    }

    /**
     * Write a complete ArrayOf<ProgramElement>.
     */
    protected void writeImmutableArrayOfProgramElement(int firstLF, int levelChange,
            int firstBlanks, String separationSymbol, int separationLF, int separationBlanks,
            ImmutableArray<? extends ProgramElement> list) {
        int s = list.size();
        if (s == 0) {
            return;
        }
        writeElement(firstLF, levelChange, firstBlanks, list.get(0));
        for (int i = 1; i < s; i += 1) {
            write(separationSymbol);
            writeElement(separationLF, separationBlanks, list.get(i));
        }
    }

    /**
     * Write a complete ArrayOf<ProgramElement> using "Keyword" style.
     */
    protected void writeKeywordList(int firstLF, int levelChange, int firstBlanks,
            ImmutableArray<? extends ProgramElement> list) {
        writeImmutableArrayOfProgramElement(firstLF, levelChange, firstBlanks, "", 0, 1, list);
    }

    /**
     * Write keyword list.
     *
     * @param list a program element list.
     */
    protected void writeKeywordList(ImmutableArray<? extends ProgramElement> list) {
        writeImmutableArrayOfProgramElement(0, 0, 0, "", 0, 1, list);
    }

    /**
     * Write a complete ArrayOf<ProgramElement> using "Comma" style.
     */
    protected void writeCommaList(int firstLF, int levelChange, int firstBlanks,
            ImmutableArray<? extends ProgramElement> list) {
        writeImmutableArrayOfProgramElement(firstLF, levelChange, firstBlanks, ",", 0, 1, list);
    }

    /**
     * Write comma list.
     *
     * @param list a program element list.
     */
    protected void writeCommaList(int separationBlanks,
            ImmutableArray<? extends ProgramElement> list) {
        writeImmutableArrayOfProgramElement(0, 0, 0, ",", 0, separationBlanks, list);
    }

    /**
     * Write comma list.
     *
     * @param list a program element list.
     */
    protected void writeCommaList(ImmutableArray<? extends ProgramElement> list) {
        writeImmutableArrayOfProgramElement(0, 0, 0, ",", 0, 1, list);
    }

    /**
     * Write a complete ArrayOf<ProgramElement> using "Line" style.
     */
    protected void writeLineList(int firstLF, int levelChange, int firstBlanks,
            ImmutableArray<? extends ProgramElement> list) {
        writeImmutableArrayOfProgramElement(firstLF, levelChange, firstBlanks, "", 1, 0, list);
    }

    /**
     * Write line list.
     *
     * @param list a program element list.
     */
    protected void writeLineList(ImmutableArray<? extends ProgramElement> list) {
        writeImmutableArrayOfProgramElement(0, 0, 0, "", 1, 0, list);
    }

    /**
     * Write a complete ArrayOf<ProgramElement> using "Block" style.
     */
    protected void writeBlockList(int firstLF, int levelChange, int firstBlanks,
            ImmutableArray<? extends ProgramElement> list) {
        writeImmutableArrayOfProgramElement(firstLF, levelChange, firstBlanks, "", 2, 0, list);
    }

    /**
     * Write block list.
     *
     * @param list a program element list.
     */
    protected void writeBlockList(ImmutableArray<? extends ProgramElement> list) {
        writeImmutableArrayOfProgramElement(0, 0, 0, "", 2, 0, list);
    }

    private void dumpComments() {
    }

    /**
     * Write.
     *
     * @param c an int value.
     */
    public void write(int c) {
        if (c == '\n') {
            if (!isPrintingSingleLineComments) {
                dumpComments();
            }
            column = 0;
            line += 1;
        } else {
            column += 1;
        }
        outBuf.append(c);
    }

    /**
     * Write.
     *
     * @param cbuf a char value.
     */
    public void write(char[] cbuf) {
        write(cbuf, 0, cbuf.length);
    }

    /**
     * Write.
     *
     * @param cbuf an array of char.
     * @param off an int value.
     * @param len an int value.
     */
    public void write(char[] cbuf, int off, int len) {
        boolean col = false;

        for (int i = off + len - 1; i >= off; i -= 1) {
            if (cbuf[i] == '\n') {
                if (!isPrintingSingleLineComments) {
                    dumpComments();
                }
                line += 1;
                if (!col) {
                    column = (off + len - 1 - i);
                    col = true;
                }
            }
        }
        if (!col) {
            column += len;
            /*
             * int i; for (i = off + len - 1; (i >= off && cbuf[i] != '\n'); i -= 1) ; column = (i
             * >= off) ? (off + len - 1 - i) : (column + len);
             */
        }
        outBuf.append(cbuf, off, len);
    }

    /**
     * Write.
     *
     * @param str a string.
     */
    public void write(String str) {
        int i = str.lastIndexOf('\n');
        if (i >= 0) {
            column = str.length() - i + 1;
            do {
                dumpComments();
                line += 1;
                i = str.lastIndexOf('\n', i - 1);
            } while (i >= 0);
        } else {
            column += str.length();
        }
        outBuf.append(str);
    }

    /**
     * Write.
     *
     * @param str a string.
     * @param off an int value.
     * @param len an int value.
     */
    public void write(String str, int off, int len) {
        write(str.substring(off, off + len));
    }

    private static final int INDENTATION = 2;

    /**
     * Print program element header.
     *
     * @param lf an int value.
     * @param blanks an int value.
     * @param elem a program element.
     */
    protected void printHeader(int lf, int blanks, ProgramElement elem) {

        printHeader(lf, 0, blanks, elem);
    }

    /**
     * Print program element header.
     *
     * @param blanks an int value.
     * @param elem a program element.
     */
    protected void printHeader(int blanks, ProgramElement elem) {
        printHeader(0, 0, blanks, elem);
    }

    /**
     * Print program element header.
     *
     * @param elem a program element.
     */
    protected void printHeader(ProgramElement elem) {
        printHeader(0, 0, 0, elem);
    }


    /**
     * Print program element header.
     *
     * @param lf number of line feeds.
     * @param levelChange the level change.
     * @param blanks number of white spaces.
     * @param x the program element.
     */
    protected void printHeader(int lf, int levelChange, int blanks, ProgramElement x) {

        level += levelChange;
        if (lf > 0) {
            blanks += getTotalIndentation();
        }
        SourceElement first = x.getFirstElement();
        Position indent = getRelativePosition(first);
        if (indent == Position.UNDEFINED) {
            indent = new Position(lf, blanks);
        } else {
            if (lf > indent.getLine()) {
                indent = new Position(lf, indent.getColumn());
            }
            if (blanks > indent.getColumn()) {
                indent = new Position(indent.getLine(), blanks);
            }
        }
        indentMap.put(first, indent);
    }


    /**
     * Print program element footer.
     *
     * @param x the program element.
     */
    protected void printFooter(ProgramElement x) {
        output();
    }


    protected void printOperator(Operator x, String symbol) {

        // Mark statement start ...
        markStart(0, x);


        ImmutableArray<Expression> children = x.getArguments();
        if (children != null) {
            // boolean addParentheses = x.isToBeParenthesized();
            // if (addParentheses) {
            // write('(');
            // } //????

            if (!noLinefeed) {
                writeSymbol(1, 0, "");
            }
            output();

            boolean wasNoSemicolons = noSemicolons;
            boolean wasNoLinefeed = noLinefeed;
            noSemicolons = true;
            // noLinefeed=true;
            switch (x.getArity()) {
            case 2:
                noLinefeed = true;
                writeElement(0, children.get(0));
                writeToken(0, symbol, x);
                output();
                writeElement(0, children.get(1));
                break;
            case 1:
                switch (x.getNotation()) {
                case Operator.PREFIX:
                    noLinefeed = true;
                    writeToken(symbol, x);
                    writeElement(0, children.get(0));
                    output();
                    break;
                case Operator.POSTFIX:
                    noLinefeed = true;
                    writeElement(0, children.get(0));
                    writeToken(1, symbol, x);
                    break;
                default:
                    break;
                }
            }
            output();
            noSemicolons = wasNoSemicolons;
            noLinefeed = wasNoLinefeed;
            // if (addParentheses) {
            // write(')');
            // } //???? as above
            if (x instanceof Assignment) {
                // if (((Assignment)x).getStatementContainer() != null) {
                write(";"); // ????


                // }
            }
            output();
            // Mark statement end ...
            markEnd(0, x);

            /*
             * if (!noLinefeed) { writeSymbol(1,0, ""); }
             */
        }
    }


    public void printProgramElementName(ProgramElementName x) {
        printHeader(x);
        writeInternalIndentation(x);
        String name = x.getProgramName();
        boolean isKey = (name.equals("int") || name.equals("float") || name.equals("char")
                || name.equals("short") || name.equals("long") || name.equals("boolean"));
        if (isKey) {
            markKeywordStart();
        }
        write(name);
        if (isKey) {
            markKeywordEnd();
        }
        printFooter(x);
    }

    public void printProgramVariable(ProgramVariable x) {

        printHeader(x);
        writeInternalIndentation(x);

        write(x.name().toString());
        printFooter(x);
    }

    public void printProgramMethod(IProgramMethod x) {

        printHeader(x);
        writeInternalIndentation(x);
        write(x.getMethodDeclaration().getProgramElementName().toString());
        printFooter(x);
    }

    public void printProgramMetaConstruct(ProgramTransformer x) {
        printHeader(x);
        write(x.name().toString());
        writeToken("(", x);
        boolean oldNoLinefeed = noLinefeed;
        noLinefeed = true;
        if (x.getChildAt(0) != null) {
            writeElement(1, +1, 0, x.getChildAt(0));
            writeSymbol(1, -1, ")");
        } else {
            write(")");
        }
        noLinefeed = oldNoLinefeed;
        printFooter(x);
    }

    public void printContextStatementBlock(ContextStatementBlock x) {
        printHeader(x);

        if (x.getStatementCount() > 0) {
            writeToken("{ .. ", x);
            writeLineList(1, +1, 0, x.getBody());
            writeSymbol(1, -1, " ... }");
        } else {
            markStart(0, x);
            writeToken("{ .. ", x);
            write(" ... }");
            markEnd(0, x);
        }
        printFooter(x);
    }

    public void printIntLiteral(IntLiteral x) {
        printHeader(x);
        writeInternalIndentation(x);
        write(x.getValueString());
        printFooter(x);
    }

    public void printBooleanLiteral(BooleanLiteral x) {
        printHeader(x);
        writeInternalIndentation(x);
        markKeywordStart();
        write(x.getValue() ? "true" : "false");
        markKeywordEnd();
        printFooter(x);
    }

    public void printEmptySetLiteral(EmptySetLiteral x) {
        printHeader(x);
        writeInternalIndentation(x);
        write("\\empty");
        printFooter(x);
    }

    public void printSingleton(de.uka.ilkd.key.java.expression.operator.adt.Singleton x) {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\singleton", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(")");
        printFooter(x);
    }

    public void printSetUnion(de.uka.ilkd.key.java.expression.operator.adt.SetUnion x) {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\set_union", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(",");
        writeElement(0, x.getChildAt(1));
        write(")");
        printFooter(x);
    }

    public void printIntersect(de.uka.ilkd.key.java.expression.operator.Intersect x) {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\intersect", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(",");
        writeElement(0, x.getChildAt(1));
        write(")");
        printFooter(x);
    }

    public void printSetMinus(de.uka.ilkd.key.java.expression.operator.adt.SetMinus x) {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\set_minus", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(",");
        writeElement(0, x.getChildAt(1));
        write(")");
        printFooter(x);
    }


    public void printAllFields(de.uka.ilkd.key.java.expression.operator.adt.AllFields x) {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\all_fields", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(")");
        printFooter(x);
    }

    public void printAllObjects(de.uka.ilkd.key.java.expression.operator.adt.AllObjects x) {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\all_objects", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(")");
        printFooter(x);
    }

    public void printEmptySeqLiteral(EmptySeqLiteral x) {
        printHeader(x);
        writeInternalIndentation(x);
        write("\\seq_empty");
        printFooter(x);
    }

    public void printSeqLength(SeqLength x) {
        printHeader(x);
        writeInternalIndentation(x);
        writeElement(0, x.getChildAt(0));
        write(".length");
        printFooter(x);
    }

    public void printSeqGet(SeqGet x) {
        printHeader(x);
        writeInternalIndentation(x);
        writeElement(0, x.getChildAt(0));
        write("[");
        writeElement(1, x.getChildAt(1));
        write("]");
        printFooter(x);
    }

    public void printSeqSingleton(de.uka.ilkd.key.java.expression.operator.adt.SeqSingleton x) {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\seq_singleton", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(")");
        printFooter(x);
    }

    public void printSeqConcat(de.uka.ilkd.key.java.expression.operator.adt.SeqConcat x) {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\seq_concat", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(",");
        writeElement(0, x.getChildAt(1));
        write(")");
        printFooter(x);
    }

    public void printIndexOf(de.uka.ilkd.key.java.expression.operator.adt.SeqIndexOf x) {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\indexOf", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(",");
        writeElement(0, x.getChildAt(1));
        write(")");
        printFooter(x);
    }

    public void printSeqSub(de.uka.ilkd.key.java.expression.operator.adt.SeqSub x) {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\seq_sub", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(",");
        writeElement(0, x.getChildAt(1));
        write(",");
        writeElement(0, x.getChildAt(2));
        write(")");
        printFooter(x);
    }

    public void printSeqReverse(de.uka.ilkd.key.java.expression.operator.adt.SeqReverse x) {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\seq_reverse", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(")");
        printFooter(x);
    }

    public void printDLEmbeddedExpression(DLEmbeddedExpression x) {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\dl_" + x.getFunctionSymbol().name(), x);
        write("(");
        for (int i = 0; i < x.getChildCount(); i++) {
            if (i != 0) {
                write(",");
            }
            writeElement(0, x.getChildAt(i));
        }
        write(")");
        printFooter(x);
    }

    public void printStringLiteral(StringLiteral x) {
        printHeader(x);
        writeInternalIndentation(x);
        write(encodeUnicodeChars(x.getValue()));
        printFooter(x);
    }

    public void printNullLiteral(NullLiteral x) {
        printHeader(x);
        writeInternalIndentation(x);
        markKeywordStart();
        write("null");
        markKeywordEnd();
        printFooter(x);
    }

    public void printCharLiteral(CharLiteral x) {
        printHeader(x);
        writeInternalIndentation(x);
        write(encodeUnicodeChars(x.toString()));
        printFooter(x);
    }

    public void printDoubleLiteral(DoubleLiteral x) {
        printHeader(x);
        writeInternalIndentation(x);
        write(x.getValue());
        printFooter(x);
    }

    public void printMergePointStatementBlock(MergePointStatement x) {
        printHeader(x);
        writeInternalIndentation(x);

        // Mark statement start ...
        markStart(0, x);

        write("//@ merge_point (");
        write(x.getExpression().toString());
        write(");");

        // Mark statement end ...
        markEnd(0, x);

        printFooter(x);
    }

    public void printLongLiteral(LongLiteral x) {
        printHeader(x);
        writeInternalIndentation(x);
        write(x.getValueString());
        printFooter(x);
    }

    public void printFloatLiteral(FloatLiteral x) {
        printHeader(x);
        writeInternalIndentation(x);
        write(x.getValue());
        printFooter(x);
    }

    public void printPackageSpecification(PackageSpecification x) {

        printHeader(x);
        writeInternalIndentation(x);
        write("package");
        writeElement(1, x.getPackageReference());
        write(";");
        printFooter(x);
    }

    public void printAssert(Assert x) {
        printHeader(x);
        writeInternalIndentation(x);

        // Mark statement start ...
        markStart(0, x);

        boolean wasNoLinefeed = noLinefeed;
        boolean wasNoSemicolon = noSemicolons;
        markKeywordStart();
        write("assert");
        markKeywordEnd();
        write(" ");

        noLinefeed = true;
        noSemicolons = true;
        writeElement(0, x.getCondition());

        if (x.getMessage() != null) {
            write(" : ");
            writeElement(0, x.getMessage());
        }

        noSemicolons = wasNoSemicolon;
        noLinefeed = wasNoLinefeed;

        write(";");

        output();
        // Mark statement end ...
        markEnd(0, x);

        printFooter(x);
    }

    public void printArrayDeclaration(ArrayDeclaration type) {
        Type baseType = type.getBaseType().getKeYJavaType().getJavaType();
        assert baseType != null;
        if (baseType instanceof ArrayDeclaration) {
            printArrayDeclaration((ArrayDeclaration) baseType);
        } else {
            writeSymbol(1, 0, baseType.getFullName());
        }
        write("[]");
    }

    public void printTypeReference(TypeReference x) {
        printTypeReference(x, false);
    }

    public void printTypeReference(TypeReference x, boolean fullTypeNames) {
        if (x.getKeYJavaType().getJavaType() instanceof ArrayDeclaration) {
            printArrayDeclaration((ArrayDeclaration) x.getKeYJavaType().getJavaType());
        } else if (x.getProgramElementName() != null) {
            printHeader(x);
            if (x.getReferencePrefix() != null) {
                write(x.getReferencePrefix() + "." + x.getProgramElementName());// XXX
                // writeElement(x.getReferencePrefix());
                // writeToken(".", x);
            } else {
                if (fullTypeNames) {
                    write(x.getKeYJavaType().getFullName());
                } else {
                    writeElement(x.getProgramElementName());
                }
            }
            printFooter(x);
        }
    }

    public void printSchemaTypeReference(SchemaTypeReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            boolean wasNoSemicolons = noSemicolons;
            noSemicolons = true;
            writeElement(x.getReferencePrefix());
            noSemicolons = wasNoSemicolons;
            writeToken(".", x);
        }

        if (x.getProgramElementName() != null) {
            writeElement(x.getProgramElementName());
        }
        printFooter(x);
    }


    public void printFieldReference(FieldReference x) {
        printHeader(x);
        if (x.getName() != null
                && "javax.realtime.MemoryArea::currentMemoryArea".equals(x.getName())) {
            write("<currentMemoryArea>");
        } else {
            if (x.getReferencePrefix() != null) {
                boolean wasNoSemicolons = noSemicolons;
                noSemicolons = true;
                writeElement(x.getReferencePrefix());
                noSemicolons = wasNoSemicolons;
                writeToken(".", x);
            }
            if (x.getProgramElementName() != null) {
                writeElement(x.getProgramElementName());
            }
        }
        printFooter(x);
    }

    public void printPackageReference(PackageReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            writeElement(x.getReferencePrefix());
            writeToken(".", x);
        }
        if (x.getProgramElementName() != null) {
            writeElement(x.getProgramElementName());
        }
        printFooter(x);
    }



    public void printThrows(Throws x) {
        printHeader(x);
        if (x.getExceptions() != null) {
            writeInternalIndentation(x);
            markKeywordStart();
            write("throws");
            markKeywordEnd();

            writeCommaList(0, 0, 1, x.getExceptions());
        }
        printFooter(x);
    }

    public void printArrayInitializer(ArrayInitializer x) {

        printHeader(x);
        writeToken("{", x);
        if (x.getArguments() != null) {
            writeCommaList(0, 0, 1, x.getArguments());
        }
        if (x.getArguments() != null && x.getArguments().size() > 0
                && getRelativePosition(x).getLine() > 0) {

            writeSymbol(1, 0, "}");
        } else {
            write(" }");
        }
        printFooter(x);
    }

    public void printCompilationUnit(CompilationUnit x) {
        printHeader(x);
        setIndentationLevel(0);
        boolean hasPackageSpec = (x.getPackageSpecification() != null);
        if (hasPackageSpec) {
            writeElement(x.getPackageSpecification());
        }
        boolean hasImports = (x.getImports() != null) && (x.getImports().size() > 0);
        if (hasImports) {
            writeLineList((x.getPackageSpecification() != null) ? 2 : 0, 0, 0, x.getImports());
        }
        if (x.getDeclarations() != null) {
            writeBlockList((hasImports || hasPackageSpec) ? 2 : 0, 0, 0, x.getDeclarations());
        }
        printFooter(x);
        // we do this linefeed here to allow flushing of the pretty printer
        // single line comment work list
        writeIndentation(1, 0);
    }

    public void printClassDeclaration(ClassDeclaration x) {
        printHeader(x);
        int m = 0;
        if (x.getModifiers() != null) {
            m = x.getModifiers().size();
        }
        if (m > 0) {
            ImmutableArray<Modifier> mods = x.getModifiers();
            writeKeywordList(mods);
            m = 1;
        }
        if (x.getProgramElementName() != null) {
            writeToken(m, "class", x);
            writeElement(1, x.getProgramElementName());
        }
        if (x.getExtendedTypes() != null) {
            writeElement(1, x.getExtendedTypes());
        }
        if (x.getImplementedTypes() != null) {
            writeElement(1, x.getImplementedTypes());
        }
        if (x.getProgramElementName() != null) {
            write(" {");
        } else { // anonymous class
            write("{");
        }
        if (x.getMembers() != null) {
            // services.getJavaInfo().getKeYProgModelInfo().getConstructors(kjt)
            writeBlockList(2, 1, 0, x.getMembers());
        }
        writeSymbol(1, (x.getMembers() != null) ? -1 : 0, "}");
        printFooter(x);
    }

    protected boolean containsDefaultConstructor(ImmutableArray<MemberDeclaration> members) {
        for (int i = 0; i < members.size(); i++) {
            MemberDeclaration md = members.get(i);
            if (md instanceof IProgramMethod) {
                md = ((IProgramMethod) md).getMethodDeclaration();
            }
            if ((md instanceof ConstructorDeclaration)
                    && ((ConstructorDeclaration) md).getParameterDeclarationCount() == 0) {
                return true;
            }
        }
        return false;
    }

    public void printInterfaceDeclaration(InterfaceDeclaration x) {

        printHeader(x);
        int m = 0;
        if (x.getModifiers() != null) {
            m = x.getModifiers().size();
        }
        if (m > 0) {
            writeKeywordList(x.getModifiers());
            m = 1;
        }
        if (x.getProgramElementName() != null) {
            writeToken(m, "interface", x);
            writeElement(1, x.getProgramElementName());
        }
        if (x.getExtendedTypes() != null) {
            writeElement(1, x.getExtendedTypes());
        }
        write(" {");
        if (x.getMembers() != null) {
            writeBlockList(2, 1, 0, x.getMembers());
        }
        writeSymbol(1, (x.getMembers() != null) ? -1 : 0, "}");
        printFooter(x);
    }

    protected ImmutableArray<Modifier> removeFinal(ImmutableArray<Modifier> ma) {
        LinkedList<Modifier> l = new LinkedList<>();
        for (Modifier mod : ma) {
            if (!(mod instanceof Final)) {
                l.add(mod);
            }
        }
        return new ImmutableArray<>(l);
    }

    protected ImmutableArray<Modifier> replacePrivateByPublic(ImmutableArray<Modifier> ma) {
        LinkedList<Modifier> l = new LinkedList<>();
        boolean publicFound = false;
        for (int i = 0; i < ma.size(); i++) {
            if (ma.get(i) instanceof Private) {
                l.add(new Public());
                publicFound = true;
            } else if (ma.get(i) instanceof Public) {
                l.add(ma.get(i));
                publicFound = true;
            } else if (ma.get(i) instanceof Protected) {
                l.add(new Public());
                publicFound = true;
            } else {
                l.add(ma.get(i));
            }
        }
        if (!publicFound) {
            l.add(new Public());
        }
        return new ImmutableArray<>(l);
    }

    public void printFieldDeclaration(FieldDeclaration x) {
        printHeader(x);
        int m = 0;
        if (x.getModifiers() != null) {
            ImmutableArray<Modifier> mods = x.getModifiers();
            m = mods.size();
            writeKeywordList(mods);
        }
        writeElement((m > 0) ? 1 : 0, x.getTypeReference());
        final ImmutableArray<? extends VariableSpecification> varSpecs = x.getVariables();
        assert varSpecs != null
                : "Strange: a field declaration without a" + " variable specification";
        writeCommaList(0, 0, 1, varSpecs);
        write(";");
        printFooter(x);

    }

    public static String getTypeNameForAccessMethods(String typeName) {
        typeName = typeName.replace('[', '_');
        return typeName.replace('.', '_');
    }

    public void printLocalVariableDeclaration(LocalVariableDeclaration x) {
        printHeader(x);
        // Mark statement start ...
        markStart(0, x);
        int m = 0;
        if (x.getModifiers() != null) {
            m = x.getModifiers().size();
            writeKeywordList(x.getModifiers());
        }
        writeElement((m > 0) ? 1 : 0, x.getTypeReference());
        write(" ");
        ImmutableArray<VariableSpecification> varSpecs = x.getVariables();
        boolean wasNoSemicolons = noSemicolons;
        boolean wasNoLinefeed = noLinefeed;
        noSemicolons = true;
        noLinefeed = true;
        if (varSpecs != null) {
            writeCommaList(0, 0, 1, varSpecs);
        }
        // !!!!!!!!!! HAS TO BE CHANGED
        // if (!(x.getStatementContainer() instanceof LoopStatement)) {
        write(";");
        // }

        // Mark statement end ...
        markEnd(0, x);
        noSemicolons = wasNoSemicolons;
        noLinefeed = wasNoLinefeed;
        printFooter(x);
    }

    public void printVariableDeclaration(VariableDeclaration x) {

        printHeader(x);

        // Mark statement start ...
        markStart(0, x);

        int m = 0;
        if (x.getModifiers() != null) {
            m = x.getModifiers().size();
            writeKeywordList(x.getModifiers());
        }
        writeElement((m > 0) ? 1 : 0, x.getTypeReference());
        write(" ");
        ImmutableArray<? extends VariableSpecification> varSpecs = x.getVariables();
        if (varSpecs != null) {
            writeCommaList(0, 0, 1, varSpecs);
        }

        // Mark statement end ...
        markEnd(0, x);

        printFooter(x);
    }

    public void printMethodDeclaration(MethodDeclaration x) {
        printHeader(x);
        Comment[] c = x.getComments();
        int m = c.length;
        for (Comment aC : c) {
            printComment(aC);
        }
        if (x.getModifiers() != null) {
            ImmutableArray<Modifier> mods = x.getModifiers();
            m += mods.size();
            writeKeywordList(mods);
        }
        if (x.getTypeReference() != null) {
            if (m > 0) {
                writeElement(1, x.getTypeReference());
            } else {
                writeElement(x.getTypeReference());
            }
            writeElement(1, x.getProgramElementName());
        } else if (x.getTypeReference() == null && !(x instanceof ConstructorDeclaration)) {
            write(" void ");
            writeElement(1, x.getProgramElementName());
        } else {
            if (m > 0) {
                writeElement(1, x.getProgramElementName());
            } else {
                writeElement(x.getProgramElementName());
            }
        }
        write(" (");
        if (x.getParameters() != null) {
            writeCommaList(1, x.getParameters());
        }
        write(")");
        if (x.getThrown() != null) {
            writeElement(1, x.getThrown());
        }
        if (x.getBody() != null) {
            writeElement(1, x.getBody());
        } else {
            write(";");
        }
        printFooter(x);
    }

    public void printClassInitializer(ClassInitializer x) {

        printHeader(x);
        int m = 0;
        if (x.getModifiers() != null) {
            m = x.getModifiers().size();
            writeKeywordList(x.getModifiers());
        }
        if (x.getBody() != null) {
            writeElement(m > 0 ? 1 : 0, x.getBody());
        }
        printFooter(x);
    }

    public void printStatementBlock(StatementBlock x) {
        printHeader(x);

        if (!(x.getBody() != null && x.getBody().size() > 0)) {
            // We have an empty statement block ...

            // Mark statement start ...
            markStart(0, x);

        }

        // Hack to insert space after "if (cond)", etc. but not
        // at beginning of diamond.
        if (column != 0) {
            write(" ");
        }
        write("{");
        if (x.getBody() != null && x.getBody().size() > 0) {
            writeLineList(1, +1, 0, x.getBody());
            writeSymbol(1, -1, "}");
        } else {
            write("}");

            // Mark statement end ...
            markEnd(0, x);

        }
        printFooter(x);
    }

    public void printBreak(Break x) {
        printHeader(x);
        writeInternalIndentation(x);

        // Mark statement start ...
        markStart(0, x);
        markKeywordStart();
        write("break");
        markKeywordEnd();
        write(" ");
        noLinefeed = true;
        if (x.getProgramElementName() != null) {
            writeElement(1, x.getProgramElementName());
        }
        write(";");
        noLinefeed = false;

        // Mark statement end ...
        markEnd(0, x);

        printFooter(x);
    }

    public void printContinue(Continue x) {
        printHeader(x);
        writeInternalIndentation(x);

        // Mark statement start ...
        markStart(0, x);
        markKeywordStart();
        write("continue");
        markKeywordEnd();
        write(" ");
        noLinefeed = true;
        if (x.getProgramElementName() != null) {
            writeElement(1, x.getProgramElementName());
        }
        write(";");
        noLinefeed = false;

        // Mark statement end ...
        markEnd(0, x);

        printFooter(x);
    }

    public void printReturn(Return x) {
        printHeader(x);
        writeInternalIndentation(x);

        // Mark statement start ...
        markStart(0, x);
        markKeywordStart();
        write("return");
        markKeywordEnd();
        write(" ");
        if (x.getExpression() != null) {
            noSemicolons = true;
            writeElement(1, x.getExpression());
            noSemicolons = false;
        }
        write(";");

        // Mark statement end ...
        markEnd(0, x);

        printFooter(x);
    }

    public void printThrow(Throw x) {
        printHeader(x);
        writeInternalIndentation(x);

        // Mark statement start ...
        markStart(0, x);

        write("throw ");
        if (x.getExpression() != null) {
            noSemicolons = true;
            writeElement(1, x.getExpression());
            noSemicolons = false;
        }
        write(";");

        // Mark statement end ...
        markEnd(0, x);

        printFooter(x);
    }

    public void printDo(Do x) {
        printDo(x, true);
    }

    public void printDo(Do x, boolean includeBody) {
        printHeader(x);
        writeInternalIndentation(x);

        // Mark statement start ...
        markStart(0, x);
        markKeywordStart();
        write("do");
        markKeywordEnd();
        if (includeBody) {
            if (x.getBody() == null || x.getBody() instanceof EmptyStatement) {
                write(";");
                // w.writeElement(1, body);
            } else {
                if (x.getBody() instanceof StatementBlock) {
                    writeElement(1, 0, x.getBody());
                } else {
                    writeElement(1, +1, 0, x.getBody());
                    changeLevel(-1);
                }
            }
        } else {
            write(" ... ");
        }
        writeSymbol(1, 0, "while");
        noLinefeed = true;
        noSemicolons = true;
        write(" (");
        if (x.getGuardExpression() != null) {
            write(" ");
            writeElement(x.getGuardExpression());
            write(" ");
        }
        noLinefeed = false;
        noSemicolons = false;
        write(");");

        // Mark statement end ...
        markEnd(0, x);

        printFooter(x);
    }

    private static void removeChar(StringBuffer sb, char c) {
        for (int i = 0; i < sb.length(); i++) {
            if (sb.charAt(i) == c) {
                sb.deleteCharAt(i);
            }
        }
    }

    public void printEnhancedFor(EnhancedFor x) {
        printEnhancedFor(x, true);
    }

    public void printEnhancedFor(EnhancedFor x, boolean includeBody) {
        printHeader(x);
        writeInternalIndentation(x);
        output();

        // Mark statement start ...
        markStart(0, x);

        write("for (");
        noLinefeed = true;
        noSemicolons = true;

        ImmutableArray<LoopInitializer> initializers = x.getInitializers();
        if (initializers != null) {
            LoopInitializer loopInit = initializers.get(0);
            writeElement(1, loopInit);
        }

        write(" : ");

        if (x.getGuard() != null)
            writeElement(1, x.getGuardExpression());

        write(")");
        output();
        noLinefeed = false;
        noSemicolons = false;

        if (includeBody) {
            if (x.getBody() == null || x.getBody() instanceof EmptyStatement) {
                write(";");
            } else {
                if (x.getBody() instanceof StatementBlock) {
                    writeElement(1, 0, x.getBody());
                } else {
                    writeElement(1, +1, 0, x.getBody());
                    changeLevel(-1);
                }
            }
        }

        // Mark statement end ...
        markEnd(0, x);

        printFooter(x);
    }

    public void printFor(For x) {
        printFor(x, true);
    }

    public void printFor(For x, boolean includeBody) {
        printHeader(x);
        writeInternalIndentation(x);
        output();

        // Mark statement start ...
        markStart(0, x);
        markKeywordStart();
        write("for");
        markKeywordEnd();
        write(" (");
        noLinefeed = true;
        noSemicolons = true;
        write(" ");

        // there is no "getLoopInit" method
        // so get the first child of the for loop
        ILoopInit init = x.getILoopInit();
        if (init != null) {
            if (init instanceof ProgramSV)
                writeElement(init);
            else
                writeCommaList(x.getInitializers());
        }
        noSemicolons = false;
        write("; ");
        output();
        noSemicolons = true;
        if (x.getGuardExpression() != null) {
            writeElement(1, x.getGuardExpression());
        }
        noSemicolons = false;
        write("; ");
        output();
        noSemicolons = true;

        IForUpdates upd = x.getIForUpdates();
        if (upd != null) {
            if (upd instanceof ProgramSV)
                writeElement(1, upd);
            else
                writeCommaList(0, 0, 1, x.getUpdates());
        }
        write(" ");
        write(")");
        output();
        noLinefeed = false;
        noSemicolons = false;

        if (includeBody) {
            if (x.getBody() == null || x.getBody() instanceof EmptyStatement) {
                write(";");
            } else {
                if (x.getBody() instanceof StatementBlock) {
                    writeElement(1, 0, x.getBody());
                } else {
                    writeElement(1, +1, 0, x.getBody());
                    changeLevel(-1);
                }
            }
        }

        // Mark statement end ...
        markEnd(0, x);

        printFooter(x);
    }

    public void printWhile(While x) {
        printWhile(x, true);
    }

    public void printWhile(While x, boolean includeBody) {
        printHeader(x);
        writeInternalIndentation(x);
        output();
        noLinefeed = true;
        noSemicolons = true;

        // Mark statement start ...
        markStart(0, x);
        markKeywordStart();
        write("while");
        markKeywordEnd();
        write(" (");
        write(" ");
        if (x.getGuardExpression() != null) {
            writeElement(x.getGuardExpression());
        }
        write(" )");
        output();
        noLinefeed = false;
        noSemicolons = false;

        if (includeBody) {
            if (x.getBody() == null || x.getBody() instanceof EmptyStatement) {
                write(";");
            } else {
                if (x.getBody() instanceof StatementBlock) {
                    writeElement(0, 0, x.getBody());
                } else {
                    writeElement(1, +1, 0, x.getBody());
                    changeLevel(-1);
                }
            }
        }

        // Mark statement end ...
        markEnd(0, x);

        printFooter(x);
    }

    public void printIf(If x) {
        printIf(x, true);
    }

    public void printIf(If x, boolean includeBranches) {
        printHeader(x);
        writeInternalIndentation(x);
        output();

        noLinefeed = true;
        noSemicolons = true;

        // Mark statement start ...
        markStart(0, x);
        markKeywordStart();
        write("if");
        markKeywordEnd();
        write(" (");
        if (x.getExpression() != null) {
            writeElement(1, x.getExpression());
        }
        write(")");

        noLinefeed = false;
        noSemicolons = false;

        if (includeBranches) {
            if (x.getThen() != null) {
                if (x.getThen().getBody() instanceof StatementBlock) {
                    writeElement(1, 0, x.getThen());
                } else {
                    writeElement(1, +1, 0, x.getThen());
                    changeLevel(-1);
                }
            }
            if (x.getElse() != null) {
                writeElement(1, 0, x.getElse());
            }
        }

        // Mark statement end ...
        markEnd(0, x);

        printFooter(x);
    }

    public void printSwitch(Switch x) {
        printSwitch(x, true);
    }

    public void printSwitch(Switch x, boolean includeBranches) {
        printHeader(x);
        writeInternalIndentation(x);

        // Mark statement start ...
        markStart(0, x);
        markKeywordStart();
        write("switch");
        markKeywordEnd();
        write(" (");
        if (x.getExpression() != null) {
            noSemicolons = true;
            writeElement(x.getExpression());
            noSemicolons = false;
        }
        write(")");
        if (includeBranches) {
            write(" {");
            if (x.getBranchList() != null) {
                writeLineList(1, 0, 0, x.getBranchList());
            }
            writeSymbol(1, 0, "}");
        }

        // Mark statement end ...
        markEnd(0, x);

        printFooter(x);
    }

    public void printTry(Try x) {
        printHeader(x);
        writeInternalIndentation(x);

        // // Mark statement start ...
        // markStart(0,x);
        markKeywordStart();
        write("try");
        markKeywordEnd();
        if (x.getBody() != null) {
            writeElement(0, 0, x.getBody());
        }
        if (x.getBranchList() != null) {
            writeLineList(1, 0, 0, x.getBranchList());
        }

        // // Mark statement end ...
        // markEnd(0,x);

        printFooter(x);
    }

    public void printLabeledStatement(LabeledStatement x) {

        printHeader(x);


        if (x.getLabel() != null) {
            writeElement(x.getLabel());
            writeToken(":", x);
        }

        if (x.getBody() != null) {
            writeElement(1, 0, x.getBody());
        }

        printFooter(x);
    }

    public void printMethodFrame(MethodFrame x) {

        printHeader(x);

        noLinefeed = false;
        markKeywordStart();
        write("method-frame");
        markKeywordEnd();
        write("(");
        IProgramVariable pvar = x.getProgramVariable();
        if (pvar != null) {
            write("result->");
            writeElement(pvar);
            write(", ");
        }

        if (x.getExecutionContext() instanceof ExecutionContext) {
            writeElement(x.getExecutionContext());
        } else {
            printSchemaVariable((SchemaVariable) x.getExecutionContext());
        }

        write(")");
        writeToken(":", x);

        noLinefeed = false;
        noSemicolons = false;

        if (x.getBody() != null) {
            writeElement(0, 0, x.getBody());
        }

        printFooter(x);
    }

    public void printCatchAllStatement(CatchAllStatement x) {
        printHeader(x);
        markStart(0, x);
        write("#catchAll");
        write("(");
        writeElement(x.getParam());
        write(")");
        writeElement(1, x.getBody());
        markEnd(0, x);
        printFooter(x);
    }

    public void printMethodBodyStatement(MethodBodyStatement x) {

        boolean wasNoLinefeed = noLinefeed;
        noLinefeed = false;

        printHeader(x);
        writeInternalIndentation(x);
        markStart(0, x);

        IProgramVariable pvar = x.getResultVariable();
        if (pvar != null) {
            writeElement(pvar);
            write("=");
        }

        printMethodReference(x.getMethodReference(), false);
        // CHG:
        write("@");
        final TypeReference tr = x.getBodySourceAsTypeReference();
        if (tr instanceof SchemaTypeReference) {
            printSchemaTypeReference((SchemaTypeReference) tr);
        } else if (tr instanceof SchemaVariable) {
            printSchemaVariable((SchemaVariable) tr);
        } else {
            printTypeReference(tr);
        }
        write(";");
        markEnd(0, x);
        printFooter(x);

        noLinefeed = wasNoLinefeed;
    }


    public void printSynchronizedBlock(SynchronizedBlock x) {

        printHeader(x);
        writeInternalIndentation(x);
        write("synchronized");
        if (x.getExpression() != null) {
            write("(");
            writeElement(x.getExpression());
            write(")");
        }
        if (x.getBody() != null) {
            writeElement(1, x.getBody());
        }
        printFooter(x);
    }


    public void printLoopScopeBlock(LoopScopeBlock x) {
        printHeader(x);
        writeInternalIndentation(x);
        // write("\u21BB"); // UTF-8 loop scope sign
        write("loop-scope(");
        if (x.getIndexPV() != null) {
            writeElement(x.getIndexPV());
        }
        write(")");
        if (x.getBody() != null) {
            writeElement(1, x.getBody());
        }
        // write("\u21BA"); // UTF-8 loop scope end sign
        printFooter(x);
    }

    public void printImport(Import x) {
        printHeader(x);
        writeInternalIndentation(x);
        write("import");
        writeElement(1, x.getReference());
        if (x.isMultiImport()) {
            write(".*;");
        } else {
            write(";");
        }
        printFooter(x);
    }


    public void printExtends(Extends x) {
        printHeader(x);
        if (x.getSupertypes() != null) {
            writeInternalIndentation(x);
            write("extends");
            writeCommaList(0, 0, 1, x.getSupertypes());
        }
        printFooter(x);
    }

    public void printImplements(Implements x) {
        printHeader(x);
        if (x.getSupertypes() != null) {
            writeInternalIndentation(x);
            write("implements");
            writeCommaList(0, 0, 1, x.getSupertypes());
        }
        printFooter(x);
    }

    public void printVariableSpecification(VariableSpecification x) {

        printHeader(x);

        // Mark statement start ...
        markStart(0, x);

        x.getProgramVariable().prettyPrint(this);
        // writeElement(x.getProgramElementName());
        for (int i = 0; i < x.getDimensions(); i += 1) {
            write("[]");
        }
        if (x.getInitializer() != null) {
            // w.writeIndentation(getInternalLinefeeds(),
            // getInternalIndentation());
            write(" = ");
            writeElement(0, 0, 1, x.getInitializer());
        }
        // Mark statement end ...
        markEnd(0, x);

        printFooter(x);

    }

    public void printBinaryAnd(BinaryAnd x) {
        printHeader(x);
        printOperator(x, "&");
        printFooter(x);
    }

    public void printBinaryAndAssignment(BinaryAndAssignment x) {

        printHeader(x);
        printOperator(x, "&=");
        printFooter(x);
    }

    public void printBinaryOrAssignment(BinaryOrAssignment x) {

        printHeader(x);
        printOperator(x, "|=");
        printFooter(x);
    }

    public void printBinaryXOrAssignment(BinaryXOrAssignment x) {

        printHeader(x);
        printOperator(x, "^=");
        printFooter(x);
    }

    public void printCopyAssignment(CopyAssignment x) {
        printHeader(x);
        // output();
        // noLinefeed=true;
        printOperator(x, "=");
        // noLinefeed=false;
        // write("\n");
        printFooter(x);
    }

    public void printDivideAssignment(DivideAssignment x) {
        printHeader(x);
        printOperator(x, "/=");
        printFooter(x);
    }

    public void printMinusAssignment(MinusAssignment x) {
        printHeader(x);
        printOperator(x, "-=");
        printFooter(x);
    }

    public void printModuloAssignment(ModuloAssignment x) {
        printHeader(x);
        printOperator(x, "%=");
        printFooter(x);
    }

    public void printPlusAssignment(PlusAssignment x) {
        printHeader(x);
        printOperator(x, "+=");
        printFooter(x);
    }

    public void printPostDecrement(PostDecrement x) {
        printHeader(x);
        printOperator(x, "--");
        printFooter(x);
    }

    public void printPostIncrement(PostIncrement x) {
        printHeader(x);
        printOperator(x, "++");
        printFooter(x);
    }

    public void printPreDecrement(PreDecrement x) {
        printHeader(x);
        printOperator(x, "--");
        printFooter(x);
    }

    public void printPreIncrement(PreIncrement x) {
        printHeader(x);
        printOperator(x, "++");
        printFooter(x);
    }

    public void printShiftLeftAssignment(ShiftLeftAssignment x) {

        printHeader(x);
        printOperator(x, "<<=");
        printFooter(x);
    }

    public void printShiftRightAssignment(ShiftRightAssignment x) {

        printHeader(x);
        printOperator(x, ">>=");
        printFooter(x);
    }

    public void printTimesAssignment(TimesAssignment x) {
        printHeader(x);
        printOperator(x, "*=");
        printFooter(x);
    }

    public void printUnsignedShiftRightAssignment(UnsignedShiftRightAssignment x) {

        printHeader(x);
        printOperator(x, ">>>=");
        printFooter(x);
    }

    public void printBinaryNot(BinaryNot x) {
        printHeader(x);
        printOperator(x, "~");
        printFooter(x);
    }

    public void printBinaryOr(BinaryOr x) {
        printHeader(x);
        printOperator(x, "|");
        printFooter(x);
    }

    public void printBinaryXOr(BinaryXOr x) {
        printHeader(x);
        printOperator(x, "^");
        printFooter(x);
    }

    public void printConditional(Conditional x) {
        printHeader(x);

        boolean addParentheses = x.isToBeParenthesized();
        if (x.getArguments() != null) {
            if (addParentheses) {
                write("(");
            }
            writeElement(0, x.getArguments().get(0));
            write(" ?");
            writeElement(1, x.getArguments().get(1));
            write(" :");
            writeElement(1, x.getArguments().get(2));
            if (addParentheses) {
                write(")");
            }
        }
        printFooter(x);
    }

    public void printDivide(Divide x) {
        printHeader(x);
        printOperator(x, "/");
        printFooter(x);
    }

    public void printEquals(Equals x) {
        printHeader(x);
        printOperator(x, "==");
        printFooter(x);
    }

    public void printGreaterOrEquals(GreaterOrEquals x) {
        printHeader(x);
        printOperator(x, ">=");
        printFooter(x);
    }

    public void printGreaterThan(GreaterThan x) {
        printHeader(x);
        printOperator(x, ">");
        printFooter(x);
    }

    public void printLessOrEquals(LessOrEquals x) {
        printHeader(x);
        printOperator(x, "<=");
        printFooter(x);
    }

    public void printLessThan(LessThan x) {
        printHeader(x);
        printOperator(x, "<");
        printFooter(x);
    }

    public void printNotEquals(NotEquals x) {
        printHeader(x);
        printOperator(x, "!=");
        printFooter(x);
    }

    public void printNewArray(NewArray x) {
        printHeader(x);
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses) {
            write("(");
        }
        writeInternalIndentation(x);
        write("new ");

        writeElement(1, x.getTypeReference());
        int i = 0;
        if (x.getArguments() != null) {
            for (; i < x.getArguments().size(); i += 1) {
                write("[");
                writeElement(x.getArguments().get(i));
                write("]");
            }
        }
        for (; i < x.getDimensions(); i += 1) {
            write("[]");
        }
        if (x.getArrayInitializer() != null) {
            writeElement(1, x.getArrayInitializer());
        }
        if (addParentheses) {
            write(")");
        }
        printFooter(x);
    }

    public void printInstanceof(Instanceof x) {
        printHeader(x);
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses) {
            write("(");
        }
        if (x.getArguments() != null) {
            writeElement(0, x.getExpressionAt(0));
        }
        writeInternalIndentation(x);
        write(" instanceof ");
        if (x.getTypeReference() != null) {
            writeElement(1, x.getTypeReference());
        }
        if (addParentheses) {
            write(")");
        }
        printFooter(x);
    }


    public void printExactInstanceof(ExactInstanceof x) {
        printHeader(x);
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses) {
            write("(");
        }
        if (x.getArguments() != null) {
            writeElement(0, x.getExpressionAt(0));
        }
        writeInternalIndentation(x);
        write(" exactInstanceof ");
        if (x.getTypeReference() != null) {
            writeElement(1, x.getTypeReference());
        }
        if (addParentheses) {
            write(")");
        }
        printFooter(x);
    }



    public void printNew(New x) {
        printHeader(x);

        // Mark statement start ...
        markStart(0, x);

        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses) {
            write("(");
        }
        if (x.getReferencePrefix() != null) {
            writeElement(0, x.getReferencePrefix());
            write(".");
        }
        writeInternalIndentation(x);
        write("new ");

        writeElement(1, x.getTypeReference());
        write(" (");
        if (x.getArguments() != null) {
            writeCommaList(x.getArguments());
        }
        write(")");
        if (x.getClassDeclaration() != null) {
            writeElement(1, x.getClassDeclaration());
        }
        if (addParentheses) {
            write(")");
        }
        // !!!!!!!!!! HAS TO BE CHANGED
        // if (x.getStatementContainer() != null && fileWriterMode) {
        // write(";");
        // }

        // Mark statement end ...
        markEnd(0, x);
        printFooter(x);
    }

    public void printTypeCast(TypeCast x) {
        printHeader(x);
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses) {
            write("(");
        }
        writeInternalIndentation(x);
        write("(");
        if (x.getTypeReference() != null) {
            writeElement(0, x.getTypeReference());
        }
        write(")");
        if (x.getArguments() != null) {
            writeElement(0, x.getArguments().get(0));
        }
        if (addParentheses) {
            write(")");
        }
        printFooter(x);
    }

    public void printLogicalAnd(LogicalAnd x) {
        printHeader(x);
        printOperator(x, "&&");
        printFooter(x);
    }

    public void printLogicalNot(LogicalNot x) {
        printHeader(x);
        printOperator(x, "!");
        printFooter(x);
    }

    public void printLogicalOr(LogicalOr x) {
        printHeader(x);
        printOperator(x, "||");
        printFooter(x);
    }

    public void printMinus(Minus x) {
        printHeader(x);
        printOperator(x, "-");
        printFooter(x);
    }

    public void printModulo(Modulo x) {
        printHeader(x);
        printOperator(x, "%");
        printFooter(x);
    }

    public void printNegative(Negative x) {
        printHeader(x);
        printOperator(x, "-");
        printFooter(x);
    }

    public void printPlus(Plus x) {
        printHeader(x);
        printOperator(x, "+");
        printFooter(x);
    }

    public void printPositive(Positive x) {
        printHeader(x);
        printOperator(x, "+");
        printFooter(x);
    }

    public void printShiftLeft(ShiftLeft x) {
        printHeader(x);
        printOperator(x, "<<");
        printFooter(x);
    }

    public void printShiftRight(ShiftRight x) {
        printHeader(x);
        printOperator(x, ">>");
        printFooter(x);
    }

    public void printTimes(Times x) {
        printHeader(x);
        printOperator(x, "*");
        printFooter(x);
    }

    public void printUnsignedShiftRight(UnsignedShiftRight x) {

        printHeader(x);
        printOperator(x, ">>>");
        printFooter(x);
    }

    public void printArrayReference(ArrayReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            writeElement(x.getReferencePrefix());
        }
        if (x.getDimensionExpressions() != null) {
            int s = x.getDimensionExpressions().size();
            for (int i = 0; i < s; i += 1) {
                write("[");
                writeElement(x.getDimensionExpressions().get(i));
                write("]");
            }
        }
        printFooter(x);
    }

    public void printMetaClassReference(MetaClassReference x) {

        printHeader(x);
        if (x.getTypeReference() != null) {
            writeElement(x.getTypeReference());
            writeToken(".", x);
        }
        write("class");
        printFooter(x);
    }

    public void printMethodReference(MethodReference x) {
        printMethodReference(x, !noSemicolons);
    }


    protected void printMethodReference(MethodReference x, boolean withSemicolon) {
        printHeader(x);
        // Mark statement start ...
        markStart(0, x);

        if (x.getReferencePrefix() != null) {
            writeElement(x.getReferencePrefix());
            write(".");
        }
        if (x.getProgramElementName() != null) {
            x.getMethodName().prettyPrint(this);
            // writeElement(x.getProgramElementName());
        }

        write("(");
        boolean wasNoSemicolons = noSemicolons;
        boolean wasNoLinefeed = noLinefeed;
        noLinefeed = true;
        noSemicolons = true;
        if (x.getArguments() != null) {
            writeCommaList(x.getArguments());
        }
        write(")");
        if (withSemicolon) {
            write(";");
        }
        noLinefeed = wasNoLinefeed;
        noSemicolons = wasNoSemicolons;
        output();

        // Mark statement end ...
        markEnd(0, x);

    }

    public void printMethod(IProgramMethod x) {
        // printHeader(x);
        write(x.name().toString());
        // printFooter(x);
    }

    public void printFullMethodSignature(IProgramMethod x) {
        printHeader(x);
        writeFullMethodSignature(x);
        printFooter(x);
    }

    protected void writeFullMethodSignature(IProgramMethod x) {
        write(x.getName());
        write("(");
        boolean afterFirst = false;
        for (ParameterDeclaration pd : x.getParameters()) {
            if (afterFirst) {
                write(", ");
            } else {
                afterFirst = true;
            }
            boolean originalNoLinefeed = noLinefeed;
            try {
                noLinefeed = true;
                printTypeReference(pd.getTypeReference(), true);
            } finally {
                noLinefeed = originalNoLinefeed;
            }
        }
        write(")");
    }

    public void printExecutionContext(ExecutionContext x) {
        write("source=");
        writeFullMethodSignature(x.getMethodContext());
        write("@");
        writeElement(x.getTypeReference());
        if (x.getRuntimeInstance() != null) {
            write(",this=");
            writeElement(x.getRuntimeInstance());
        }
    }

    public void printSuperConstructorReference(SuperConstructorReference x) {

        printHeader(x);
        markStart(0, x);

        if (x.getReferencePrefix() != null) {
            writeElement(x.getReferencePrefix());
            write(".");
        }
        writeToken("super (", x);
        if (x.getArguments() != null) {
            writeCommaList(0, 0, 0, x.getArguments());
        }
        write(");");
        markEnd(0, x);
        printFooter(x);
    }

    public void printThisConstructorReference(ThisConstructorReference x) {

        printHeader(x);
        markStart(0, x);
        writeInternalIndentation(x);
        markKeywordStart();
        write("this");
        markKeywordEnd();
        write(" (");
        if (x.getArguments() != null) {
            writeCommaList(x.getArguments());
        }
        write(");");
        markEnd(0, x);
        printFooter(x);
    }

    public void printSuperReference(SuperReference x) {
        printHeader(x);
        markStart(0, x);
        if (x.getReferencePrefix() != null) {
            writeElement(x.getReferencePrefix());
            writeToken(".super", x);
        } else {
            writeToken("super", x);
        }
        markEnd(0, x);
        printFooter(x);
    }

    public void printThisReference(ThisReference x) {
        printHeader(x);
        markStart(0, x);
        if (x.getReferencePrefix() != null) {
            writeElement(x.getReferencePrefix());
            writeToken(".this", x);
        } else {
            writeToken("this", x);
        }
        markEnd(0, x);
        printFooter(x);
    }

    public void printArrayLengthReference(ArrayLengthReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            writeElement(x.getReferencePrefix());
            write(".");
        }
        writeToken("length", x);
        printFooter(x);
    }

    public void printThen(Then x) {
        printHeader(x);
        if (x.getBody() != null) {
            writeElement(x.getBody());
        }
        printFooter(x);
    }

    public void printElse(Else x) {
        printHeader(x);
        writeInternalIndentation(x);
        markKeywordStart();
        write("else ");
        markKeywordEnd();
        if (x.getBody() != null) {
            if (x.getBody() instanceof StatementBlock) {
                writeElement(1, 0, x.getBody());
            } else {
                writeElement(1, +1, 0, x.getBody());
                changeLevel(-1);
            }
        }

        printFooter(x);
    }

    public void printCase(Case x) {
        printHeader(x);
        writeInternalIndentation(x);
        markKeywordStart();
        write("case");
        markKeywordEnd();
        write(" ");
        if (x.getExpression() != null) {
            boolean wasNoSemicolons = noSemicolons;
            noSemicolons = true;
            writeElement(1, x.getExpression());
            noSemicolons = wasNoSemicolons;
        }
        write(":");
        if (x.getBody() != null && x.getBody().size() > 0) {
            writeLineList(1, +1, 0, x.getBody());
            changeLevel(-1);
        }
        printFooter(x);
    }

    public void printCatch(Catch x) {
        printHeader(x);
        boolean oldLineFeed = noLinefeed;
        noLinefeed = true;
        writeToken("catch", x);
        noLinefeed = oldLineFeed;
        write(" (");
        if (x.getParameterDeclaration() != null) {
            noLinefeed = true;
            noSemicolons = true;
            writeElement(x.getParameterDeclaration());
        }
        write(")");
        noSemicolons = false;
        noLinefeed = false;
        if (x.getBody() != null) {
            writeElement(1, x.getBody());
        }
        printFooter(x);
    }

    public void printDefault(Default x) {
        printHeader(x);
        writeInternalIndentation(x);
        write("default:");
        if (x.getBody() != null && x.getBody().size() > 0) {
            writeLineList(1, +1, 0, x.getBody());
            changeLevel(-1);
        }
        printFooter(x);
    }

    public void printFinally(Finally x) {
        printHeader(x);
        writeInternalIndentation(x);
        noLinefeed = true;
        output();
        noLinefeed = false;
        markKeywordStart();
        write("finally");
        markKeywordEnd();
        if (x.getBody() != null) {
            writeElement(1, x.getBody());
        }
        printFooter(x);
    }

    public void printModifier(Modifier x) {
        printHeader(x);
        writeInternalIndentation(x);
        write(x.getText());
        printFooter(x);
    }

    @SuppressWarnings("unchecked")
    public void printSchemaVariable(SchemaVariable x) {
        if (x instanceof ProgramSV) {
            if (!noSemicolons) {
                markStart(0, x);
            }
            Object o = instantiations.getInstantiation(x);
            if (o == null) {
                printHeader((ProgramSV) x);
                writeInternalIndentation((ProgramSV) x);
                write(x.name().toString());
                printFooter((ProgramSV) x);
            } else {
                // logger.debug(o.toString() + " " + o.getClass().getName());
                // Debug.assertTrue(o instanceof ProgramElement);
                if (o instanceof ProgramElement) {
                    ((ProgramElement) o).prettyPrint(this);
                } else if (o instanceof ImmutableArray/* <ProgramElement> */) {
                    writeBlockList((ImmutableArray<ProgramElement>) o);
                } else {
                    LOGGER.warn("No PrettyPrinting available for {}", o.getClass().getName());
                }
            }
            if (!noSemicolons) {
                markEnd(0, x);
            }
        } else {
            Debug.fail(
                "That cannot happen! Don't know how to pretty print non program SV in programs.");
        }

    }


    public void printEmptyStatement(EmptyStatement x) {
        printHeader(x);
        writeInternalIndentation(x);

        // Mark statement start ...
        markStart(0, x);

        write(";");

        // Mark statement end ...
        markEnd(0, x);

        printFooter(x);
    }

    public void printComment(Comment x) {
        write("/*" + x.getText() + "*/");
    }

    public void printParenthesizedExpression(ParenthesizedExpression x) {

        writeToken("(", x);
        if (x.getArguments() != null) {
            writeElement(x.getArguments().get(0));
        }
        write(")");
        output();
    }



    public void printPassiveExpression(PassiveExpression x) {

        writeToken("@(", x);
        if (x.getArguments() != null) {
            writeElement(x.getArguments().get(0));
        }
        write(")");
        output();
    }

    public void printTransactionStatement(TransactionStatement x) {
        printHeader(x);
        writeInternalIndentation(x);

        // Mark statement start ...
        markStart(0, x);

        write(x.toString());
        write(";");

        // Mark statement end ...
        markEnd(0, x);

        printFooter(x);
    }

    public void printEmptyMapLiteral(EmptyMapLiteral x) {
        printHeader(x);
        writeInternalIndentation(x);
        write("\\map_empty");
        printFooter(x);
    }

    /**
     * Prints an exec statement. Initial code copied from {@link #printTry(Try)}.
     *
     * @param x
     */
    public void printExec(Exec x) {
        printHeader(x);
        writeInternalIndentation(x);

        // // Mark statement start ...
        // markStart(0,x);
        markKeywordStart();
        write("exec");
        markKeywordEnd();
        if (x.getBody() != null) {
            writeElement(0, 0, x.getBody());
        }
        if (x.getBranchList() != null) {
            writeLineList(1, 0, 0, x.getBranchList());
        }

        // // Mark statement end ...
        // markEnd(0,x);

        printFooter(x);
    }

    /**
     * Prints a ccatch statement. Initial code copied from {@link #printCatch(Catch)}.
     *
     * @param x
     */
    public void printCcatch(Ccatch x) {
        printHeader(x);
        write(" ");
        markKeywordStart();
        write("ccatch");
        markKeywordEnd();
        write(" ");

        write(" (");
        if (x.hasParameterDeclaration()) {
            noLinefeed = true;
            noSemicolons = true;
            writeElement(x.getParameterDeclaration());
        } else if (x.hasNonStdParameterDeclaration()) {
            noLinefeed = true;
            noSemicolons = true;
            writeElement(x.getNonStdParameterDeclaration());
        }
        write(")");
        noSemicolons = false;
        noLinefeed = false;
        if (x.getBody() != null) {
            writeElement(1, x.getBody());
        }
        printFooter(x);
    }

    public void printCcatchReturnParameterDeclaration(CcatchReturnParameterDeclaration x) {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\Return", x);
        printFooter(x);
    }

    public void printCcatchReturnValParameterDeclaration(CcatchReturnValParameterDeclaration x) {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\Return", x);
        write(" ");
        writeElement(x.getDelegate());
        printFooter(x);
    }

    public void printCcatchContinueParameterDeclaration(CcatchContinueParameterDeclaration x) {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\Continue", x);
        printFooter(x);
    }

    public void printCcatchBreakParameterDeclaration(CcatchBreakParameterDeclaration x) {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\Break", x);
        printFooter(x);
    }

    public void printCcatchBreakLabelParameterDeclaration(CcatchBreakLabelParameterDeclaration x) {
        printHeader(x);
        writeInternalIndentation(x);

        markStart(0, x);
        markKeywordStart();
        write("\\Break");
        markKeywordEnd();
        write(" ");
        noLinefeed = true;
        if (x.getLabel() != null) {
            writeElement(1, x.getLabel());
        }
        noLinefeed = false;

        markEnd(0, x);

        printFooter(x);
    }

    public void printCcatchContinueLabelParameterDeclaration(
            CcatchContinueLabelParameterDeclaration x) {
        printHeader(x);
        writeInternalIndentation(x);

        markStart(0, x);
        markKeywordStart();
        write("\\Continue");
        markKeywordEnd();
        write(" ");
        noLinefeed = true;
        if (x.getLabel() != null) {
            writeElement(1, x.getLabel());
        }
        noLinefeed = false;

        markEnd(0, x);

        printFooter(x);
    }

    public void printCcatchBreakWildcardParameterDeclaration(
            CcatchBreakWildcardParameterDeclaration x) {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\Break *", x);
        printFooter(x);
    }

    public void printCcatchContinueWildcardParameterDeclaration(
            CcatchContinueWildcardParameterDeclaration x) {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\Continue *", x);
        printFooter(x);
    }

    /**
     * Prints the JML assert statement.
     *
     * @param jmlAssert the statement to print
     */
    public void printJmlAssert(JmlAssert jmlAssert) {
        printHeader(jmlAssert);
        writeInternalIndentation(jmlAssert);

        final String kind = jmlAssert.getKind().name().toLowerCase();

        markStart(0, jmlAssert);

        markKeywordStart();
        write("@");
        write(kind);
        markKeywordEnd();
        write(" ");

        write(jmlAssert.getConditionText());

        write(";");

        output();
        markEnd(0, jmlAssert);

        printFooter(jmlAssert);
    }
}
