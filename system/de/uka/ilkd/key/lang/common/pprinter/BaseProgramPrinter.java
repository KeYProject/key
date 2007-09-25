package de.uka.ilkd.key.lang.common.pprinter;

import java.io.IOException;
import java.io.Writer;
import java.util.HashMap;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SingleLineComment;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.lang.common.program.ArrayOfIProgramElement;
import de.uka.ilkd.key.lang.common.program.INonTerminalProgramElement;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.pp.Range;

/**
 * A base implementation of program printer.
 * 
 * TODO: this implementation was ripped off from Java pretty printer
 * and needs more work including on correctness. 
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BaseProgramPrinter implements IProgramPrinter {

        public void init(Writer writer) {
                this.setWriter(writer);
                outBuf = new StringBuffer();
        }

        public abstract void print(IProgramElement x) throws IOException;

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

        protected Writer out;

        protected StringBuffer outBuf;

        protected boolean noLinefeed = false;

        protected boolean noSemicolons = false;

        protected boolean fileWriterMode = false; // enfoces the output of

        // real Java syntax that
        // can be compiled.

        protected Type classToPrint = null;

        protected int firstStatementStart = -1;

        protected int firstStatementEnd = -1;

        protected boolean startAlreadyMarked = false;

        protected boolean endAlreadyMarked = false;

        protected Object firstStatement = null;

        static Logger logger = Logger.getLogger(BaseProgramPrinter.class
                        .getName());

        public void setNoLineFeed(boolean noLineFeed) {
                this.noLinefeed = noLineFeed;
        }

        public void setFileWriterMode(boolean fileWriterMode) {
                this.fileWriterMode = fileWriterMode;
        }

        /** The number of charcters that have been send to the writer */
        protected int writtenCharacters = 0;

        protected void output() throws IOException {
                if (noSemicolons)
                        removeChar(outBuf, ';');
                if (noLinefeed)
                        removeChar(outBuf, '\n');
                String toWrite = outBuf.toString();
                writtenCharacters += toWrite.length();
                out.write(toWrite);
                outBuf = new StringBuffer();

        }

        /** Numbers of generated characters */
        protected int getCurrentPos() {
                return writtenCharacters + outBuf.length();
        }

        /**
         * Marks the start of the first executable statement ...
         * 
         * @param n
         *                offset from the current position
         * @param stmt
         *                current statement;
         */
        protected void markStart(int n, Object stmt) {
                if (!startAlreadyMarked) {

                        // System.err.println("Mark start ... called");

                        firstStatementStart = getCurrentPos() + n;
                        firstStatement = stmt;
                        startAlreadyMarked = true;
                }
        }

        /**
         * Marks the end of the first executable statement ...
         * 
         * @param n
         *                offset from the current position
         */
        protected void markEnd(int n, Object stmt) {
                if (!endAlreadyMarked && (firstStatement == stmt)) {

                        // System.err.println("Mark end ... called ");

                        firstStatementEnd = getCurrentPos() + n;
                        endAlreadyMarked = true;
                }
        }

        /**
         * @return the range of the first executable statement that means the
         *         corresponding start and end position in the string
         *         representation
         */
        public Range getFocusRange() {
                return new Range(firstStatementStart, firstStatementEnd);
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
        }

        /**
         * Flag to indicate if a single line comment is being put out. Needed to
         * disable the worklist meanwhile.
         */
        private boolean isPrintingSingleLineComments = false;

        private HashMap indentMap = new HashMap();

        /**
         * Set a new stream to write to. Useful to redirect the output while
         * retaining all other settings. Resets the current source positions and
         * comments.
         */
        public void setWriter(Writer out) {
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
         * Get indentation level.
         * 
         * @return the int value.
         */
        public int getIndentationLevel() {
                return level;
        }

        /**
         * Set indentation level.
         * 
         * @param level
         *                an int value.
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
                return indentation * level;
        }

        /**
         * Change level.
         * 
         * @param delta
         *                an int value.
         */
        public void changeLevel(int delta) {
                level += delta;
        }

        private static char[] BLANKS = new char[128];

        private static char[] FEEDS = new char[8];

        static {
                for (int i = 0; i < FEEDS.length; i++) {
                        FEEDS[i] = '\n';
                }
                for (int i = 0; i < BLANKS.length; i++) {
                        BLANKS[i] = ' ';
                }
        }

        /**
         * Convenience method to write indentation chars.
         */
        protected void writeIndentation(int lf, int blanks) throws IOException {
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
        protected void writeIndentation(Position relative) throws IOException {
                writeIndentation(relative.getLine(), relative.getColumn());
        }

        /**
         * Write indentation.
         * 
         * @param elem
         *                a source element.
         * @exception IOException
         *                    occasionally thrown.
         */
        protected void writeIndentation(SourceElement elem) throws IOException {
                writeIndentation(getRelativePosition(elem.getFirstElement()));
        }

        /**
         * Write internal indentation.
         * 
         * @param elem
         *                a source element.
         * @exception IOException
         *                    occasionally thrown.
         */
        protected void writeInternalIndentation(SourceElement elem)
                        throws IOException {
                writeIndentation(getRelativePosition(elem));
        }

        /**
         * Write symbol.
         * 
         * @param lf
         *                an int value.
         * @param levelChange
         *                an int value.
         * @param symbol
         *                a string.
         * @exception IOException
         *                    occasionally thrown.
         */
        protected void writeSymbol(int lf, int levelChange, String symbol)
                        throws IOException {
                level += levelChange;
                writeIndentation(lf, getTotalIndentation());
                write(symbol);
        }

        /**
         * Replace all unicode characters above ? by their explicite
         * representation.
         * 
         * @param str
         *                the input string.
         * @return the encoded string.
         */
        protected static String encodeUnicodeChars(String str) {
                int len = str.length();
                StringBuffer buf = new StringBuffer(len + 4);
                for (int i = 0; i < len; i += 1) {
                        char c = str.charAt(i);
                        if (c >= 0x0100) {
                                if (c < 0x1000) {
                                        buf.append("\\u0"
                                                        + Integer.toString(c,
                                                                        16));
                                } else {
                                        buf.append("\\u"
                                                        + Integer.toString(c,
                                                                        16));
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
         * @param slc
         *                the comment to delay.
         */
        protected void scheduleComment(SingleLineComment slc) {
        }

        /**
         * Adds indentation for a program element if necessary and if required,
         * but does not print the indentation itself.
         */
        protected void writeElement(int lf, int levelChange, int blanks,
                        IProgramElement elem) throws IOException {
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
                print(elem);
        }

        private Position getRelativePosition(SourceElement first) {
                // System.out.println(indentMap);
                if (indentMap.containsKey(first)) {
                        return (Position) indentMap.get(first);
                } else {
                        if (first != null)
                                return first.getRelativePosition();
                        else
                                return Position.UNDEFINED;
                }
        }

        /**
         * Writes an implicit terminal token of a NonTerminal, including its
         * indentation. Sets the indentation if it is necessary or required.
         * 
         * @see SourceElement#prettyPrint
         */
        protected void writeToken(int lf, int blanks, String image,
                        INonTerminalProgramElement parent) throws IOException {
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
                indentMap.put(parent.getFirstElement(), indent); // needed
                // ?????
                writeIndentation(indent);
                // if (overwriteParsePositions) {
                // parent.setInternalParsedLine(line);
                // parent.setInternalParsedColumn(column);
                // }
                write(image);
        }

        protected final void writeToken(int blanks, String image,
                        INonTerminalProgramElement parent) throws IOException {
                writeToken(0, blanks, image, parent);
        }

        protected final void writeToken(String image,
                        INonTerminalProgramElement parent) throws IOException {
                writeToken(0, 0, image, parent);
        }

        /**
         * Write a source element.
         * 
         * @param lf
         *                an int value.
         * @param blanks
         *                an int value.
         * @param elem
         *                a source element.
         * @exception IOException
         *                    occasionally thrown.
         */
        protected void writeElement(int lf, int blanks, IProgramElement elem)
                        throws IOException {
                writeElement(lf, 0, blanks, elem);
        }

        /**
         * Write source element.
         * 
         * @param blanks
         *                an int value.
         * @param elem
         *                a source element.
         * @exception IOException
         *                    occasionally thrown.
         */
        protected void writeElement(int blanks, IProgramElement elem)
                        throws IOException {
                writeElement(0, 0, blanks, elem);
        }

        /**
         * Write source element.
         * 
         * @param elem
         *                a source element.
         * @exception IOException
         *                    occasionally thrown.
         */
        protected void writeElement(IProgramElement elem) throws IOException {
                writeElement(0, 0, 0, elem);
        }

        /**
         * Write a complete ArrayOfProgramElement.
         */
        protected void writeArrayOfProgramElement(int firstLF, int levelChange,
                        int firstBlanks, String separationSymbol,
                        int separationLF, int separationBlanks,
                        ArrayOfIProgramElement list) throws IOException {
                int s = list.size();
                if (s == 0) {
                        return;
                }
                writeElement(firstLF, levelChange, firstBlanks, list
                                .getIProgramElement(0));
                for (int i = 1; i < s; i += 1) {
                        write(separationSymbol);
                        writeElement(separationLF, separationBlanks, list
                                        .getIProgramElement(i));
                }
        }

        /**
         * Write a complete ArrayOfProgramElement using "Keyword" style.
         */
        protected void writeKeywordList(int firstLF, int levelChange,
                        int firstBlanks, ArrayOfIProgramElement list)
                        throws IOException {
                writeArrayOfProgramElement(firstLF, levelChange, firstBlanks,
                                "", 0, 1, list);
        }

        /**
         * Write keyword list.
         * 
         * @param list
         *                a program element list.
         * @exception IOException
         *                    occasionally thrown.
         */
        protected void writeKeywordList(ArrayOfIProgramElement list)
                        throws IOException {
                writeArrayOfProgramElement(0, 0, 0, "", 0, 1, list);
        }

        /**
         * Write a complete ArrayOfProgramElement using "Comma" style.
         */
        protected void writeCommaList(int firstLF, int levelChange,
                        int firstBlanks, ArrayOfIProgramElement list)
                        throws IOException {
                writeArrayOfProgramElement(firstLF, levelChange, firstBlanks,
                                ",", 0, 1, list);
        }

        /**
         * Write comma list.
         * 
         * @param list
         *                a program element list.
         * @exception IOException
         *                    occasionally thrown.
         */
        protected void writeCommaList(int separationBlanks,
                        ArrayOfIProgramElement list) throws IOException {
                writeArrayOfProgramElement(0, 0, 0, ",", 0, separationBlanks,
                                list);
        }

        /**
         * Write comma list.
         * 
         * @param list
         *                a program element list.
         * @exception IOException
         *                    occasionally thrown.
         */
        protected void writeCommaList(ArrayOfIProgramElement list)
                        throws IOException {
                writeArrayOfProgramElement(0, 0, 0, ",", 0, 1, list);
        }

        /**
         * Write a complete ArrayOfProgramElement using "Line" style.
         */
        protected void writeLineList(int firstLF, int levelChange,
                        int firstBlanks, ArrayOfIProgramElement list)
                        throws IOException {
                writeArrayOfProgramElement(firstLF, levelChange, firstBlanks,
                                "", 1, 0, list);
        }

        /**
         * Write line list.
         * 
         * @param list
         *                a program element list.
         * @exception IOException
         *                    occasionally thrown.
         */
        protected void writeLineList(ArrayOfIProgramElement list)
                        throws IOException {
                writeArrayOfProgramElement(0, 0, 0, "", 1, 0, list);
        }

        /**
         * Write a complete ArrayOfProgramElement using "Block" style.
         */
        protected void writeBlockList(int firstLF, int levelChange,
                        int firstBlanks, ArrayOfIProgramElement list)
                        throws IOException {
                writeArrayOfProgramElement(firstLF, levelChange, firstBlanks,
                                "", 2, 0, list);
        }

        /**
         * Write block list.
         * 
         * @param list
         *                a program element list.
         * @exception IOException
         *                    occasionally thrown.
         */
        protected void writeBlockList(ArrayOfIProgramElement list)
                        throws IOException {
                writeArrayOfProgramElement(0, 0, 0, "", 2, 0, list);
        }

        private void dumpComments() throws IOException {
        }

        /**
         * Write.
         * 
         * @param c
         *                an int value.
         * @exception IOException
         *                    occasionally thrown.
         */
        public void write(int c) throws IOException {
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
         * @param cbuf
         *                a char value.
         * @exception IOException
         *                    occasionally thrown.
         */
        public void write(char[] cbuf) throws IOException {
                write(cbuf, 0, cbuf.length);
        }

        /**
         * Write.
         * 
         * @param cbuf
         *                an array of char.
         * @param off
         *                an int value.
         * @param len
         *                an int value.
         * @exception IOException
         *                    occasionally thrown.
         */
        public void write(char[] cbuf, int off, int len) throws IOException {
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
                         * int i; for (i = off + len - 1; (i >= off && cbuf[i] !=
                         * '\n'); i -= 1) ; column = (i >= off) ? (off + len - 1 -
                         * i) : (column + len);
                         */
                }
                outBuf.append(cbuf, off, len);
        }

        /**
         * Write.
         * 
         * @param str
         *                a string.
         * @exception IOException
         *                    occasionally thrown.
         */
        public void write(String str) throws IOException {
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
         * @param str
         *                a string.
         * @param off
         *                an int value.
         * @param len
         *                an int value.
         * @exception IOException
         *                    occasionally thrown.
         */
        public void write(String str, int off, int len) throws IOException {
                write(str.substring(off, off + len));
        }

        /**
         * Indentation (cached).
         */
        private int indentation = 2;

        /*
         * Wrap threshold (cached). private int wrap;
         */

        /**
         * Overwrite indentation flag (cached).
         */
        private boolean overwriteIndentation;

        /**
         * Overwrite parse positions flag (cached).
         */
        private boolean overwriteParsePositions;

        /**
         * Get indentation amount (blanks per level).
         * 
         * @return the value of getIntegerProperty("indentationAmount").
         */
        protected int getIndentation() {
                return indentation;
        }

        /**
         * Returns true if the pretty printer should also reformat existing
         * code.
         * 
         * @return the value of the overwriteIndentation property.
         */
        protected boolean isOverwritingIndentation() {
                return overwriteIndentation;
        }

        /**
         * Returns true if the pretty printer should reset the parse positions
         * accordingly.
         * 
         * @return the value of the overwriteParsePositions property.
         */
        protected boolean isOverwritingParsePositions() {
                return overwriteParsePositions;
        }

        /**
         * Print program element header.
         * 
         * @param lf
         *                an int value.
         * @param blanks
         *                an int value.
         * @param elem
         *                a program element.
         * @exception IOException
         *                    occasionally thrown.
         */
        protected void printHeader(int lf, int blanks, ProgramElement elem)
                        throws IOException {

                printHeader(lf, 0, blanks, elem);
        }

        /**
         * Print program element header.
         * 
         * @param blanks
         *                an int value.
         * @param elem
         *                a program element.
         * @exception IOException
         *                    occasionally thrown.
         */
        protected void printHeader(int blanks, ProgramElement elem)
                        throws IOException {
                printHeader(0, 0, blanks, elem);
        }

        /**
         * Print program element header.
         * 
         * @param elem
         *                a program element.
         * @exception IOException
         *                    occasionally thrown.
         */
        protected void printHeader(ProgramElement elem) throws IOException {
                printHeader(0, 0, 0, elem);
        }

        /**
         * Print program element header.
         * 
         * @param lf
         *                number of line feeds.
         * @param levelChange
         *                the level change.
         * @param blanks
         *                number of white spaces.
         * @param x
         *                the program element.
         * @exception IOException
         *                    occasionally thrown.
         */
        protected void printHeader(int lf, int levelChange, int blanks,
                        ProgramElement x) throws IOException {

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
         * @param x
         *                the program element.
         * @exception IOException
         *                    occasionally thrown.
         */
        protected void printFooter(ProgramElement x) throws IOException {
                output();
        }

        private static void removeChar(StringBuffer sb, char c) {
                for (int i = 0; i < sb.length(); i++) {
                        if (sb.charAt(i) == c) {
                                sb.deleteCharAt(i);
                        }
                }
        }

}
