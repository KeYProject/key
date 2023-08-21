/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java;

import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Properties;

import recoder.io.PropertyNames;
import recoder.java.SourceElement.Position;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.*;
import recoder.java.expression.*;
import recoder.java.expression.literal.*;
import recoder.java.expression.operator.*;
import recoder.java.reference.*;
import recoder.java.statement.*;
import recoder.util.StringUtils;

/**
 * A configurable pretty printer for Java source elements. The settings of the pretty printer is
 * given by the current project settings and cannot be changed. Instances of this class are
 * available from {@link recoder.ProgramFactory#getPrettyPrinter}. Remember to <CODE>close()
 * </CODE> the writer once finished.
 *
 * @author AL
 */
public class PrettyPrinter extends SourceVisitor implements PropertyNames {

    private static final char[] BLANKS = new char[128];
    private static final char[] FEEDS = new char[8];

    static {
        Arrays.fill(FEEDS, '\n');
        Arrays.fill(BLANKS, ' ');
    }

    /**
     * A snapshot of the system properties at creation time of this instance.
     */
    private final Properties properties;
    /**
     * Worklist of single line comments that must be delayed till the next linefeed.
     */
    private final List<SingleLineComment> singleLineCommentWorkList =
        new ArrayList<>();
    /**
     * Shared and reused position object.
     */
    private final Position overwritePosition = new Position(0, 0);
    /**
     * The destination writer stream.
     */
    private Writer out = null;
    /**
     * Line number.
     */
    private int line = 1;
    /**
     * Column number. Used to keep track of indentations.
     */
    private int column = 1;
    /**
     * Level.
     */
    private int level = 0;
    /**
     * Flag to indicate if a single line comment is being put out. Needed to disable the worklist
     * meanwhile.
     */
    private boolean isPrintingSingleLineComments = false;
    /**
     * Flag to indicate that a single line comment has just been printed. Needed if, for example,
     */
    private boolean hasJustPrintedComment = false;
    /**
     * Indentation (cached).
     */
    private int indentation;
    /**
     * Overwrite indentation flag (cached).
     */
    private boolean overwriteIndentation;
    /**
     * Overwrite parse positions flag (cached).
     */
    private boolean overwriteParsePositions;

    /**
     * Set up a pretty printer with given options. Note that it is not wise to change the options
     * during pretty printing - nothing dangerous will happen, but the results might look strange.
     * It can make sense to change options between source files, however.
     */
    protected PrettyPrinter(Writer out, Properties props) {
        setWriter(out);
        properties = props;
        cacheFrequentlyUsed();
    }

    /**
     * Replace all unicode characters above ? by their explicite representation.
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
                    buf.append("\\u0" + Integer.toString(c, 16));
                } else {
                    buf.append("\\u" + Integer.toString(c, 16));
                }
            } else {
                buf.append(c);
            }
        }
        return buf.toString();
    }

    /**
     * Gets the currently used writer. Be careful when using.
     *
     * @return the currently used writer.
     */
    public Writer getWriter() {
        return out;
    }

    /**
     * Set a new stream to write to. Useful to redirect the output while retaining all other
     * settings. Resets the current source positions and comments.
     */
    public void setWriter(Writer out) {
        if (out == null) {
            throw new IllegalArgumentException("Impossible to write to null");
        }
        this.out = out;
        column = 1;
        line = 1;
        singleLineCommentWorkList.clear();
        isPrintingSingleLineComments = false;
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
        return indentation * level;
    }

    /**
     * Change level.
     *
     * @param delta an int value.
     */
    public void changeLevel(int delta) {
        level += delta;
    }

    /**
     * Convenience method to write indentation chars.
     */
    protected void printIndentation(int lf, int blanks) {
        if (lf > 0) {
            do {
                int n = Math.min(lf, FEEDS.length);
                print(FEEDS, 0, n);
                lf -= n;
            } while (lf > 0);
        }
        while (blanks > 0) {
            int n = Math.min(blanks, BLANKS.length);
            print(BLANKS, 0, n);
            blanks -= n;
        }
    }

    /**
     * Sets the indentation of the specified element to at least the specified minimum.
     *
     * @return the final relative position of the element.
     */
    protected Position setElementIndentation(int minlf, int minblanks, SourceElement element) {
        Position indent = element.getRelativePosition();
        if (hasJustPrintedComment && element.getStartPosition() == SourceElement.Position.UNDEFINED
                && element.getEndPosition() == SourceElement.Position.UNDEFINED) {
            minlf = Math.max(1, minlf);
        }
        hasJustPrintedComment = false; // Not sure if necessary, but can't hurt
        if (indent == Position.UNDEFINED) {
            if (minlf > 0) {
                minblanks += getTotalIndentation();
            }
            indent = new Position(minlf, minblanks);
        } else if (overwriteIndentation) {
            if (minlf > 0) {
                minblanks += getTotalIndentation();
            }
            indent.setPosition(minlf, minblanks);
        } else {
            if (minlf > 0 && indent.getColumn() == 0 && indent.getLine() == 0) {
                indent.setLine(1);
            }
            if (indent.getLine() > 0 && !(element instanceof Comment)) {
                // do not change comment indentation!
                minblanks += getTotalIndentation();
            }
            if (minblanks > indent.getColumn()) {
                indent.setColumn(minblanks);
            }
        }
        element.setRelativePosition(indent);
        return indent;
    }

    /**
     * Sets the indentation of the specified element to at least the specified minimum and writes
     * it.
     */
    protected void printElementIndentation(int minlf, int minblanks, SourceElement element) {
        Position indent = setElementIndentation(minlf, minblanks, element);
        printIndentation(indent.getLine(), indent.getColumn());
        if (overwriteParsePositions) {
            indent.setPosition(line, column);
            element.setStartPosition(indent);
        }
    }

    protected void printElementIndentation(int minblanks, SourceElement element) {
        printElementIndentation(0, minblanks, element);
    }

    protected void printElementIndentation(SourceElement element) {
        printElementIndentation(0, 0, element);
    }

    /**
     * Adds indentation for a program element if necessary and if required, but does not print the
     * indentation itself.
     */
    protected void printElement(int lf, int levelChange, int blanks, SourceElement elem) {
        level += levelChange;
        setElementIndentation(lf, blanks, findFirstElementInclComment(elem));
        elem.accept(this);
    }

    /**
     * Write a source element.
     *
     * @param lf an int value.
     * @param blanks an int value.
     * @param elem a source element.
     */
    protected void printElement(int lf, int blanks, SourceElement elem) {
        setElementIndentation(lf, blanks, findFirstElementInclComment(elem));
        elem.accept(this);
    }

    /**
     * Write source element.
     *
     * @param blanks an int value.
     * @param elem a source element.
     */
    protected void printElement(int blanks, SourceElement elem) {
        setElementIndentation(0, blanks, findFirstElementInclComment(elem));
        elem.accept(this);
    }

    /**
     * Write source element.
     *
     * @param elem a source element.
     */
    protected void printElement(SourceElement elem) {
        setElementIndentation(0, 0, findFirstElementInclComment(elem));
        elem.accept(this);
    }

    /**
     * Write a complete ProgramElementList.
     */
    protected void printProgramElementList(int firstLF, int levelChange, int firstBlanks,
            String separationSymbol, int separationLF, int separationBlanks,
            List<? extends ProgramElement> list) {
        int s = list.size();
        if (s == 0) {
            return;
        }
        printElement(firstLF, levelChange, firstBlanks, list.get(0));
        for (int i = 1; i < s; i += 1) {
            print(separationSymbol);
            printElement(separationLF, separationBlanks, list.get(i));
        }
    }

    /**
     * Write a complete ProgramElementList using "Keyword" style.
     *
     * @param list a program element list.
     */
    protected void printKeywordList(List<? extends ProgramElement> list) {
        printProgramElementList(0, 0, 0, "", 0, 1, list);
    }

    protected void printCommaList(int firstLF, int levelChange, int firstBlanks,
            List<? extends ProgramElement> list) {
        printProgramElementList(firstLF, levelChange, firstBlanks, ",", 0, 1, list);
    }

    /**
     * Write comma list.
     *
     * @param list a program element list.
     */
    protected void printCommaList(int separationBlanks, List<? extends ProgramElement> list) {
        printProgramElementList(0, 0, 0, ",", 0, separationBlanks, list);
    }

    /**
     * Write comma list.
     *
     * @param list a program element list.
     */
    protected void printCommaList(List<? extends ProgramElement> list) {
        printProgramElementList(0, 0, 0, ",", 0, 1, list);
    }

    /**
     * Write a complete ProgramElementList using "Line" style.
     */
    protected void printLineList(int firstLF, int levelChange,
            List<? extends ProgramElement> list) {
        printProgramElementList(firstLF, levelChange, 0, "", 1, 0, list);
    }

    /**
     * Write a complete ProgramElementList using "Block" style.
     */
    protected void printBlockList(int firstLF, int levelChange,
            List<? extends ProgramElement> list) {
        printProgramElementList(firstLF, levelChange, 0, "", 2, 0, list);
    }

    private void dumpComments() {
        int size = singleLineCommentWorkList.size();
        if (size > 0) {
            isPrintingSingleLineComments = true;
            for (SingleLineComment singleLineComment : singleLineCommentWorkList) {
                singleLineComment.accept(this);
            }
            singleLineCommentWorkList.clear();
            isPrintingSingleLineComments = false;
        }
    }

    /**
     * Write a single character.
     *
     * @param c an int value.
     * @throws PrettyPrintingException wrapping an IOException.
     */
    protected void print(int c) {
        if (c == '\n') {
            if (!isPrintingSingleLineComments) {
                dumpComments();
            }
            column = 1;
            line += 1;
        } else {
            column += 1;
        }
        try {
            out.write(c);
        } catch (IOException ioe) {
            throw new PrettyPrintingException(ioe);
        }
    }

    /*
     * Wrap threshold (cached). private int wrap;
     */

    /**
     * Write a sequence of characters.
     *
     * @param cbuf an array of char.
     * @param off an int value.
     * @param len an int value.
     */
    protected void print(char[] cbuf, int off, int len) {
        boolean col = false;

        for (int i = off + len - 1; i >= off; i -= 1) {
            if (cbuf[i] == '\n') {
                if (!isPrintingSingleLineComments) {
                    dumpComments();
                }
                line += 1;
                if (!col) {
                    column = (off + len - 1 - i) + 1;
                    col = true;
                }
            }
        }
        if (!col) {
            column += len;
            // int i;
            // for (i = off + len - 1; (i >= off && cbuf[i] != '\n'); i -= 1) ;
            // column = (i >= off) ? (off + len - 1 - i) : (column + len);
        }
        try {
            out.write(cbuf, off, len);
        } catch (IOException ioe) {
            throw new PrettyPrintingException(ioe);
        }
    }

    /**
     * Writes a string.
     *
     * @param str a string.
     * @throws PrettyPrintingException wrapping an IOException.
     */
    protected void print(String str) {
        int i = str.lastIndexOf('\n');
        if (i >= 0) {
            column = str.length() - i + 1 + 1;
            do {
                dumpComments();
                line += 1;
                i = str.lastIndexOf('\n', i - 1);
            } while (i >= 0);
        } else {
            column += str.length();
        }
        try {
            out.write(str);
        } catch (IOException ioe) {
            throw new PrettyPrintingException(ioe);
        }
    }

    public boolean getBooleanProperty(String key) {
        return StringUtils.parseBooleanProperty(properties.getProperty(key));
    }

    // parse and cache some important settings
    private void cacheFrequentlyUsed() {
        indentation = Integer.parseInt(properties.getProperty(INDENTATION_AMOUNT));
        if (indentation < 0) {
            throw new IllegalArgumentException("Negative indentation");
        }
        /*
         * wrap = Integer.parseInt(properties.getProperty("wrappingThreshold")); if (wrap < 40) {
         * throw new IllegalArgumentException("Wrapping threshold " + wrap + " is useless"); }
         */
        overwriteIndentation = getBooleanProperty(OVERWRITE_INDENTATION);
        overwriteParsePositions = getBooleanProperty(OVERWRITE_PARSE_POSITIONS);
    }

    /**
     * Get indentation amount (blanks per level).
     *
     * @return the value of getIntegerProperty("indentationAmount").
     */
    protected int getIndentation() {
        return indentation;
    }

    /**
     * Returns true if the pretty printer should also reformat existing code.
     *
     * @return the value of the overwriteIndentation property.
     */
    protected boolean isOverwritingIndentation() {
        return overwriteIndentation;
    }

    /**
     * Returns true if the pretty printer should reset the parse positions accordingly.
     *
     * @return the value of the overwriteParsePositions property.
     */
    protected boolean isOverwritingParsePositions() {
        return overwriteParsePositions;
    }

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

    private SourceElement findFirstElementInclComment(SourceElement x) {
        if (!(x instanceof ProgramElement)) {
            return x.getFirstElement();
        }
        List<Comment> cl = ((ProgramElement) x).getComments();
        int s = cl == null ? 0 : cl.size();
        for (int i = 0; i < s; i++) {
            Comment c = cl.get(i);
            if (c.isPrefixed()) {
                return c;
            }
        }
        return x.getFirstElement();
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
        SourceElement first = findFirstElementInclComment(x);

        setElementIndentation(lf, blanks, first);
        /*
         * Position indent = first.getRelativePosition(); if (indent == Position.UNDEFINED) { indent
         * = new Position(lf, blanks); } else if (overwriteIndentation) { indent.setPosition(lf,
         * blanks); } else { if (lf > indent.getLine()) { indent.setLine(lf); } if (blanks >
         * indent.getColumn()) { indent.setColumn(blanks); } } first.setRelativePosition(indent);
         */
        hasJustPrintedComment = false;
        int s = (x.getComments() != null) ? x.getComments().size() : 0;
        for (int i = 0; i < s; i += 1) {
            Comment c = x.getComments().get(i);
            if (c.isPrefixed()) {
                c.accept(this);
                hasJustPrintedComment = true;
            }
        }
    }

    /**
     * Sets end positions if required, and prints program element footer.
     *
     * @param x the program element.
     */
    protected void printFooter(ProgramElement x) {
        // also in visitComment!
        if (overwriteParsePositions) {
            overwritePosition.setPosition(line, column);
            x.setEndPosition(overwritePosition);
        }
        int s = (x.getComments() != null) ? x.getComments().size() : 0;
        for (int i = 0; i < s; i += 1) {
            Comment c = x.getComments().get(i);
            if (!c.isPrefixed() && !c.isContainerComment()) {
                if (c instanceof SingleLineComment) {
                    // Store until the next line feed is written.
                    singleLineCommentWorkList.add((SingleLineComment) c);
                } else {
                    c.accept(this);
                }
            }
        }
    }

    /**
     * @param x
     * @return true if any comment has been printed, false otherwise
     */
    protected boolean printContainerComments(ProgramElement x) {
        // TODO overwriteParsePositions???
        boolean commentPrinted = false;
        int s = (x.getComments() != null) ? x.getComments().size() : 0;
        for (int i = 0; i < s; i += 1) {
            Comment c = x.getComments().get(i);
            if (c.isContainerComment()) {
                c.accept(this);
                printIndentation(1, getIndentation());
                commentPrinted = true;
            }
        }
        return commentPrinted;
    }

    protected void printOperator(Operator x, String symbol) {
        List<Expression> children = x.getArguments();
        if (children != null) {
            boolean addParentheses = x.isToBeParenthesized();
            if (addParentheses) {
                print('(');
            }
            switch (x.getArity()) {
            case 2:
                printElement(0, children.get(0));
                if (getBooleanProperty(GLUE_INFIX_OPERATORS)) {
                    printElementIndentation(0, x);
                    print(symbol);
                    printElement(children.get(1));
                } else {
                    printElementIndentation(1, x);
                    print(symbol);
                    printElement(1, children.get(1));
                }
                break;
            case 1:
                switch (x.getNotation()) {
                case Operator.PREFIX:
                    printElementIndentation(x);
                    print(symbol);
                    if (getBooleanProperty(GLUE_UNARY_OPERATORS)) {
                        printElement(0, children.get(0));
                    } else {
                        printElement(1, children.get(0));
                    }
                    break;
                case Operator.POSTFIX:
                    printElement(0, children.get(0));
                    if (getBooleanProperty(GLUE_UNARY_OPERATORS)) {
                        printElementIndentation(x);
                        print(symbol);
                    } else {
                        printElementIndentation(1, x);
                        print(symbol);
                    }
                    break;
                default:
                    break;
                }
            }
            if (addParentheses) {
                print(')');
            }
            if (x instanceof Assignment) {
                if (((Assignment) x).getStatementContainer() != null) {
                    print(';');
                }
            }
        }
    }

    public void visitIdentifier(Identifier x) {
        printHeader(x);
        printElementIndentation(x);
        print(x.getText());
        printFooter(x);
    }

    public void visitIntLiteral(IntLiteral x) {
        printHeader(x);
        printElementIndentation(x);
        print(x.getValue());
        printFooter(x);
    }

    public void visitBooleanLiteral(BooleanLiteral x) {
        printHeader(x);
        printElementIndentation(x);
        print(x.getValue() ? "true" : "false");
        printFooter(x);
    }

    public void visitStringLiteral(StringLiteral x) {
        printHeader(x);
        printElementIndentation(x);
        print(encodeUnicodeChars(x.getValue()));
        printFooter(x);
    }

    public void visitNullLiteral(NullLiteral x) {
        printHeader(x);
        printElementIndentation(x);
        print("null");
        printFooter(x);
    }

    public void visitCharLiteral(CharLiteral x) {
        printHeader(x);
        printElementIndentation(x);
        print(encodeUnicodeChars(x.getValue()));
        printFooter(x);
    }

    public void visitDoubleLiteral(DoubleLiteral x) {
        printHeader(x);
        printElementIndentation(x);
        print(x.getValue());
        printFooter(x);
    }

    public void visitLongLiteral(LongLiteral x) {
        printHeader(x);
        printElementIndentation(x);
        print(x.getValue());
        printFooter(x);
    }

    public void visitFloatLiteral(FloatLiteral x) {
        printHeader(x);
        printElementIndentation(x);
        print(x.getValue());
        printFooter(x);
    }

    public void visitPackageSpecification(PackageSpecification x) {
        printHeader(x);
        int m = 0;
        if (x.getAnnotations() != null && x.getAnnotations().size() > 0) {
            m = x.getAnnotations().size();
            printKeywordList(x.getAnnotations());
            m = 1;
        }
        printElementIndentation(m, x);
        print("package");
        printElement(1, x.getPackageReference());
        print(';');
        printFooter(x);
    }

    public void visitTypeReference(TypeReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            printElement(x.getReferencePrefix());
            printElementIndentation(x);
            print('.');
        }
        if (x.getIdentifier() != null) {
            printElement(x.getIdentifier());
        }
        if (x.getTypeArguments() != null && x.getTypeArguments().size() > 0) {
            print('<');
            printCommaList(x.getTypeArguments());
            print('>');
        }
        for (int i = 0; i < x.getDimensions(); i += 1) {
            print("[]");
        }
        printFooter(x);
    }

    public void visitPackageReference(PackageReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            printElement(x.getReferencePrefix());
            printElementIndentation(x);
            print('.');
        }
        if (x.getIdentifier() != null) {
            printElement(x.getIdentifier());
        }
        printFooter(x);
    }

    public void visitThrows(Throws x) {
        printHeader(x);
        if (x.getExceptions() != null) {
            printElementIndentation(x);
            print("throws");
            printCommaList(0, 0, 1, x.getExceptions());
        }
        printFooter(x);
    }

    public void visitArrayInitializer(ArrayInitializer x) {
        printHeader(x);
        printElementIndentation(x);
        print('{');
        printContainerComments(x);

        if (x.getArguments() != null) {
            printCommaList(0, 0, 1, x.getArguments());
        }
        if (x.getArguments() != null && x.getArguments().size() > 0
                && x.getRelativePosition().getLine() > 0) {
            printIndentation(1, getTotalIndentation());
            print('}');
        } else {
            print(" }");
        }
        printFooter(x);
    }

    public void visitElementValueArrayInitializer(ElementValueArrayInitializer x) {
        printHeader(x);
        printElementIndentation(x);
        print('{');
        if (x.getElementValues() != null) {
            printCommaList(0, 0, 1, x.getElementValues());
        }
        if (x.getElementValues() != null && x.getElementValues().size() > 0
                && x.getRelativePosition().getLine() > 0) {
            printIndentation(1, getTotalIndentation());
            print('}');
        } else {
            print(" }");
        }
        printFooter(x);
    }

    public void visitCompilationUnit(CompilationUnit x) {
        line = column = 1;
        printHeader(x);
        setIndentationLevel(0);
        boolean hasPackageSpec = (x.getPackageSpecification() != null);
        if (hasPackageSpec) {
            printElement(x.getPackageSpecification());
        }
        boolean hasImports = (x.getImports() != null) && (x.getImports().size() > 0);
        if (hasImports) {
            printLineList((x.getPackageSpecification() != null) ? 2 : 1, 0, x.getImports());
        }
        if (x.getDeclarations() != null) {
            printBlockList((hasImports || hasPackageSpec) ? 2 : 0, 0, x.getDeclarations());
        }
        printFooter(x);
        // we do this linefeed here to allow flushing of the pretty printer
        // single line comment work list
        printIndentation(1, 0);
    }

    public void visitClassDeclaration(ClassDeclaration x) {
        printHeader(x);
        int m = 0;
        if (x.getDeclarationSpecifiers() != null) {
            m = x.getDeclarationSpecifiers().size();
        }
        if (m > 0) {
            printKeywordList(x.getDeclarationSpecifiers());
            m = 1;
        }
        if (x.getIdentifier() != null) {
            printElementIndentation(m, x);
            print("class");
            printElement(1, x.getIdentifier());
        }
        if (x.getTypeParameters() != null && x.getTypeParameters().size() > 0) {
            print("<");
            printCommaList(x.getTypeParameters());
            print("> ");
        }
        if (x.getExtendedTypes() != null) {
            printElement(1, x.getExtendedTypes());
        }
        if (x.getImplementedTypes() != null) {
            printElement(1, x.getImplementedTypes());
        }
        if (x.getIdentifier() != null) {
            print(' ');
        }
        print('{');
        printContainerComments(x);
        if (x.getMembers() != null && !x.getMembers().isEmpty()) {
            printBlockList(2, 1, x.getMembers());
            changeLevel(-1);
        }
        printIndentation(1, getTotalIndentation());
        print('}');
        printFooter(x);
    }

    public void visitInterfaceDeclaration(InterfaceDeclaration x) {
        visitInterfaceDeclaration(x, false);
    }

    private void visitInterfaceDeclaration(InterfaceDeclaration x, boolean annotation) {
        printHeader(x);
        int m = 0;
        if (x.getDeclarationSpecifiers() != null) {
            m = x.getDeclarationSpecifiers().size();
        }
        if (m > 0) {
            printKeywordList(x.getDeclarationSpecifiers());
            m = 1;
        }
        if (x.getIdentifier() != null) {
            printElementIndentation(m, x);
            if (annotation) {
                print("@");
            }
            print("interface");
            printElement(1, x.getIdentifier());
        }
        if (x.getTypeParameters() != null && x.getTypeParameters().size() > 0) {
            print("<");
            printCommaList(x.getTypeParameters());
            print("> ");
        }
        if (x.getExtendedTypes() != null) {
            printElement(1, x.getExtendedTypes());
        }
        print(" {");
        if (x.getMembers() != null && !x.getMembers().isEmpty()) {
            printBlockList(2, 1, x.getMembers());
            changeLevel(-1);
        }
        printIndentation(1, getTotalIndentation());
        print('}');
        printFooter(x);
    }

    public void visitAnnotationDeclaration(AnnotationDeclaration x) {
        visitInterfaceDeclaration(x, true);
    }

    public void visitFieldDeclaration(FieldDeclaration x) {
        printHeader(x);
        int m = 0;
        if (x.getDeclarationSpecifiers() != null) {
            m = x.getDeclarationSpecifiers().size();
            printKeywordList(x.getDeclarationSpecifiers());
        }
        printElement((m > 0) ? 1 : 0, x.getTypeReference());
        List<? extends VariableSpecification> varSpecs = x.getVariables();
        if (varSpecs != null) {
            printCommaList(0, 0, 1, varSpecs);
        }
        print(';');
        printFooter(x);
    }

    public void visitLocalVariableDeclaration(LocalVariableDeclaration x) {
        printHeader(x);
        int m = 0;
        if (x.getDeclarationSpecifiers() != null) {
            m = x.getDeclarationSpecifiers().size();
            printKeywordList(x.getDeclarationSpecifiers());
        }
        printElement((m > 0) ? 1 : 0, x.getTypeReference());
        List<? extends VariableSpecification> varSpecs = x.getVariables();
        if (varSpecs != null) {
            printCommaList(0, 0, 1, varSpecs);
        }
        if (!(x.getStatementContainer() instanceof LoopStatement)) {
            print(';');
        }
        printFooter(x);
    }

    protected void visitVariableDeclaration(VariableDeclaration x) {
        visitVariableDeclaration(x, false);
    }

    protected void visitVariableDeclaration(VariableDeclaration x, boolean spec) {
        printHeader(x);
        int m = 0;
        if (x.getDeclarationSpecifiers() != null) {
            m = x.getDeclarationSpecifiers().size();
            printKeywordList(x.getDeclarationSpecifiers());
        }
        printElement((m > 0) ? 1 : 0, x.getTypeReference());
        if (spec) {
            print(" ...");
            // printElement(spec);
        }
        List<? extends VariableSpecification> varSpecs = x.getVariables();
        if (varSpecs != null) {
            printCommaList(0, 0, 1, varSpecs);
        }
        printFooter(x);
    }

    public void visitMethodDeclaration(MethodDeclaration x) {
        printHeader(x);
        int m = 0;
        if (x.getDeclarationSpecifiers() != null) {
            m = x.getDeclarationSpecifiers().size();
            printKeywordList(x.getDeclarationSpecifiers());
        }
        if (x.getTypeParameters() != null && x.getTypeParameters().size() > 0) {
            if (m > 0) {
                print(' ');
            } else {
                printElementIndentation(x);
            }
            print('<');
            printCommaList(x.getTypeParameters());
            print('>');
            m = 1; // print another blank afterwards
        }
        if (x.getTypeReference() != null) {
            if (m > 0) {
                printElement(1, x.getTypeReference());
            } else {
                printElement(x.getTypeReference());
            }
            printElement(1, x.getIdentifier());
        } else {
            if (m > 0) {
                printElement(1, x.getIdentifier());
            } else {
                printElement(x.getIdentifier());
            }
        }
        if (getBooleanProperty(GLUE_PARAMETER_LISTS)) {
            print('(');
        } else {
            print(" (");
        }
        if (x.getParameters() != null) {
            List<? extends ParameterDeclaration> params = x.getParameters();
            printCommaList(getBooleanProperty(GLUE_PARAMETERS) ? 0 : 1, params);
        }
        print(')');
        if (x.getThrown() != null) {
            printElement(1, x.getThrown());
        }
        if (x instanceof AnnotationPropertyDeclaration) {
            AnnotationPropertyDeclaration apd = (AnnotationPropertyDeclaration) x;
            Expression e = apd.getDefaultValueExpression();
            if (e != null) {
                print(" default ");
                e.accept(this);
            }
        }
        if (x.getBody() != null) {
            printElement(1, x.getBody());
        } else {
            print(';');
        }
        printFooter(x);
    }

    public void visitClassInitializer(ClassInitializer x) {
        printHeader(x);
        int m = 0;
        if (x.getDeclarationSpecifiers() != null) {
            m = x.getDeclarationSpecifiers().size();
            printKeywordList(x.getDeclarationSpecifiers());
        }
        if (x.getBody() != null) {
            printElement(m > 0 ? 1 : 0, x.getBody());
        }
        printFooter(x);
    }

    public void visitStatementBlock(StatementBlock x) {
        printHeader(x);
        printElementIndentation(x);
        print('{');
        boolean doNotPossiblyPrintIndentation = printContainerComments(x);
        if (x.getBody() != null && x.getBody().size() > 0) {
            printLineList(1, +1, x.getBody());
            changeLevel(-1);
            Position firstStatementEndPosition = x.getBody().get(0).getEndPosition();
            Position blockEndPosition = x.getEndPosition();
            if (x.getBody().size() > 1 || firstStatementEndPosition.equals(Position.UNDEFINED)
                    || blockEndPosition.equals(Position.UNDEFINED)
                    || firstStatementEndPosition.getLine() < blockEndPosition.getLine()) {
                printIndentation(1, getTotalIndentation());
            } else {
                printIndentation(0,
                    blockEndPosition.getColumn() - firstStatementEndPosition.getColumn() - 1);
            }
        } else if (!doNotPossiblyPrintIndentation) {
            // keep old indentation
            int lf = x.getEndPosition().getLine() - x.getStartPosition().getLine();
            if (lf > 0) {
                printIndentation(lf, getIndentation());
            }
        }
        print('}');
        printFooter(x);
    }

    public void visitBreak(Break x) {
        printHeader(x);
        printElementIndentation(x);
        print("break");
        if (x.getIdentifier() != null) {
            printElement(1, x.getIdentifier());
        }
        print(';');
        printFooter(x);
    }

    public void visitContinue(Continue x) {
        printHeader(x);
        printElementIndentation(x);
        print("continue");
        if (x.getIdentifier() != null) {
            printElement(1, x.getIdentifier());
        }
        print(';');
        printFooter(x);
    }

    public void visitReturn(Return x) {
        printHeader(x);
        printElementIndentation(x);
        print("return");
        if (x.getExpression() != null) {
            printElement(1, x.getExpression());
        }
        print(';');
        printFooter(x);
    }

    public void visitThrow(Throw x) {
        printHeader(x);
        printElementIndentation(x);
        print("throw");
        if (x.getExpression() != null) {
            printElement(1, x.getExpression());
        }
        print(';');
        printFooter(x);
    }

    public void visitDo(Do x) {
        printHeader(x);
        printElementIndentation(x);
        print("do");
        if (x.getBody() == null || x.getBody() instanceof EmptyStatement) {
            print(';');
            // w.printElement(1, body);
        } else {
            if (getBooleanProperty(GLUE_STATEMENT_BLOCKS)) {
                printElement(1, x.getBody());
            } else {
                if (x.getBody() instanceof StatementBlock) {
                    printElement(1, 0, x.getBody());
                } else {
                    printElement(1, +1, 0, x.getBody());
                    changeLevel(-1);
                }
            }
        }
        if (getBooleanProperty(GLUE_STATEMENT_BLOCKS)) {
            print(" while");
        } else {
            printIndentation(1, getTotalIndentation());
            print("while");
        }
        if (getBooleanProperty(GLUE_PARAMETER_LISTS)) {
            print('(');
        } else {
            print(" (");
        }
        if (x.getGuard() != null) {
            boolean glueExprParentheses = getBooleanProperty(GLUE_EXPRESSION_PARENTHESES);
            if (!glueExprParentheses) {
                print(' ');
            }
            printElement(x.getGuard());
            if (!glueExprParentheses) {
                print(' ');
            }
        }
        print(");");
        printFooter(x);
    }

    public void visitFor(For x) {
        printHeader(x);
        printElementIndentation(x);
        print(getBooleanProperty(GLUE_CONTROL_EXPRESSIONS) ? "for(" : "for (");
        boolean glueExprParentheses = getBooleanProperty(GLUE_EXPRESSION_PARENTHESES);
        if (!glueExprParentheses) {
            print(' ');
        }
        if (x.getInitializers() != null) {
            printCommaList(x.getInitializers());
        }
        print(';');
        if (x.getGuard() != null) {
            printElement(1, x.getGuard());
        }
        print(';');
        if (x.getUpdates() != null) {
            printCommaList(0, 0, 1, x.getUpdates());
        }
        if (!glueExprParentheses) {
            print(' ');
        }
        print(')');
        if (x.getBody() == null || x.getBody() instanceof EmptyStatement) {
            print(';');
        } else {
            if (getBooleanProperty(GLUE_STATEMENT_BLOCKS)) {
                printElement(1, x.getBody());
            } else {
                if (x.getBody() instanceof StatementBlock) {
                    printElement(1, 0, x.getBody());
                } else {
                    printElement(1, +1, 0, x.getBody());
                    changeLevel(-1);
                }
            }
        }
        printFooter(x);
    }

    public void visitEnhancedFor(EnhancedFor x) {
        printHeader(x);
        printElementIndentation(x);
        print(getBooleanProperty(GLUE_CONTROL_EXPRESSIONS) ? "for(" : "for (");
        boolean glueExprParentheses = getBooleanProperty(GLUE_EXPRESSION_PARENTHESES);
        if (!glueExprParentheses) {
            print(' ');
        }
        printCommaList(x.getInitializers()); // must not be null for enhanced for loop
        print(':');
        printElement(1, x.getGuard()); // must not be null for enhanced for loop
        if (!glueExprParentheses) {
            print(' ');
        }
        print(')');
        if (x.getBody() == null || x.getBody() instanceof EmptyStatement) {
            print(';');
        } else {
            if (getBooleanProperty(GLUE_STATEMENT_BLOCKS)) {
                printElement(1, x.getBody());
            } else {
                printElement(1, +1, 0, x.getBody());
                changeLevel(-1);
            }
        }
        printFooter(x);
    }

    public void visitWhile(While x) {
        printHeader(x);
        printElementIndentation(x);
        print(getBooleanProperty(GLUE_CONTROL_EXPRESSIONS) ? "while(" : "while (");
        boolean glueExpParentheses = getBooleanProperty(GLUE_EXPRESSION_PARENTHESES);
        if (!glueExpParentheses) {
            print(' ');
        }
        if (x.getGuard() != null) {
            printElement(x.getGuard());
        }
        if (glueExpParentheses) {
            print(')');
        } else {
            print(" )");
        }
        if (x.getBody() == null || x.getBody() instanceof EmptyStatement) {
            print(';');
        } else {
            if (getBooleanProperty(GLUE_STATEMENT_BLOCKS)) {
                printElement(1, x.getBody());
            } else {
                if (x.getBody() instanceof StatementBlock) {
                    printElement(1, 0, x.getBody());
                } else {
                    printElement(1, +1, 0, x.getBody());
                    changeLevel(-1);
                }
            }
        }
        printFooter(x);
    }

    public void visitAssert(Assert x) {
        printHeader(x);
        printElementIndentation(x);
        print("assert");
        if (x.getCondition() != null) {
            printElement(1, x.getCondition());
        }
        if (x.getMessage() != null) {
            print(" :");
            printElement(1, x.getMessage());
        }
        print(';');
        printFooter(x);
    }

    public void visitIf(If x) {
        printHeader(x);
        printElementIndentation(x);
        print(getBooleanProperty(GLUE_CONTROL_EXPRESSIONS) ? "if(" : "if (");
        boolean glueExpr = getBooleanProperty(GLUE_EXPRESSION_PARENTHESES);
        if (x.getExpression() != null) {
            if (glueExpr) {
                printElement(x.getExpression());
            } else {
                printElement(1, x.getExpression());
            }
        }
        if (glueExpr) {
            print(')');
        } else {
            print(" )");
        }
        if (x.getThen() != null) {
            if (getBooleanProperty(GLUE_STATEMENT_BLOCKS)) {
                printElement(1, x.getThen());
            } else {
                if (x.getThen().getBody() instanceof StatementBlock) {
                    printElement(1, 0, x.getThen());
                } else {
                    printElement(1, +1, 0, x.getThen());
                    changeLevel(-1);
                }
            }
        }
        if (x.getElse() != null) {
            if (getBooleanProperty(GLUE_SEQUENTIAL_BRANCHES)) {
                printElement(1, x.getElse());
            } else {
                printElement(1, 0, x.getElse());
            }
        }
        printFooter(x);
    }

    public void visitSwitch(Switch x) {
        printHeader(x);
        printElementIndentation(x);
        print("switch (");
        if (x.getExpression() != null) {
            printElement(x.getExpression());
        }
        print(") {");
        if (x.getBranchList() != null) {
            if (getBooleanProperty(GLUE_SEQUENTIAL_BRANCHES)) {
                printLineList(1, +1, x.getBranchList());
                changeLevel(-1);
            } else {
                printLineList(1, 0, x.getBranchList());
            }
        }
        printIndentation(1, getTotalIndentation());
        print('}');
        printFooter(x);
    }

    public void visitTry(Try x) {
        printHeader(x);
        printElementIndentation(x);
        print("try");
        if (x.getBody() != null) {
            if (getBooleanProperty(GLUE_STATEMENT_BLOCKS)) {
                printElement(1, x.getBody());
            } else {
                printElement(1, 0, x.getBody());
            }
        }
        if (x.getBranchList() != null) {
            if (getBooleanProperty(GLUE_SEQUENTIAL_BRANCHES)) {
                for (int i = 0; i < x.getBranchList().size(); i++) {
                    printElement(1, x.getBranchList().get(i));
                }
            } else {
                printLineList(1, 0, x.getBranchList());
            }
        }
        printFooter(x);
    }

    public void visitLabeledStatement(LabeledStatement x) {
        printHeader(x);
        if (x.getIdentifier() != null) {
            printElement(x.getIdentifier());
            printElementIndentation(x);
            print(':');
        }
        if (x.getBody() != null) {
            printElement(1, 0, x.getBody());
        }
        printFooter(x);
    }

    public void visitSynchronizedBlock(SynchronizedBlock x) {
        printHeader(x);
        printElementIndentation(x);
        print("synchronized");
        if (x.getExpression() != null) {
            print('(');
            printElement(x.getExpression());
            print(')');
        }
        if (x.getBody() != null) {
            printElement(1, x.getBody());
        }
        printFooter(x);
    }

    public void visitImport(Import x) {
        printHeader(x);
        printElementIndentation(x);
        print("import");
        if (x.isStaticImport()) {
            print(" static");
        }
        printElement(1, x.getReference());
        if (x.isMultiImport()) {
            print(".*;");
        } else {
            if (x.isStaticImport()) {
                print(".");
                printElement(x.getStaticIdentifier());
            }
            print(';');
        }
        printFooter(x);
    }

    public void visitUncollatedReferenceQualifier(UncollatedReferenceQualifier x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            printElement(x.getReferencePrefix());
            printElementIndentation(x);
            print('.');
        }
        if (x.getIdentifier() != null) {
            printElement(x.getIdentifier());
        }
        printFooter(x);
    }

    public void visitExtends(Extends x) {
        printHeader(x);
        if (x.getSupertypes() != null) {
            printElementIndentation(x);
            print("extends");
            printCommaList(0, 0, 1, x.getSupertypes());
        }
        printFooter(x);
    }

    public void visitImplements(Implements x) {
        printHeader(x);
        if (x.getSupertypes() != null) {
            printElementIndentation(x);
            print("implements");
            printCommaList(0, 0, 1, x.getSupertypes());
        }
        printFooter(x);
    }

    public void visitVariableSpecification(VariableSpecification x) {
        printHeader(x);
        printElement(x.getIdentifier());
        for (int i = 0; i < x.getDimensions(); i += 1) {
            print("[]");
        }
        if (x.getInitializer() != null) {
            print(" = ");
            printElement(0, 0, 1, x.getInitializer());
        }
        printFooter(x);
    }

    public void visitBinaryAnd(BinaryAnd x) {
        printHeader(x);
        printOperator(x, "&");
        printFooter(x);
    }

    public void visitBinaryAndAssignment(BinaryAndAssignment x) {
        printHeader(x);
        printOperator(x, "&=");
        printFooter(x);
    }

    public void visitBinaryOrAssignment(BinaryOrAssignment x) {
        printHeader(x);
        printOperator(x, "|=");
        printFooter(x);
    }

    public void visitBinaryXOrAssignment(BinaryXOrAssignment x) {
        printHeader(x);
        printOperator(x, "^=");
        printFooter(x);
    }

    public void visitCopyAssignment(CopyAssignment x) {
        printHeader(x);
        printOperator(x, "=");
        printFooter(x);
    }

    public void visitDivideAssignment(DivideAssignment x) {
        printHeader(x);
        printOperator(x, "/=");
        printFooter(x);
    }

    public void visitMinusAssignment(MinusAssignment x) {
        printHeader(x);
        printOperator(x, "-=");
        printFooter(x);
    }

    public void visitModuloAssignment(ModuloAssignment x) {
        printHeader(x);
        printOperator(x, "%=");
        printFooter(x);
    }

    public void visitPlusAssignment(PlusAssignment x) {
        printHeader(x);
        printOperator(x, "+=");
        printFooter(x);
    }

    public void visitPostDecrement(PostDecrement x) {
        printHeader(x);
        printOperator(x, "--");
        printFooter(x);
    }

    public void visitPostIncrement(PostIncrement x) {
        printHeader(x);
        printOperator(x, "++");
        printFooter(x);
    }

    public void visitPreDecrement(PreDecrement x) {
        printHeader(x);
        printOperator(x, "--");
        printFooter(x);
    }

    public void visitPreIncrement(PreIncrement x) {
        printHeader(x);
        printOperator(x, "++");
        printFooter(x);
    }

    public void visitShiftLeftAssignment(ShiftLeftAssignment x) {
        printHeader(x);
        printOperator(x, "<<=");
        printFooter(x);
    }

    public void visitShiftRightAssignment(ShiftRightAssignment x) {
        printHeader(x);
        printOperator(x, ">>=");
        printFooter(x);
    }

    public void visitTimesAssignment(TimesAssignment x) {
        printHeader(x);
        printOperator(x, "*=");
        printFooter(x);
    }

    public void visitUnsignedShiftRightAssignment(UnsignedShiftRightAssignment x) {
        printHeader(x);
        printOperator(x, ">>>=");
        printFooter(x);
    }

    public void visitBinaryNot(BinaryNot x) {
        printHeader(x);
        printOperator(x, "~");
        printFooter(x);
    }

    public void visitBinaryOr(BinaryOr x) {
        printHeader(x);
        printOperator(x, "|");
        printFooter(x);
    }

    public void visitBinaryXOr(BinaryXOr x) {
        printHeader(x);
        printOperator(x, "^");
        printFooter(x);
    }

    public void visitConditional(Conditional x) {
        printHeader(x);
        boolean addParentheses = x.isToBeParenthesized();
        if (x.getArguments() != null) {
            if (addParentheses) {
                print('(');
            }
            printElement(0, x.getArguments().get(0));
            print(" ?");
            printElement(1, x.getArguments().get(1));
            print(" :");
            printElement(1, x.getArguments().get(2));
            if (addParentheses) {
                print(')');
            }
        }
        printFooter(x);
    }

    public void visitDivide(Divide x) {
        printHeader(x);
        printOperator(x, "/");
        printFooter(x);
    }

    public void visitEquals(Equals x) {
        printHeader(x);
        printOperator(x, "==");
        printFooter(x);
    }

    public void visitGreaterOrEquals(GreaterOrEquals x) {
        printHeader(x);
        printOperator(x, ">=");
        printFooter(x);
    }

    public void visitGreaterThan(GreaterThan x) {
        printHeader(x);
        printOperator(x, ">");
        printFooter(x);
    }

    public void visitLessOrEquals(LessOrEquals x) {
        printHeader(x);
        printOperator(x, "<=");
        printFooter(x);
    }

    public void visitLessThan(LessThan x) {
        printHeader(x);
        printOperator(x, "<");
        printFooter(x);
    }

    public void visitNotEquals(NotEquals x) {
        printHeader(x);
        printOperator(x, "!=");
        printFooter(x);
    }

    public void visitNewArray(NewArray x) {
        printHeader(x);
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses) {
            print('(');
        }
        printElementIndentation(x);
        print("new");
        printElement(1, x.getTypeReference());
        int i = 0;
        if (x.getArguments() != null) {
            for (; i < x.getArguments().size(); i += 1) {
                print('[');
                printElement(x.getArguments().get(i));
                print(']');
            }
        }
        for (; i < x.getDimensions(); i += 1) {
            print("[]");
        }
        if (x.getArrayInitializer() != null) {
            printElement(1, x.getArrayInitializer());
        }
        if (addParentheses) {
            print(')');
        }
        printFooter(x);
    }

    public void visitInstanceof(Instanceof x) {
        printHeader(x);
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses) {
            print('(');
        }
        if (x.getArguments() != null) {
            printElement(0, x.getArguments().get(0));
        }
        printElementIndentation(1, x);
        print("instanceof");
        if (x.getTypeReference() != null) {
            printElement(1, x.getTypeReference());
        }
        if (addParentheses) {
            print(')');
        }
        printFooter(x);
    }

    public void visitNew(New x) {
        printHeader(x);
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses) {
            print('(');
        }
        if (x.getReferencePrefix() != null) {
            printElement(0, x.getReferencePrefix());
            print('.');
        }
        printElementIndentation(x);
        print("new");
        printElement(1, x.getTypeReference());
        if (getBooleanProperty(GLUE_PARAMETER_LISTS)) {
            print('(');
        } else {
            print(" (");
        }
        if (x.getArguments() != null) {
            printCommaList(x.getArguments());
        }
        print(')');
        if (x.getClassDeclaration() != null) {
            printElement(1, x.getClassDeclaration());
        }
        if (addParentheses) {
            print(')');
        }
        if (x.getStatementContainer() != null) {
            print(';');
        }
        printFooter(x);
    }

    public void visitTypeCast(TypeCast x) {
        printHeader(x);
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses) {
            print('(');
        }
        printElementIndentation(x);
        print('(');
        if (x.getTypeReference() != null) {
            printElement(0, x.getTypeReference());
        }
        print(')');
        if (x.getArguments() != null) {
            printElement(0, x.getArguments().get(0));
        }
        if (addParentheses) {
            print(')');
        }
        printFooter(x);
    }

    public void visitLogicalAnd(LogicalAnd x) {
        printHeader(x);
        printOperator(x, "&&");
        printFooter(x);
    }

    public void visitLogicalNot(LogicalNot x) {
        printHeader(x);
        printOperator(x, "!");
        printFooter(x);
    }

    public void visitLogicalOr(LogicalOr x) {
        printHeader(x);
        printOperator(x, "||");
        printFooter(x);
    }

    public void visitMinus(Minus x) {
        printHeader(x);
        printOperator(x, "-");
        printFooter(x);
    }

    public void visitModulo(Modulo x) {
        printHeader(x);
        printOperator(x, "%");
        printFooter(x);
    }

    public void visitNegative(Negative x) {
        printHeader(x);
        printOperator(x, "-");
        printFooter(x);
    }

    public void visitPlus(Plus x) {
        printHeader(x);
        printOperator(x, "+");
        printFooter(x);
    }

    public void visitPositive(Positive x) {
        printHeader(x);
        printOperator(x, "+");
        printFooter(x);
    }

    public void visitShiftLeft(ShiftLeft x) {
        printHeader(x);
        printOperator(x, "<<");
        printFooter(x);
    }

    public void visitShiftRight(ShiftRight x) {
        printHeader(x);
        printOperator(x, ">>");
        printFooter(x);
    }

    public void visitTimes(Times x) {
        printHeader(x);
        printOperator(x, "*");
        printFooter(x);
    }

    public void visitUnsignedShiftRight(UnsignedShiftRight x) {
        printHeader(x);
        printOperator(x, ">>>");
        printFooter(x);
    }

    public void visitArrayReference(ArrayReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            printElement(x.getReferencePrefix());
        }
        if (x.getDimensionExpressions() != null) {
            int s = x.getDimensionExpressions().size();
            for (int i = 0; i < s; i += 1) {
                print('[');
                printElement(x.getDimensionExpressions().get(i));
                print(']');
            }
        }
        printFooter(x);
    }

    public void visitFieldReference(FieldReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            printElement(x.getReferencePrefix());
            printElementIndentation(x);
            print('.');
        }
        if (x.getIdentifier() != null) {
            printElement(x.getIdentifier());
        }
        printFooter(x);
    }

    public void visitVariableReference(VariableReference x) {
        printHeader(x);
        if (x.getIdentifier() != null) {
            printElement(x.getIdentifier());
        }
        printFooter(x);
    }

    public void visitMetaClassReference(MetaClassReference x) {
        printHeader(x);
        if (x.getTypeReference() != null) {
            printElement(x.getTypeReference());
            printElementIndentation(x);
            print('.');
        }
        print("class");
        printFooter(x);
    }

    public void visitMethodReference(MethodReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            printElement(x.getReferencePrefix());
            // printElementIndentation(x); not yet implemented
            print('.');
        }
        if (x.getTypeArguments() != null && x.getTypeArguments().size() > 0) {
            // a prefix must be present to allow type arguments. Why is not clear,
            // so we leave this here in case it'll change sometime
            print('<');
            printCommaList(x.getTypeArguments());
            print('>');
        }
        if (x.getIdentifier() != null) {
            printElement(x.getIdentifier());
        }
        if (getBooleanProperty(GLUE_PARAMETER_LISTS)) {
            print('(');
        } else {
            print(" (");
        }
        if (x.getArguments() != null) {
            printCommaList(x.getArguments());
        }
        print(')');
        if (x.getStatementContainer() != null) {
            print(';');
        }
        printFooter(x);
    }

    public void visitSuperConstructorReference(SuperConstructorReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            printElement(x.getReferencePrefix());
            print('.');
        }
        printElementIndentation(x);
        if (getBooleanProperty(GLUE_PARAMETER_LISTS)) {
            print("super(");
        } else {
            print("super (");
        }
        if (x.getArguments() != null) {
            printCommaList(x.getArguments());
        }
        print(");");
        printFooter(x);
    }

    public void visitThisConstructorReference(ThisConstructorReference x) {
        printHeader(x);
        printElementIndentation(x);
        print(getBooleanProperty(GLUE_PARAMETER_LISTS) ? "this(" : "this (");
        if (x.getArguments() != null) {
            printCommaList(x.getArguments());
        }
        print(");");
        printFooter(x);
    }

    public void visitSuperReference(SuperReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            printElement(x.getReferencePrefix());
            printElementIndentation(x);
            print(".super");
        } else {
            printElementIndentation(x);
            print("super");
        }
        printFooter(x);
    }

    public void visitThisReference(ThisReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            printElement(x.getReferencePrefix());
            printElementIndentation(x);
            print(".this");
        } else {
            printElementIndentation(x);
            print("this");
        }
        printFooter(x);
    }

    public void visitArrayLengthReference(ArrayLengthReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            printElement(x.getReferencePrefix());
            print('.');
        }
        printElementIndentation(x);
        print("length");
        printFooter(x);
    }

    public void visitThen(Then x) {
        printHeader(x);
        if (x.getBody() != null) {
            printElement(x.getBody());
        }
        printFooter(x);
    }

    public void visitElse(Else x) {
        printHeader(x);
        printElementIndentation(x);
        print("else");
        if (x.getBody() != null) {
            if (getBooleanProperty(GLUE_STATEMENT_BLOCKS)) {
                printElement(1, x.getBody());
            } else {
                if (x.getBody() instanceof StatementBlock) {
                    printElement(1, 0, x.getBody());
                } else {
                    printElement(1, +1, 0, x.getBody());
                    changeLevel(-1);
                }
            }
        }
        printFooter(x);
    }

    public void visitCase(Case x) {
        printHeader(x);
        printElementIndentation(x);
        print("case");
        if (x.getExpression() != null) {
            printElement(1, x.getExpression());
        }
        print(':');
        if (x.getBody() != null && x.getBody().size() > 0) {
            printLineList(1, +1, x.getBody());
            changeLevel(-1);
        }
        printFooter(x);
    }

    public void visitCatch(Catch x) {
        printHeader(x);
        if (getBooleanProperty(GLUE_CONTROL_EXPRESSIONS)) {
            printElementIndentation(x);
            print("catch(");
        } else {
            printElementIndentation(x);
            print("catch (");
        }
        if (x.getParameterDeclaration() != null) {
            printElement(x.getParameterDeclaration());
        }
        print(')');
        if (x.getBody() != null) {
            printElement(1, x.getBody());
        }
        printFooter(x);
    }

    public void visitDefault(Default x) {
        printHeader(x);
        printElementIndentation(x);
        print("default:");
        if (x.getBody() != null && x.getBody().size() > 0) {
            printLineList(1, +1, x.getBody());
            changeLevel(-1);
        }
        printFooter(x);
    }

    public void visitFinally(Finally x) {
        printHeader(x);
        printElementIndentation(x);
        print("finally");
        if (x.getBody() != null) {
            printElement(1, x.getBody());
        }
        printFooter(x);
    }

    public void visitAbstract(Abstract x) {
        printHeader(x);
        printElementIndentation(x);
        print("abstract");
        printFooter(x);
    }

    public void visitFinal(Final x) {
        printHeader(x);
        printElementIndentation(x);
        print("final");
        printFooter(x);
    }

    public void visitNative(Native x) {
        printHeader(x);
        printElementIndentation(x);
        print("native");
        printFooter(x);
    }

    public void visitPrivate(Private x) {
        printHeader(x);
        printElementIndentation(x);
        print("private");
        printFooter(x);
    }

    public void visitProtected(Protected x) {
        printHeader(x);
        printElementIndentation(x);
        print("protected");
        printFooter(x);
    }

    public void visitPublic(Public x) {
        printHeader(x);
        printElementIndentation(x);
        print("public");
        printFooter(x);
    }

    public void visitStatic(Static x) {
        printHeader(x);
        printElementIndentation(x);
        print("static");
        printFooter(x);
    }

    public void visitStrictFp(StrictFp x) {
        printHeader(x);
        printElementIndentation(x);
        print("strictfp");
        printFooter(x);
    }

    public void visitSynchronized(Synchronized x) {
        printHeader(x);
        printElementIndentation(x);
        print("synchronized");
        printFooter(x);
    }

    public void visitTransient(Transient x) {
        printHeader(x);
        printElementIndentation(x);
        print("transient");
        printFooter(x);
    }

    public void visitVolatile(Volatile x) {
        printHeader(x);
        printElementIndentation(x);
        print("volatile");
        printFooter(x);
    }

    public void visitAnnotationUse(AnnotationUseSpecification a) {
        // TODO better indentation handling
        printHeader(a);
        printElementIndentation(a);
        print('@');
        printElement(a.getTypeReference());
        List<AnnotationElementValuePair> evp = a.getElementValuePairs();
        if (evp != null) {
            print('(');
            printCommaList(0, 0, 0, evp);
            print(')');
        }
        printFooter(a);
    }

    public void visitElementValuePair(AnnotationElementValuePair x) {
        // TODO better indentation handling
        printHeader(x);
        printElementIndentation(x);
        AnnotationPropertyReference id = x.getElement();
        if (id != null) {
            printElement(id);
            print(" =");
        }
        ProgramElement ev = x.getElementValue();
        if (ev != null) {
            printElement(ev);
        }
        printFooter(x);
    }

    public void visitAnnotationPropertyReference(AnnotationPropertyReference x) {
        printHeader(x);
        printElementIndentation(x);
        Identifier id = x.getIdentifier();
        if (id != null) {
            printElement(id);
        }
        printFooter(x);
    }


    public void visitEmptyStatement(EmptyStatement x) {
        printHeader(x);
        printElementIndentation(x);
        print(';');
        printFooter(x);
    }

    public void visitComment(Comment x) {
        printElementIndentation(x);
        print(x.getText());

        if (overwriteParsePositions) {
            overwritePosition.setPosition(line, Math.max(0, column - 1));
            x.getLastElement().setEndPosition(overwritePosition);
        }
    }

    public void visitParenthesizedExpression(ParenthesizedExpression x) {
        printHeader(x);
        printElementIndentation(x);
        print('(');
        if (x.getArguments() != null) {
            printElement(x.getArguments().get(0));
        }
        print(')');
        printFooter(x);
    }

    public void visitEnumConstructorReference(EnumConstructorReference x) {
        printHeader(x);
        printElementIndentation(x);
        List<? extends Expression> exprs = x.getArguments();
        if (exprs != null) {
            print('(');
            printCommaList(exprs);
            print(')');
        }
        if (x.getClassDeclaration() != null) {
            printElement(x.getClassDeclaration());
        }
    }

    public void visitEnumConstantDeclaration(EnumConstantDeclaration x) {
        printHeader(x);
        printElementIndentation(x);
        if (x.getAnnotations() != null && x.getAnnotations().size() != 0) {
            printKeywordList(x.getAnnotations());
            print(' ');
        }
        printElement(1, x.getEnumConstantSpecification());
        printFooter(x);
    }

    public void visitEnumConstantSpecification(EnumConstantSpecification x) {
        printHeader(x);
        printElement(x.getIdentifier());
        printElement(x.getConstructorReference());
        printFooter(x);
    }


    public void visitEnumDeclaration(EnumDeclaration x) {
        printHeader(x);
        int m = 0;
        if (x.getDeclarationSpecifiers() != null) {
            m = x.getDeclarationSpecifiers().size();
        }
        if (m > 0) {
            printKeywordList(x.getDeclarationSpecifiers());
            m = 1;
        }
        // unlike class declarations, enum declarations always require an identifier
        printElementIndentation(m, x);
        print("enum");
        printElement(1, x.getIdentifier());
        // if (x.getImplementedTypes() != null) {
        // // actually, this is not allowed
        // printElement(1, x.getImplementedTypes());
        // }
        print(' ');
        print('{');
        printContainerComments(x);
        // if (x.getMembers() != null && !x.getMembers().isEmpty()) {
        // //printBlockList(2, 1, x.getMembers());
        // printCommaList(2, 1, 1, x.getMembers())
        // changeLevel(-1);
        // }
        printCommaList(2, 1, 1, x.getConstants());
        print(";");
        changeLevel(-1);

        printBlockList(2, 1, x.getNonConstantMembers());
        changeLevel(-1);

        printIndentation(1, getTotalIndentation());
        print('}');
        printFooter(x);
    }

    public void visitTypeArgument(TypeArgumentDeclaration x) {
        printHeader(x);
        switch (x.getWildcardMode()) {
        case None:
            break;
        case Any:
            print("?");
            break;
        case Extends:
            print("? extends ");
            break;
        case Super:
            print("? super ");
            break;
        }
        if (x.getTypeReferenceCount() == 1) {
            printElement(x.getTypeReferenceAt(0));
        }
        printFooter(x);
    }


    public void visitTypeParameter(TypeParameterDeclaration x) {
        printHeader(x);
        if (x.getIdentifier() != null) {
            printElement(x.getIdentifier());
        }
        if (x.getBounds() != null && x.getBounds().size() != 0) {
            print(" extends ");
            printProgramElementList(0, 0, 0, "&", 0, 1, x.getBounds());
        }
        printFooter(x);
    }

    public void visitParameterDeclaration(ParameterDeclaration x) {
        visitVariableDeclaration(x, x.isVarArg());
    }
}
