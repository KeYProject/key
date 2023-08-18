/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.*;
import java.nio.CharBuffer;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.DefaultServiceConfiguration;
import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.ServiceConfiguration;
import recoder.convenience.TreeWalker;
import recoder.io.ProjectSettings;
import recoder.io.PropertyNames;
import recoder.java.SourceElement.Position;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.*;
import recoder.java.expression.ArrayInitializer;
import recoder.java.expression.ParenthesizedExpression;
import recoder.java.expression.literal.*;
import recoder.java.expression.operator.*;
import recoder.java.reference.*;
import recoder.java.statement.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.parser.JavaCCParser;
import recoder.util.StringUtils;

public class JavaProgramFactory implements ProgramFactory, PropertyChangeListener {
    private static final Logger LOGGER = LoggerFactory.getLogger(JavaProgramFactory.class);
    private final static Position ZERO_POSITION = new Position(0, 0);
    /**
     * The singleton instance of the program factory.
     */
    private static final JavaProgramFactory theFactory = new JavaProgramFactory();
    /**
     * For internal reuse and synchronization.
     */
    private static final JavaCCParser parser = new JavaCCParser(System.in);
    /**
     * The singleton instance of the program factory.
     */
    private static ServiceConfiguration serviceConfiguration;
    /**
     * StringWriter for toSource.
     */
    private static StringWriter writer = new StringWriter();
    /**
     * PrettyPrinter, for toSource.
     */
    private static PrettyPrinter sourcePrinter;
    private static boolean useAddNewlineReader = true;

    /**
     * Private constructor - use {@link #getInstance}instead.
     */
    protected JavaProgramFactory() { /* singleton */
    }

    /**
     * Returns the single instance of this class.
     */
    public static JavaProgramFactory getInstance() {
        return theFactory;
    }

    private static void attachComment(Comment c, ProgramElement pe) {
        ProgramElement dest = pe;

        if (c.isPrefixed() && pe instanceof CompilationUnit
                && ((CompilationUnit) pe).getChildCount() > 0) {
            // may need attach to first child element
            ProgramElement fc = ((CompilationUnit) pe).getChildAt(0);
            int distcu = c.getStartPosition().getLine();
            int distfc = fc.getStartPosition().getLine() - c.getEndPosition().getLine();
            if (c instanceof SingleLineComment) {
                distcu--;
            }
            if (distcu >= distfc) {
                dest = fc;
            }
        } else if (!c.isPrefixed()) {
            NonTerminalProgramElement ppe = dest.getASTParent();
            int i = 0;
            if (ppe != null) {
                for (; ppe.getChildAt(i) != dest; i++) {
                }
            }
            if (i == 0) { // before syntactical parent
                c.setPrefixed(true);
            } else {
                dest = ppe.getChildAt(i - 1);
                while (dest instanceof NonTerminalProgramElement) {
                    ppe = (NonTerminalProgramElement) dest;
                    i = ppe.getChildCount();
                    if (i == 0) {
                        break;
                    }
                    dest = ppe.getChildAt(i - 1);
                }
                // Comments attached better - Fix by T.Gutzmann
                ppe = dest.getASTParent();
                boolean doChange = false;
                while (ppe != null && ppe.getASTParent() != null
                        && ppe.getEndPosition().compareTo(dest.getEndPosition()) >= 0
                        && ppe.getASTParent().getEndPosition()
                                .compareTo(c.getStartPosition()) <= 0) {
                    ppe = ppe.getASTParent();
                    doChange = true;
                }
                if (ppe != null && doChange) {
                    dest = ppe;
                }
                if (dest instanceof NonTerminalProgramElement) {
                    ppe = (NonTerminalProgramElement) dest;
                    if (ppe.getEndPosition().compareTo(c.getStartPosition()) >= 0) {
                        while (ppe.getChildCount() > 0 && ppe.getChildAt(ppe.getChildCount() - 1)
                                .getEndPosition().compareTo(ppe.getEndPosition()) == 0
                        // TODO Gutzmann - this shouldn't be neccessary
                                && ppe.getChildAt(
                                    ppe.getChildCount() - 1) instanceof NonTerminalProgramElement) {
                            ppe =
                                (NonTerminalProgramElement) ppe.getChildAt(ppe.getChildCount() - 1);
                            dest = ppe;
                        }
                        c.setContainerComment(true);
                    }
                }
                if (!c.isContainerComment() && pe != dest) {
                    // if in between two program elements in same line, prefer prefixing/look at
                    // number of whitespaces
                    if (pe.getFirstElement().getStartPosition().getLine() == dest.getLastElement()
                            .getEndPosition().getLine()) {
                        // TODO strategy when looking at # of whitespaces ?!
                        int before = c.getStartPosition().getColumn()
                                - dest.getLastElement().getEndPosition().getColumn();
                        int after = pe.getFirstElement().getStartPosition().getColumn()
                                - c.getEndPosition().getColumn();
                        if (after <= before) {
                            dest = pe;
                            c.setPrefixed(true);
                        }
                    }
                }
            }
        }
        if (c.isPrefixed()) {
            // once again, go up as long as possible
            NonTerminalProgramElement npe = dest.getASTParent();
            while (npe != null && npe.getStartPosition().equals(dest.getStartPosition())) {
                dest = npe;
                npe = npe.getASTParent();
            }
        } else {
            NonTerminalProgramElement npe = dest.getASTParent();
            while (npe != null && npe.getEndPosition().equals(dest.getEndPosition())) {
                dest = npe;
                npe = npe.getASTParent();
            }
        }
        // if this is a full line comment, may need to change
        if (c.isPrefixed() && c.getEndPosition().getLine() < dest.getStartPosition().getLine()) {
            NonTerminalProgramElement npe = dest.getASTParent();
            if (npe != null) {
                int idx = npe.getIndexOfChild(dest);
                if (idx > 0) {
                    // calculate distance, maybe attach to next element
                    int distPre = dest.getStartPosition().getLine() - c.getEndPosition().getLine();
                    int distPost = c.getStartPosition().getLine()
                            - npe.getChildAt(idx - 1).getEndPosition().getLine();
                    if (c instanceof SingleLineComment) {
                        distPost--; // prefer postfix comment in this case
                    }
                    if (distPost < distPre) {
                        dest = npe.getChildAt(idx - 1);
                        c.setPrefixed(false);
                    }
                }
            }
        } else if (!c.isPrefixed()
                && c.getStartPosition().getLine() > dest.getEndPosition().getLine()) {
            NonTerminalProgramElement npe = dest.getASTParent();
            if (npe != null) {
                int idx = npe.getIndexOfChild(dest);
                if (idx + 1 < npe.getChildCount()) {
                    int distPre = npe.getChildAt(idx + 1).getStartPosition().getLine()
                            - c.getEndPosition().getLine();
                    int distPost = c.getStartPosition().getLine() - dest.getEndPosition().getLine();
                    if (c instanceof SingleLineComment) {
                        distPost--;
                    }
                    if (distPre <= distPost) {
                        dest = npe.getChildAt(idx + 1);
                        c.setPrefixed(true);
                    }
                }
            }
        }

        if (c instanceof SingleLineComment && c.isPrefixed()) {
            Position p = dest.getFirstElement().getRelativePosition();
            if (p.getLine() < 1) {
                p.setLine(1);
                dest.getFirstElement().setRelativePosition(p);
            }
        }
        ASTList<Comment> cml = dest.getComments();
        if (cml == null) {
            dest.setComments(cml = new ASTArrayList<>());
        }
        cml.add(c);
    }

    /**
     * Perform post work on the created element. Creates parent links and assigns comments.
     */
    private static void postWork(ProgramElement pe) {

        List<Comment> comments = JavaCCParser.getComments();
        int commentIndex = 0;
        int commentCount = comments.size();
        Position cpos = ZERO_POSITION;
        Comment current = null;
        if (commentIndex < commentCount) {
            current = comments.get(commentIndex);
            cpos = current.getFirstElement().getStartPosition();
        }
        TreeWalker tw = new TreeWalker(pe);
        while (tw.next()) {
            pe = tw.getProgramElement();
            if (pe instanceof NonTerminalProgramElement) {
                ((NonTerminalProgramElement) pe).makeParentRoleValid();
            }
            Position pos = pe.getFirstElement().getStartPosition();
            while ((commentIndex < commentCount) && pos.compareTo(cpos) > 0) {
                attachComment(current, pe);
                commentIndex += 1;
                if (commentIndex < commentCount) {
                    current = comments.get(commentIndex);
                    cpos = current.getFirstElement().getStartPosition();
                }
            }
        }
        if (commentIndex < commentCount) {
            while (pe.getASTParent() != null) {
                pe = pe.getASTParent();
            }

            /*
             * postfixed comments may need to be attached to a child of current program element, so
             * move down AST while child is closer to comment position.
             */
            do {
                current = comments.get(commentIndex);
                ProgramElement dest = pe;
                ProgramElement newDest = null;
                while (dest instanceof NonTerminalProgramElement) {
                    NonTerminalProgramElement npe = (NonTerminalProgramElement) dest;
                    if (npe.getChildCount() == 0) {
                        break;
                    }
                    newDest = npe.getChildAt(npe.getChildCount() - 1);
                    if ((npe.getEndPosition().compareTo(current.getStartPosition()) > 0
                            || ((npe.getEndPosition().compareTo(current.getStartPosition()) == 0)
                                    && newDest.getEndPosition()
                                            .compareTo(current.getStartPosition()) <= 0))
                            && dest != newDest) {
                        dest = newDest;
                    } else {
                        break;
                    }
                }
                ASTList<Comment> cml = dest.getComments();
                if (cml == null) {
                    dest.setComments(cml = new ASTArrayList<>());
                }
                current.setPrefixed(false);
                cml.add(current);
                commentIndex += 1;
            } while (commentIndex < commentCount);
        }
    }

    /**
     * Replacement for Integer.parseInt allowing "supercharged" non-decimal constants. In contrast
     * to Integer.parseInt, works for 0x80000000 and higher octal and hex constants as well as
     * -MIN_VALUE which is allowed in case that the minus sign has been interpreted as an unary
     * minus. The method will return Integer.MIN_VALUE in that case; this is fine as -MIN_VALUE ==
     * MIN_VALUE.
     */
    public static int parseInt(String nm) throws NumberFormatException {
        int radix;
        boolean negative = false;
        int result;

        int index = 0;
        if (nm.startsWith("-")) {
            negative = true;
            index++;
        }
        if (nm.startsWith("0x", index) || nm.startsWith("0X", index)) {
            index += 2;
            radix = 16;
        } else if (nm.startsWith("0", index) && nm.length() > 1 + index) {
            index++;
            radix = 8;
        } else {
            radix = 10;
        }
        if (nm.startsWith("-", index)) {
            throw new NumberFormatException("Negative sign in wrong position");
        }
        int len = nm.length() - index;
        if (radix == 16 && len == 8) {
            char first = nm.charAt(index);
            index += 1;
            result = Integer.parseInt(nm.substring(index), radix);
            result |= Character.digit(first, 16) << 28;
            return negative ? -result : result;
        }
        if (radix == 8 && len == 11) {
            char first = nm.charAt(index);
            index += 1;
            result = Integer.parseInt(nm.substring(index), radix);
            result |= Character.digit(first, 8) << 30;
            return negative ? -result : result;
        }
        if (!negative && radix == 10 && len == 10 && nm.indexOf("2147483648", index) == index) {
            return Integer.MIN_VALUE;
        }
        result = Integer.parseInt(nm.substring(index), radix);
        return negative ? -result : result;
    }

    /**
     * Replacement for Long.parseLong which is not available in JDK 1.1 and does not handle 'l' or
     * 'L' suffices in JDK 1.2.
     */
    public static long parseLong(String nm) throws NumberFormatException {
        // fixes a bug
        if (nm.equalsIgnoreCase("0L")) {
            return 0;
        }

        int radix;
        boolean negative = false;
        long result;

        int index = 0;
        if (nm.startsWith("-")) {
            negative = true;
            index++;
        }
        if (nm.startsWith("0x", index) || nm.startsWith("0X", index)) {
            index += 2;
            radix = 16;
        } else if (nm.startsWith("0", index) && nm.length() > 1 + index) {
            index++;
            radix = 8;
        } else {
            radix = 10;
        }

        if (nm.startsWith("-", index)) {
            throw new NumberFormatException("Negative sign in wrong position");
        }
        int endIndex = nm.length();
        if (nm.endsWith("L") || nm.endsWith("l")) {
            endIndex -= 1;
        }

        int len = endIndex - index;
        if (radix == 16 && len == 16) {
            char first = nm.charAt(index);
            index += 1;
            result = Long.parseLong(nm.substring(index, endIndex), radix);
            result |= ((long) Character.digit(first, 16)) << 60;
            return negative ? -result : result;
        }
        if (radix == 8 && len == 21) {
            char first = nm.charAt(index);
            index += 1;
            result = Long.parseLong(nm.substring(index, endIndex), radix);
            result |= ((long) Character.digit(first, 8)) << 63;
            return negative ? -result : result;
        }
        if (!negative && radix == 10 && len == 19
                && nm.indexOf("9223372036854775808", index) == index) {
            return Long.MIN_VALUE;
        }
        result = Long.parseLong(nm.substring(index, endIndex), radix);
        return negative ? -result : result;
    }

    /**
     * Demo program reading a single source file and writing it back to stdout using the default
     * {@link PrettyPrinter}.
     */
    public static void main(String[] args) throws Exception {
        if (args.length < 1) {
            System.err.println("Requires a java source file as argument");
            System.exit(1);
        }
        try {
            CompilationUnit cu = new DefaultServiceConfiguration().getProgramFactory()
                    .parseCompilationUnit(new FileReader(args[0], StandardCharsets.UTF_8));
            System.out.println(cu.toSource());
        } catch (IOException | ParserException ioe) {
            LOGGER.warn("Failed to parse", ioe);
        }
    }

    /**
     * Called by the service configuration indicating that all services are known. Services may now
     * start communicating or linking among their configuration partners. The service configuration
     * can be memorized if it has not been passed in by a constructor already.
     *
     * @param cfg the service configuration this services has been assigned to.
     */
    public void initialize(ServiceConfiguration cfg) {
        // if (serviceConfiguration == null) {
        // serviceConfiguration = cfg;
        // } else {
        // Debug
        // .assertBoolean(
        // // TODO low - Gutzmann - should this be != or == ???
        // serviceConfiguration != cfg,
        // "A JavaProgramFactory is a singleton and may be part of one and only one service
        // configuration. We appologize for the inconveniences.");
        // }
        serviceConfiguration = cfg;

        ProjectSettings settings = serviceConfiguration.getProjectSettings();
        settings.addPropertyChangeListener(this);
        writer = new StringWriter();
        sourcePrinter = new PrettyPrinter(writer, settings.getProperties());
        JavaCCParser.setAwareOfAssert(StringUtils
                .parseBooleanProperty(settings.getProperties().getProperty(PropertyNames.JDK1_4)));
        JavaCCParser.setJava5(StringUtils
                .parseBooleanProperty(settings.getProperties().getProperty(PropertyNames.JAVA_5)));
    }

    /**
     * Returns the service configuration this service is a part of.
     *
     * @return the configuration of this service.
     */
    public ServiceConfiguration getServiceConfiguration() {
        return serviceConfiguration;
    }

    /**
     * Parse a {@link CompilationUnit}from the given reader.
     */
    public CompilationUnit parseCompilationUnit(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(useAddNewlineReader ? new AddNewlineReader(in) : in);
            CompilationUnit res = JavaCCParser.CompilationUnit();
            postWork(res);
            return res;
        }
    }

    /**
     * Parse a {@link TypeDeclaration}from the given reader.
     */
    public TypeDeclaration parseTypeDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(in);
            TypeDeclaration res = JavaCCParser.TypeDeclaration();
            postWork(res);
            return res;
        }
    }

    /**
     * Parse a {@link FieldDeclaration}from the given reader.
     */
    public FieldDeclaration parseFieldDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(in);
            FieldDeclaration res = JavaCCParser.FieldDeclaration();
            postWork(res);
            return res;
        }
    }

    /**
     * Parse a {@link MethodDeclaration}from the given reader.
     */
    public MethodDeclaration parseMethodDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(in);
            MethodDeclaration res = JavaCCParser.MethodDeclaration();
            postWork(res);
            return res;
        }
    }

    /**
     * Parse a {@link MemberDeclaration}from the given reader.
     */
    public MemberDeclaration parseMemberDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(in);
            MemberDeclaration res = JavaCCParser.ClassBodyDeclaration();
            postWork(res);
            return res;
        }
    }

    /**
     * Parse a {@link ParameterDeclaration}from the given reader.
     */
    public ParameterDeclaration parseParameterDeclaration(Reader in)
            throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(in);
            ParameterDeclaration res = JavaCCParser.FormalParameter();
            postWork(res);
            return res;
        }
    }

    /**
     * Parse a {@link ConstructorDeclaration}from the given reader.
     */
    public ConstructorDeclaration parseConstructorDeclaration(Reader in)
            throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(in);
            ConstructorDeclaration res = JavaCCParser.ConstructorDeclaration();
            postWork(res);
            return res;
        }
    }

    /**
     * Parse a {@link TypeReference}from the given reader.
     */
    public TypeReference parseTypeReference(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(in);
            TypeReference res = JavaCCParser.ResultType();
            postWork(res);
            return res;
        }
    }

    /**
     * Parse an {@link Expression}from the given reader.
     */
    public Expression parseExpression(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(in);
            Expression res = JavaCCParser.Expression();
            postWork(res);
            return res;
        }
    }

    /**
     * Parse some {@link Statement}s from the given reader.
     */
    public ASTList<Statement> parseStatements(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(in);
            ASTList<Statement> res = JavaCCParser.GeneralizedStatements();
            for (Statement re : res) {
                postWork(re);
            }
            return res;
        }
    }

    /**
     * Parse a {@link StatementBlock}from the given string.
     */
    public StatementBlock parseStatementBlock(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(in);
            StatementBlock res = JavaCCParser.Block();
            postWork(res);
            return res;
        }
    }

    /**
     * Parse a {@link CompilationUnit}from the given string.
     */
    public CompilationUnit parseCompilationUnit(String in) throws ParserException {
        try {
            return parseCompilationUnit(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Parse {@link CompilationUnit}s from the given string.
     */
    public List<CompilationUnit> parseCompilationUnits(String[] ins) throws ParserException {
        try {
            List<CompilationUnit> cus = new ArrayList<>();
            for (String in : ins) {
                CompilationUnit cu =
                    parseCompilationUnit(new FileReader(in, StandardCharsets.UTF_8));
                cus.add(cu);
            }
            return cus;
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Parse a {@link TypeDeclaration}from the given string.
     */
    public TypeDeclaration parseTypeDeclaration(String in) throws ParserException {
        try {
            return parseTypeDeclaration(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Parse a {@link MemberDeclaration}from the given string.
     */
    public MemberDeclaration parseMemberDeclaration(String in) throws ParserException {
        try {
            return parseMemberDeclaration(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Parse a {@link FieldDeclaration}from the given string.
     */
    public FieldDeclaration parseFieldDeclaration(String in) throws ParserException {
        try {
            return parseFieldDeclaration(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Parse a {@link MethodDeclaration}from the given string.
     */
    public MethodDeclaration parseMethodDeclaration(String in) throws ParserException {
        try {
            return parseMethodDeclaration(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Parse a {@link ParameterDeclaration}from the given string.
     */
    public ParameterDeclaration parseParameterDeclaration(String in) throws ParserException {
        try {
            return parseParameterDeclaration(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Parse a {@link ConstructorDeclaration}from the given string.
     */
    public ConstructorDeclaration parseConstructorDeclaration(String in) throws ParserException {
        try {
            return parseConstructorDeclaration(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Parse a {@link TypeReference}from the given string.
     */
    public TypeReference parseTypeReference(String in) throws ParserException {
        try {
            return parseTypeReference(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Parse an {@link Expression}from the given string.
     */
    public Expression parseExpression(String in) throws ParserException {
        try {
            return parseExpression(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Parse a list of {@link Statement}s from the given string.
     */
    public ASTList<Statement> parseStatements(String in) throws ParserException {
        try {
            return parseStatements(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Creates a syntactical representation of the source element.
     */
    String toSource(JavaSourceElement jse) {
        synchronized (writer) {
            sourcePrinter.setIndentationLevel(0);
            jse.accept(sourcePrinter);
            StringBuffer buf = writer.getBuffer();
            String str = buf.toString();
            buf.setLength(0);
            return str;
        }
    }

    /**
     * Returns a new suitable {@link recoder.java.PrettyPrinter}obeying the current project settings
     * for the specified writer,
     *
     * @param out the (initial) writer to print to.
     * @return a new pretty printer.
     */
    public PrettyPrinter getPrettyPrinter(Writer out) {
        return new PrettyPrinter(out, serviceConfiguration.getProjectSettings().getProperties());
    }

    public void propertyChange(PropertyChangeEvent evt) {
        sourcePrinter =
            new PrettyPrinter(writer, serviceConfiguration.getProjectSettings().getProperties());
        String changedProp = evt.getPropertyName();
        if (changedProp.equals(PropertyNames.JDK1_4)) {
            JavaCCParser.setAwareOfAssert(
                StringUtils.parseBooleanProperty(evt.getNewValue().toString()));
            // call automatically sets Java_5 to false if neccessary.
        }
        if (changedProp.equals(PropertyNames.JAVA_5)) {
            JavaCCParser.setJava5(StringUtils.parseBooleanProperty(evt.getNewValue().toString()));
            // call automatically sets awareOfAssert to true if neccessary.
        }
        if (changedProp.equals(PropertyNames.ADD_NEWLINE_AT_END_OF_FILE)) {
            useAddNewlineReader = StringUtils.parseBooleanProperty(evt.getNewValue().toString());
        }
    }

    /**
     * Creates a new {@link Comment}.
     *
     * @return a new instance of Comment.
     */
    public Comment createComment() {
        return new Comment();
    }

    /**
     * Creates a new {@link Comment}.
     *
     * @return a new instance of Comment.
     */
    public Comment createComment(String text) {
        return new Comment(text);
    }

    /**
     * Creates a new {@link Comment}.
     *
     * @return a new instance of Comment.
     */
    public Comment createComment(String text, boolean prefixed) {
        return new Comment(text, prefixed);
    }

    /**
     * Creates a new {@link CompilationUnit}.
     *
     * @return a new instance of CompilationUnit.
     */
    public CompilationUnit createCompilationUnit() {
        return new CompilationUnit();
    }

    /**
     * Creates a new {@link CompilationUnit}.
     *
     * @return a new instance of CompilationUnit.
     */
    public CompilationUnit createCompilationUnit(PackageSpecification pkg, ASTList<Import> imports,
            ASTList<TypeDeclaration> typeDeclarations) {
        return new CompilationUnit(pkg, imports, typeDeclarations);
    }

    /**
     * Creates a new {@link DocComment}.
     *
     * @return a new instance of DocComment.
     */
    public DocComment createDocComment() {
        return new DocComment();
    }

    /**
     * Creates a new {@link DocComment}.
     *
     * @return a new instance of DocComment.
     */
    public DocComment createDocComment(String text) {
        return new DocComment(text);
    }

    /**
     * Creates a new {@link Identifier}.
     *
     * @return a new instance of Identifier.
     */
    public Identifier createIdentifier() {
        return new Identifier();
    }

    /**
     * Creates a new {@link Identifier}.
     *
     * @return a new instance of Identifier.
     */
    public Identifier createIdentifier(String text) {
        return new Identifier(text);
    }

    /**
     * Creates a new {@link Import}.
     *
     * @return a new instance of Import.
     */
    public Import createImport() {
        return new Import();
    }

    /**
     * Creates a new {@link Import}.
     *
     * @return a new instance of Import.
     */
    public Import createImport(TypeReference t, boolean multi) {
        return new Import(t, multi);
    }

    /**
     * Creates a new {@link Import}.
     *
     * @return a new instance of Import.
     */
    public Import createImport(PackageReference t) {
        return new Import(t);
    }

    public Import createStaticImport(TypeReference t) {
        return new Import(t, true, true);
    }

    public Import createStaticImport(TypeReference t, Identifier id) {
        return new Import(t, id);
    }

    /**
     * Creates a new {@link PackageSpecification}.
     *
     * @return a new instance of PackageSpecification.
     */
    public PackageSpecification createPackageSpecification() {
        return new PackageSpecification();
    }

    /**
     * Creates a new {@link PackageSpecification}.
     *
     * @return a new instance of PackageSpecification.
     */
    public PackageSpecification createPackageSpecification(PackageReference pkg) {
        return new PackageSpecification(pkg);
    }

    /**
     * Creates a new {@link SingleLineComment}.
     *
     * @return a new instance of SingleLineComment.
     */
    public SingleLineComment createSingleLineComment() {
        return new SingleLineComment();
    }

    /**
     * Creates a new {@link SingleLineComment}.
     *
     * @return a new instance of SingleLineComment.
     */
    public SingleLineComment createSingleLineComment(String text) {
        return new SingleLineComment(text);
    }

    /**
     * Creates a new {@link TypeReference}.
     *
     * @return a new instance of TypeReference.
     */
    public TypeReference createTypeReference() {
        return new TypeReference();
    }

    /**
     * Creates a new {@link TypeReference}.
     *
     * @return a new instance of TypeReference.
     */
    public TypeReference createTypeReference(Identifier name) {
        return new TypeReference(name);
    }

    /**
     * Creates a new {@link TypeReference}.
     *
     * @return a new instance of TypeReference.
     */
    public TypeReference createTypeReference(ReferencePrefix prefix, Identifier name) {
        return new TypeReference(prefix, name);
    }

    /**
     * Creates a new {@link TypeReference}.
     *
     * @return a new instance of TypeReference.
     */
    public TypeReference createTypeReference(Identifier name, int dim) {
        return new TypeReference(name, dim);
    }

    /**
     * Creates a new {@link PackageReference}.
     *
     * @return a new instance of PackageReference.
     */
    public PackageReference createPackageReference() {
        return new PackageReference();
    }

    /**
     * Creates a new {@link PackageReference}.
     *
     * @return a new instance of PackageReference.
     */
    public PackageReference createPackageReference(Identifier id) {
        return new PackageReference(id);
    }

    /**
     * Creates a new {@link PackageReference}.
     *
     * @return a new instance of PackageReference.
     */
    public PackageReference createPackageReference(PackageReference path, Identifier id) {
        return new PackageReference(path, id);
    }

    /**
     * Creates a new {@link UncollatedReferenceQualifier}.
     *
     * @return a new instance of UncollatedReferenceQualifier.
     */
    public UncollatedReferenceQualifier createUncollatedReferenceQualifier() {
        return new UncollatedReferenceQualifier();
    }

    /**
     * Creates a new {@link UncollatedReferenceQualifier}.
     *
     * @return a new instance of UncollatedReferenceQualifier.
     */
    public UncollatedReferenceQualifier createUncollatedReferenceQualifier(Identifier id) {
        return new UncollatedReferenceQualifier(id);
    }

    /**
     * Creates a new {@link UncollatedReferenceQualifier}.
     *
     * @return a new instance of UncollatedReferenceQualifier.
     */
    public UncollatedReferenceQualifier createUncollatedReferenceQualifier(ReferencePrefix prefix,
            Identifier id) {
        return new UncollatedReferenceQualifier(prefix, id);
    }

    /**
     * Creates a new {@link ClassDeclaration}.
     *
     * @return a new instance of ClassDeclaration.
     */
    public ClassDeclaration createClassDeclaration() {
        return new ClassDeclaration();
    }

    /**
     * Creates a new {@link ClassDeclaration}.
     *
     * @return a new instance of ClassDeclaration.
     */
    public ClassDeclaration createClassDeclaration(ASTList<DeclarationSpecifier> declSpecs,
            Identifier name, Extends extended, Implements implemented,
            ASTList<MemberDeclaration> members) {
        return new ClassDeclaration(declSpecs, name, extended, implemented, members);
    }

    /**
     * Creates a new {@link ClassDeclaration}.
     *
     * @return a new instance of ClassDeclaration.
     */
    public ClassDeclaration createClassDeclaration(ASTList<MemberDeclaration> members) {
        return new ClassDeclaration(members);
    }

    /**
     * Creates a new {@link ClassInitializer}.
     *
     * @return a new instance of ClassInitializer.
     */
    public ClassInitializer createClassInitializer() {
        return new ClassInitializer();
    }

    /**
     * Creates a new {@link ClassInitializer}.
     *
     * @return a new instance of ClassInitializer.
     */
    public ClassInitializer createClassInitializer(StatementBlock body) {
        return new ClassInitializer(body);
    }

    /**
     * Creates a new {@link ClassInitializer}.
     *
     * @return a new instance of ClassInitializer.
     */
    public ClassInitializer createClassInitializer(Static modifier, StatementBlock body) {
        return new ClassInitializer(modifier, body);
    }

    /**
     * Creates a new {@link ConstructorDeclaration}.
     *
     * @return a new instance of ConstructorDeclaration.
     */
    public ConstructorDeclaration createConstructorDeclaration() {
        return new ConstructorDeclaration();
    }

    /**
     * Creates a new {@link ConstructorDeclaration}.
     *
     * @return a new instance of ConstructorDeclaration.
     */
    public ConstructorDeclaration createConstructorDeclaration(VisibilityModifier modifier,
            Identifier name, ASTList<ParameterDeclaration> parameters, Throws exceptions,
            StatementBlock body) {
        return new ConstructorDeclaration(modifier, name, parameters, exceptions, body);
    }

    /**
     * Creates a new {@link Throws}.
     *
     * @return a new instance of Throws.
     */
    public Throws createThrows() {
        return new Throws();
    }

    /**
     * Creates a new {@link Throws}.
     *
     * @return a new instance of Throws.
     */
    public Throws createThrows(TypeReference exception) {
        return new Throws(exception);
    }

    /**
     * Creates a new {@link Throws}.
     *
     * @return a new instance of Throws.
     */
    public Throws createThrows(ASTList<TypeReference> list) {
        return new Throws(list);
    }

    /**
     * Creates a new {@link FieldDeclaration}.
     *
     * @return a new instance of FieldDeclaration.
     */
    public FieldDeclaration createFieldDeclaration() {
        return new FieldDeclaration();
    }

    /**
     * Creates a new {@link FieldDeclaration}.
     *
     * @return a new instance of FieldDeclaration.
     */
    public FieldDeclaration createFieldDeclaration(TypeReference typeRef, Identifier name) {
        return new FieldDeclaration(typeRef, name);
    }

    /**
     * Creates a new {@link FieldDeclaration}.
     *
     * @return a new instance of FieldDeclaration.
     */
    public FieldDeclaration createFieldDeclaration(ASTList<DeclarationSpecifier> mods,
            TypeReference typeRef, Identifier name, Expression init) {
        return new FieldDeclaration(mods, typeRef, name, init);
    }

    /**
     * Creates a new {@link FieldDeclaration}.
     *
     * @return a new instance of FieldDeclaration.
     */
    public FieldDeclaration createFieldDeclaration(ASTList<DeclarationSpecifier> mods,
            TypeReference typeRef, ASTList<FieldSpecification> vars) {
        return new FieldDeclaration(mods, typeRef, vars);
    }

    /**
     * Creates a new {@link Extends}.
     *
     * @return a new instance of Extends.
     */
    public Extends createExtends() {
        return new Extends();
    }

    /**
     * Creates a new {@link Extends}.
     *
     * @return a new instance of Extends.
     */
    public Extends createExtends(TypeReference supertype) {
        return new Extends(supertype);
    }

    /**
     * Creates a new {@link Extends}.
     *
     * @return a new instance of Extends.
     */
    public Extends createExtends(ASTList<TypeReference> list) {
        return new Extends(list);
    }

    /**
     * Creates a new {@link Implements}.
     *
     * @return a new instance of Implements.
     */
    public Implements createImplements() {
        return new Implements();
    }

    /**
     * Creates a new {@link Implements}.
     *
     * @return a new instance of Implements.
     */
    public Implements createImplements(TypeReference supertype) {
        return new Implements(supertype);
    }

    /**
     * Creates a new {@link Implements}.
     *
     * @return a new instance of Implements.
     */
    public Implements createImplements(ASTList<TypeReference> list) {
        return new Implements(list);
    }

    /**
     * Creates a new {@link InterfaceDeclaration}.
     *
     * @return a new instance of InterfaceDeclaration.
     */
    public InterfaceDeclaration createInterfaceDeclaration() {
        return new InterfaceDeclaration();
    }

    /**
     * Creates a new {@link InterfaceDeclaration}.
     *
     * @return a new instance of InterfaceDeclaration.
     */
    public InterfaceDeclaration createInterfaceDeclaration(ASTList<DeclarationSpecifier> modifiers,
            Identifier name, Extends extended, ASTList<MemberDeclaration> members) {
        return new InterfaceDeclaration(modifiers, name, extended, members);
    }

    public AnnotationDeclaration createAnnotationDeclaration() {
        return new AnnotationDeclaration();
    }

    public AnnotationDeclaration createAnnotationDeclaration(
            ASTList<DeclarationSpecifier> modifiers, Identifier name,
            ASTList<MemberDeclaration> members) {
        return new AnnotationDeclaration(modifiers, name, members);
    }

    /**
     * Creates a new {@link LocalVariableDeclaration}.
     *
     * @return a new instance of LocalVariableDeclaration.
     */
    public LocalVariableDeclaration createLocalVariableDeclaration() {
        return new LocalVariableDeclaration();
    }

    /**
     * Creates a new {@link LocalVariableDeclaration}.
     *
     * @return a new instance of LocalVariableDeclaration.
     */
    public LocalVariableDeclaration createLocalVariableDeclaration(TypeReference typeRef,
            Identifier name) {
        return new LocalVariableDeclaration(typeRef, name);
    }

    /**
     * Creates a new {@link LocalVariableDeclaration}.
     *
     * @return a new instance of LocalVariableDeclaration.
     */
    public LocalVariableDeclaration createLocalVariableDeclaration(
            ASTList<DeclarationSpecifier> mods, TypeReference typeRef,
            ASTList<VariableSpecification> vars) {
        return new LocalVariableDeclaration(mods, typeRef, vars);
    }

    /**
     * Creates a new {@link LocalVariableDeclaration}.
     *
     * @return a new instance of LocalVariableDeclaration.
     */
    public LocalVariableDeclaration createLocalVariableDeclaration(
            ASTList<DeclarationSpecifier> mods, TypeReference typeRef, Identifier name,
            Expression init) {
        return new LocalVariableDeclaration(mods, typeRef, name, init);
    }

    /**
     * Creates a new {@link MethodDeclaration}.
     *
     * @return a new instance of MethodDeclaration.
     */
    public MethodDeclaration createMethodDeclaration() {
        return new MethodDeclaration();
    }

    /**
     * Creates a new {@link MethodDeclaration}.
     *
     * @return a new instance of MethodDeclaration.
     */
    public MethodDeclaration createMethodDeclaration(ASTList<DeclarationSpecifier> modifiers,
            TypeReference returnType, Identifier name, ASTList<ParameterDeclaration> parameters,
            Throws exceptions) {
        return new MethodDeclaration(modifiers, returnType, name, parameters, exceptions);
    }

    /**
     * Creates a new {@link MethodDeclaration}.
     *
     * @return a new instance of MethodDeclaration.
     */
    public MethodDeclaration createMethodDeclaration(ASTList<DeclarationSpecifier> modifiers,
            TypeReference returnType, Identifier name, ASTList<ParameterDeclaration> parameters,
            Throws exceptions, StatementBlock body) {
        return new MethodDeclaration(modifiers, returnType, name, parameters, exceptions, body);
    }

    public AnnotationPropertyDeclaration createAnnotationPropertyDeclaration(
            ASTList<DeclarationSpecifier> modifiers, TypeReference returnType, Identifier name,
            Expression defaultValue) {
        return new AnnotationPropertyDeclaration(modifiers, returnType, name, defaultValue);
    }

    /**
     * Creates a new {@link ParameterDeclaration}.
     *
     * @return a new instance of ParameterDeclaration.
     */
    public ParameterDeclaration createParameterDeclaration() {
        return new ParameterDeclaration();
    }

    /**
     * Creates a new {@link ParameterDeclaration}.
     *
     * @return a new instance of ParameterDeclaration.
     */
    public ParameterDeclaration createParameterDeclaration(TypeReference typeRef, Identifier name) {
        return new ParameterDeclaration(typeRef, name);
    }

    /**
     * Creates a new {@link ParameterDeclaration}.
     *
     * @return a new instance of ParameterDeclaration.
     */
    public ParameterDeclaration createParameterDeclaration(ASTList<DeclarationSpecifier> mods,
            TypeReference typeRef, Identifier name) {
        return new ParameterDeclaration(mods, typeRef, name);
    }

    /**
     * Creates a new {@link VariableSpecification}.
     *
     * @return a new instance of VariableSpecification.
     */
    public VariableSpecification createVariableSpecification() {
        return new VariableSpecification();
    }

    /**
     * Creates a new {@link VariableSpecification}.
     *
     * @return a new instance of VariableSpecification.
     */
    public VariableSpecification createVariableSpecification(Identifier name) {
        return new VariableSpecification(name);
    }

    /**
     * Creates a new {@link VariableSpecification}.
     *
     * @return a new instance of VariableSpecification.
     */
    public VariableSpecification createVariableSpecification(Identifier name, Expression init) {
        return new VariableSpecification(name, init);
    }

    /**
     * Creates a new {@link VariableSpecification}.
     *
     * @return a new instance of VariableSpecification.
     */
    public VariableSpecification createVariableSpecification(Identifier name, int dimensions,
            Expression init) {
        return new VariableSpecification(name, dimensions, init);
    }

    /**
     * Creates a new {@link FieldSpecification}.
     *
     * @return a new instance of FieldSpecification.
     */
    public FieldSpecification createFieldSpecification() {
        return new FieldSpecification();
    }

    /**
     * Creates a new {@link FieldSpecification}.
     *
     * @return a new instance of FieldSpecification.
     */
    public FieldSpecification createFieldSpecification(Identifier name) {
        return new FieldSpecification(name);
    }

    /**
     * Creates a new {@link FieldSpecification}.
     *
     * @return a new instance of FieldSpecification.
     */
    public FieldSpecification createFieldSpecification(Identifier name, Expression init) {
        return new FieldSpecification(name, init);
    }

    /**
     * Creates a new {@link FieldSpecification}.
     *
     * @return a new instance of FieldSpecification.
     */
    public FieldSpecification createFieldSpecification(Identifier name, int dimensions,
            Expression init) {
        return new FieldSpecification(name, dimensions, init);
    }

    /**
     * Creates a new {@link ArrayInitializer}.
     *
     * @return a new instance of ArrayInitializer.
     */
    public ArrayInitializer createArrayInitializer() {
        return new ArrayInitializer();
    }

    /**
     * Creates a new {@link ArrayInitializer}.
     *
     * @return a new instance of ArrayInitializer.
     */
    public ArrayInitializer createArrayInitializer(ASTList<Expression> args) {
        return new ArrayInitializer(args);
    }

    /**
     * Creates a new {@link ParenthesizedExpression}.
     *
     * @return a new instance of ParenthesizedExpression.
     */
    public ParenthesizedExpression createParenthesizedExpression() {
        return new ParenthesizedExpression();
    }

    /**
     * Creates a new {@link ParenthesizedExpression}.
     *
     * @return a new instance of ParenthesizedExpression.
     */
    public ParenthesizedExpression createParenthesizedExpression(Expression child) {
        return new ParenthesizedExpression(child);
    }

    /**
     * Creates a new {@link BooleanLiteral}.
     *
     * @return a new instance of BooleanLiteral.
     */
    public BooleanLiteral createBooleanLiteral() {
        return new BooleanLiteral();
    }

    /**
     * Creates a new {@link BooleanLiteral}.
     *
     * @return a new instance of BooleanLiteral.
     */
    public BooleanLiteral createBooleanLiteral(boolean value) {
        return new BooleanLiteral(value);
    }

    /**
     * Creates a new {@link CharLiteral}.
     *
     * @return a new instance of CharLiteral.
     */
    public CharLiteral createCharLiteral() {
        return new CharLiteral();
    }

    /**
     * Creates a new {@link CharLiteral}.
     *
     * @return a new instance of CharLiteral.
     */
    public CharLiteral createCharLiteral(char value) {
        return new CharLiteral(value);
    }

    /**
     * Creates a new {@link CharLiteral}.
     *
     * @return a new instance of CharLiteral.
     */
    public CharLiteral createCharLiteral(String value) {
        return new CharLiteral(value);
    }

    /**
     * Creates a new {@link DoubleLiteral}.
     *
     * @return a new instance of DoubleLiteral.
     */
    public DoubleLiteral createDoubleLiteral() {
        return new DoubleLiteral();
    }

    /**
     * Creates a new {@link DoubleLiteral}.
     *
     * @return a new instance of DoubleLiteral.
     */
    public DoubleLiteral createDoubleLiteral(double value) {
        return new DoubleLiteral(value);
    }

    /**
     * Creates a new {@link DoubleLiteral}.
     *
     * @return a new instance of DoubleLiteral.
     */
    public DoubleLiteral createDoubleLiteral(String value) {
        return new DoubleLiteral(value);
    }

    /**
     * Creates a new {@link FloatLiteral}.
     *
     * @return a new instance of FloatLiteral.
     */
    public FloatLiteral createFloatLiteral() {
        return new FloatLiteral();
    }

    /**
     * Creates a new {@link FloatLiteral}.
     *
     * @return a new instance of FloatLiteral.
     */
    public FloatLiteral createFloatLiteral(float value) {
        return new FloatLiteral(value);
    }

    /**
     * Creates a new {@link FloatLiteral}.
     *
     * @return a new instance of FloatLiteral.
     */
    public FloatLiteral createFloatLiteral(String value) {
        return new FloatLiteral(value);
    }

    /**
     * Creates a new {@link IntLiteral}.
     *
     * @return a new instance of IntLiteral.
     */
    public IntLiteral createIntLiteral() {
        return new IntLiteral();
    }

    /**
     * Creates a new {@link IntLiteral}.
     *
     * @return a new instance of IntLiteral.
     */
    public IntLiteral createIntLiteral(int value) {
        return new IntLiteral(value);
    }

    /**
     * Creates a new {@link IntLiteral}.
     *
     * @return a new instance of IntLiteral.
     */
    public IntLiteral createIntLiteral(String value) {
        return new IntLiteral(value);
    }

    /**
     * Creates a new {@link LongLiteral}.
     *
     * @return a new instance of LongLiteral.
     */
    public LongLiteral createLongLiteral() {
        return new LongLiteral();
    }

    /**
     * Creates a new {@link LongLiteral}.
     *
     * @return a new instance of LongLiteral.
     */
    public LongLiteral createLongLiteral(long value) {
        return new LongLiteral(value);
    }

    /**
     * Creates a new {@link LongLiteral}.
     *
     * @return a new instance of LongLiteral.
     */
    public LongLiteral createLongLiteral(String value) {
        return new LongLiteral(value);
    }

    /**
     * Creates a new {@link NullLiteral}.
     *
     * @return a new instance of NullLiteral.
     */
    public NullLiteral createNullLiteral() {
        return new NullLiteral();
    }

    /**
     * Creates a new {@link StringLiteral}.
     *
     * @return a new instance of StringLiteral.
     */
    public StringLiteral createStringLiteral() {
        return new StringLiteral();
    }

    /**
     * Creates a new {@link StringLiteral}.
     *
     * @return a new instance of StringLiteral.
     */
    public StringLiteral createStringLiteral(String value) {
        return new StringLiteral(value);
    }

    /**
     * Creates a new {@link ArrayReference}.
     *
     * @return a new instance of ArrayReference.
     */
    public ArrayReference createArrayReference() {
        return new ArrayReference();
    }

    /**
     * Creates a new {@link ArrayReference}.
     *
     * @return a new instance of ArrayReference.
     */
    public ArrayReference createArrayReference(ReferencePrefix accessPath,
            ASTList<Expression> initializers) {
        return new ArrayReference(accessPath, initializers);
    }

    /**
     * Creates a new {@link FieldReference}.
     *
     * @return a new instance of FieldReference.
     */
    public FieldReference createFieldReference() {
        return new FieldReference();
    }

    /**
     * Creates a new {@link FieldReference}.
     *
     * @return a new instance of FieldReference.
     */
    public FieldReference createFieldReference(Identifier id) {
        return new FieldReference(id);
    }

    /**
     * Creates a new {@link FieldReference}.
     *
     * @return a new instance of FieldReference.
     */
    public FieldReference createFieldReference(ReferencePrefix prefix, Identifier id) {
        return new FieldReference(prefix, id);
    }

    /**
     * Creates a new {@link MetaClassReference}.
     *
     * @return a new instance of MetaClassReference.
     */
    public MetaClassReference createMetaClassReference() {
        return new MetaClassReference();
    }

    /**
     * Creates a new {@link MetaClassReference}.
     *
     * @return a new instance of MetaClassReference.
     */
    public MetaClassReference createMetaClassReference(TypeReference reference) {
        return new MetaClassReference(reference);
    }

    /**
     * Creates a new {@link MethodReference}.
     *
     * @return a new instance of MethodReference.
     */
    public MethodReference createMethodReference() {
        return new MethodReference();
    }

    /**
     * Creates a new {@link MethodReference}.
     *
     * @return a new instance of MethodReference.
     */
    public MethodReference createMethodReference(Identifier name) {
        return new MethodReference(name);
    }

    /**
     * Creates a new {@link MethodReference}.
     *
     * @return a new instance of MethodReference.
     */
    public MethodReference createMethodReference(ReferencePrefix accessPath, Identifier name) {
        return new MethodReference(accessPath, name);
    }

    /**
     * Creates a new {@link MethodReference}.
     *
     * @return a new instance of MethodReference.
     */
    public MethodReference createMethodReference(Identifier name, ASTList<Expression> args) {
        return new MethodReference(name, args);
    }

    /**
     * Creates a new {@link MethodReference}.
     *
     * @return a new instance of MethodReference.
     */
    public MethodReference createMethodReference(ReferencePrefix accessPath, Identifier name,
            ASTList<Expression> args) {
        return new MethodReference(accessPath, name, args);
    }

    public MethodReference createMethodReference(ReferencePrefix accessPath, Identifier name,
            ASTList<Expression> args, ASTList<TypeArgumentDeclaration> typeArgs) {
        return new MethodReference(accessPath, name, args, typeArgs);
    }

    public AnnotationPropertyReference createAnnotationPropertyReference(String id) {
        Identifier ident = new Identifier(id);
        return new AnnotationPropertyReference(ident);
    }

    public AnnotationPropertyReference createAnnotationPropertyReference(Identifier id) {
        return new AnnotationPropertyReference(id);
    }

    /**
     * Creates a new {@link SuperConstructorReference}.
     *
     * @return a new instance of SuperConstructorReference.
     */
    public SuperConstructorReference createSuperConstructorReference() {
        return new SuperConstructorReference();
    }

    /**
     * Creates a new {@link SuperConstructorReference}.
     *
     * @return a new instance of SuperConstructorReference.
     */
    public SuperConstructorReference createSuperConstructorReference(
            ASTList<Expression> arguments) {
        return new SuperConstructorReference(arguments);
    }

    /**
     * Creates a new {@link SuperConstructorReference}.
     *
     * @return a new instance of SuperConstructorReference.
     */
    public SuperConstructorReference createSuperConstructorReference(ReferencePrefix path,
            ASTList<Expression> arguments) {
        return new SuperConstructorReference(path, arguments);
    }

    /**
     * Creates a new {@link SuperReference}.
     *
     * @return a new instance of SuperReference.
     */
    public SuperReference createSuperReference() {
        return new SuperReference();
    }

    /**
     * Creates a new {@link SuperReference}.
     *
     * @return a new instance of SuperReference.
     */
    public SuperReference createSuperReference(ReferencePrefix accessPath) {
        return new SuperReference(accessPath);
    }

    /**
     * Creates a new {@link ThisConstructorReference}.
     *
     * @return a new instance of ThisConstructorReference.
     */
    public ThisConstructorReference createThisConstructorReference() {
        return new ThisConstructorReference();
    }

    /**
     * Creates a new {@link ThisConstructorReference}.
     *
     * @return a new instance of ThisConstructorReference.
     */
    public ThisConstructorReference createThisConstructorReference(ASTList<Expression> arguments) {
        return new ThisConstructorReference(arguments);
    }

    /**
     * Creates a new {@link ThisReference}.
     *
     * @return a new instance of ThisReference.
     */
    public ThisReference createThisReference() {
        return new ThisReference();
    }

    /**
     * Creates a new {@link ThisReference}.
     *
     * @return a new instance of ThisReference.
     */
    public ThisReference createThisReference(TypeReference outer) {
        return new ThisReference(outer);
    }

    /**
     * Creates a new {@link VariableReference}.
     *
     * @return a new instance of VariableReference.
     */
    public VariableReference createVariableReference() {
        return new VariableReference();
    }

    /**
     * Creates a new {@link VariableReference}.
     *
     * @return a new instance of VariableReference.
     */
    public VariableReference createVariableReference(Identifier id) {
        return new VariableReference(id);
    }

    /**
     * Creates a new {@link ArrayLengthReference}.
     *
     * @return a new instance of ArrayLengthReference.
     */
    public ArrayLengthReference createArrayLengthReference() {
        return new ArrayLengthReference();
    }

    /**
     * Creates a new {@link ArrayLengthReference}.
     *
     * @return a new instance of ArrayLengthReference.
     */
    public ArrayLengthReference createArrayLengthReference(ReferencePrefix prefix) {
        return new ArrayLengthReference(prefix);
    }

    /**
     * Creates a new {@link BinaryAnd}.
     *
     * @return a new instance of BinaryAnd.
     */
    public BinaryAnd createBinaryAnd() {
        return new BinaryAnd();
    }

    /**
     * Creates a new {@link BinaryAnd}.
     *
     * @return a new instance of BinaryAnd.
     */
    public BinaryAnd createBinaryAnd(Expression lhs, Expression rhs) {
        return new BinaryAnd(lhs, rhs);
    }

    /**
     * Creates a new {@link BinaryAndAssignment}.
     *
     * @return a new instance of BinaryAndAssignment.
     */
    public BinaryAndAssignment createBinaryAndAssignment() {
        return new BinaryAndAssignment();
    }

    /**
     * Creates a new {@link BinaryAndAssignment}.
     *
     * @return a new instance of BinaryAndAssignment.
     */
    public BinaryAndAssignment createBinaryAndAssignment(Expression lhs, Expression rhs) {
        return new BinaryAndAssignment(lhs, rhs);
    }

    /**
     * Creates a new {@link BinaryNot}.
     *
     * @return a new instance of BinaryNot.
     */
    public BinaryNot createBinaryNot() {
        return new BinaryNot();
    }

    /**
     * Creates a new {@link BinaryNot}.
     *
     * @return a new instance of BinaryNot.
     */
    public BinaryNot createBinaryNot(Expression child) {
        return new BinaryNot(child);
    }

    /**
     * Creates a new {@link BinaryOr}.
     *
     * @return a new instance of BinaryOr.
     */
    public BinaryOr createBinaryOr() {
        return new BinaryOr();
    }

    /**
     * Creates a new {@link BinaryOr}.
     *
     * @return a new instance of BinaryOr.
     */
    public BinaryOr createBinaryOr(Expression lhs, Expression rhs) {
        return new BinaryOr(lhs, rhs);
    }

    /**
     * Creates a new {@link BinaryOrAssignment}.
     *
     * @return a new instance of BinaryOrAssignment.
     */
    public BinaryOrAssignment createBinaryOrAssignment() {
        return new BinaryOrAssignment();
    }

    /**
     * Creates a new {@link BinaryOrAssignment}.
     *
     * @return a new instance of BinaryOrAssignment.
     */
    public BinaryOrAssignment createBinaryOrAssignment(Expression lhs, Expression rhs) {
        return new BinaryOrAssignment(lhs, rhs);
    }

    /**
     * Creates a new {@link BinaryXOr}.
     *
     * @return a new instance of BinaryXOr.
     */
    public BinaryXOr createBinaryXOr() {
        return new BinaryXOr();
    }

    /**
     * Creates a new {@link BinaryXOr}.
     *
     * @return a new instance of BinaryXOr.
     */
    public BinaryXOr createBinaryXOr(Expression lhs, Expression rhs) {
        return new BinaryXOr(lhs, rhs);
    }

    /**
     * Creates a new {@link BinaryXOrAssignment}.
     *
     * @return a new instance of BinaryXOrAssignment.
     */
    public BinaryXOrAssignment createBinaryXOrAssignment() {
        return new BinaryXOrAssignment();
    }

    /**
     * Creates a new {@link BinaryXOrAssignment}.
     *
     * @return a new instance of BinaryXOrAssignment.
     */
    public BinaryXOrAssignment createBinaryXOrAssignment(Expression lhs, Expression rhs) {
        return new BinaryXOrAssignment(lhs, rhs);
    }

    /**
     * Creates a new {@link Conditional}.
     *
     * @return a new instance of Conditional.
     */
    public Conditional createConditional() {
        return new Conditional();
    }

    /**
     * Creates a new {@link Conditional}.
     *
     * @return a new instance of Conditional.
     */
    public Conditional createConditional(Expression guard, Expression thenExpr,
            Expression elseExpr) {
        return new Conditional(guard, thenExpr, elseExpr);
    }

    /**
     * Creates a new {@link CopyAssignment}.
     *
     * @return a new instance of CopyAssignment.
     */
    public CopyAssignment createCopyAssignment() {
        return new CopyAssignment();
    }

    /**
     * Creates a new {@link CopyAssignment}.
     *
     * @return a new instance of CopyAssignment.
     */
    public CopyAssignment createCopyAssignment(Expression lhs, Expression rhs) {
        return new CopyAssignment(lhs, rhs);
    }

    /**
     * Creates a new {@link Divide}.
     *
     * @return a new instance of Divide.
     */
    public Divide createDivide() {
        return new Divide();
    }

    /**
     * Creates a new {@link Divide}.
     *
     * @return a new instance of Divide.
     */
    public Divide createDivide(Expression lhs, Expression rhs) {
        return new Divide(lhs, rhs);
    }

    /**
     * Creates a new {@link DivideAssignment}.
     *
     * @return a new instance of DivideAssignment.
     */
    public DivideAssignment createDivideAssignment() {
        return new DivideAssignment();
    }

    /**
     * Creates a new {@link DivideAssignment}.
     *
     * @return a new instance of DivideAssignment.
     */
    public DivideAssignment createDivideAssignment(Expression lhs, Expression rhs) {
        return new DivideAssignment(lhs, rhs);
    }

    /**
     * Creates a new {@link Equals}.
     *
     * @return a new instance of Equals.
     */
    public Equals createEquals() {
        return new Equals();
    }

    /**
     * Creates a new {@link Equals}.
     *
     * @return a new instance of Equals.
     */
    public Equals createEquals(Expression lhs, Expression rhs) {
        return new Equals(lhs, rhs);
    }

    /**
     * Creates a new {@link GreaterOrEquals}.
     *
     * @return a new instance of GreaterOrEquals.
     */
    public GreaterOrEquals createGreaterOrEquals() {
        return new GreaterOrEquals();
    }

    /**
     * Creates a new {@link GreaterOrEquals}.
     *
     * @return a new instance of GreaterOrEquals.
     */
    public GreaterOrEquals createGreaterOrEquals(Expression lhs, Expression rhs) {
        return new GreaterOrEquals(lhs, rhs);
    }

    /**
     * Creates a new {@link GreaterThan}.
     *
     * @return a new instance of GreaterThan.
     */
    public GreaterThan createGreaterThan() {
        return new GreaterThan();
    }

    /**
     * Creates a new {@link GreaterThan}.
     *
     * @return a new instance of GreaterThan.
     */
    public GreaterThan createGreaterThan(Expression lhs, Expression rhs) {
        return new GreaterThan(lhs, rhs);
    }

    /**
     * Creates a new {@link Instanceof}.
     *
     * @return a new instance of Instanceof.
     */
    public Instanceof createInstanceof() {
        return new Instanceof();
    }

    /**
     * Creates a new {@link Instanceof}.
     *
     * @return a new instance of Instanceof.
     */
    public Instanceof createInstanceof(Expression child, TypeReference typeref) {
        return new Instanceof(child, typeref);
    }

    /**
     * Creates a new {@link LessOrEquals}.
     *
     * @return a new instance of LessOrEquals.
     */
    public LessOrEquals createLessOrEquals() {
        return new LessOrEquals();
    }

    /**
     * Creates a new {@link LessOrEquals}.
     *
     * @return a new instance of LessOrEquals.
     */
    public LessOrEquals createLessOrEquals(Expression lhs, Expression rhs) {
        return new LessOrEquals(lhs, rhs);
    }

    /**
     * Creates a new {@link LessThan}.
     *
     * @return a new instance of LessThan.
     */
    public LessThan createLessThan() {
        return new LessThan();
    }

    /**
     * Creates a new {@link LessThan}.
     *
     * @return a new instance of LessThan.
     */
    public LessThan createLessThan(Expression lhs, Expression rhs) {
        return new LessThan(lhs, rhs);
    }

    /**
     * Creates a new {@link LogicalAnd}.
     *
     * @return a new instance of LogicalAnd.
     */
    public LogicalAnd createLogicalAnd() {
        return new LogicalAnd();
    }

    /**
     * Creates a new {@link LogicalAnd}.
     *
     * @return a new instance of LogicalAnd.
     */
    public LogicalAnd createLogicalAnd(Expression lhs, Expression rhs) {
        return new LogicalAnd(lhs, rhs);
    }

    /**
     * Creates a new {@link LogicalNot}.
     *
     * @return a new instance of LogicalNot.
     */
    public LogicalNot createLogicalNot() {
        return new LogicalNot();
    }

    /**
     * Creates a new {@link LogicalNot}.
     *
     * @return a new instance of LogicalNot.
     */
    public LogicalNot createLogicalNot(Expression child) {
        return new LogicalNot(child);
    }

    /**
     * Creates a new {@link LogicalOr}.
     *
     * @return a new instance of LogicalOr.
     */
    public LogicalOr createLogicalOr() {
        return new LogicalOr();
    }

    /**
     * Creates a new {@link LogicalOr}.
     *
     * @return a new instance of LogicalOr.
     */
    public LogicalOr createLogicalOr(Expression lhs, Expression rhs) {
        return new LogicalOr(lhs, rhs);
    }

    /**
     * Creates a new {@link Minus}.
     *
     * @return a new instance of Minus.
     */
    public Minus createMinus() {
        return new Minus();
    }

    /**
     * Creates a new {@link Minus}.
     *
     * @return a new instance of Minus.
     */
    public Minus createMinus(Expression lhs, Expression rhs) {
        return new Minus(lhs, rhs);
    }

    /**
     * Creates a new {@link MinusAssignment}.
     *
     * @return a new instance of MinusAssignment.
     */
    public MinusAssignment createMinusAssignment() {
        return new MinusAssignment();
    }

    /**
     * Creates a new {@link MinusAssignment}.
     *
     * @return a new instance of MinusAssignment.
     */
    public MinusAssignment createMinusAssignment(Expression lhs, Expression rhs) {
        return new MinusAssignment(lhs, rhs);
    }

    /**
     * Creates a new {@link Modulo}.
     *
     * @return a new instance of Modulo.
     */
    public Modulo createModulo() {
        return new Modulo();
    }

    /**
     * Creates a new {@link Modulo}.
     *
     * @return a new instance of Modulo.
     */
    public Modulo createModulo(Expression lhs, Expression rhs) {
        return new Modulo(lhs, rhs);
    }

    /**
     * Creates a new {@link ModuloAssignment}.
     *
     * @return a new instance of ModuloAssignment.
     */
    public ModuloAssignment createModuloAssignment() {
        return new ModuloAssignment();
    }

    /**
     * Creates a new {@link ModuloAssignment}.
     *
     * @return a new instance of ModuloAssignment.
     */
    public ModuloAssignment createModuloAssignment(Expression lhs, Expression rhs) {
        return new ModuloAssignment(lhs, rhs);
    }

    /**
     * Creates a new {@link Negative}.
     *
     * @return a new instance of Negative.
     */
    public Negative createNegative() {
        return new Negative();
    }

    /**
     * Creates a new {@link Negative}.
     *
     * @return a new instance of Negative.
     */
    public Negative createNegative(Expression child) {
        return new Negative(child);
    }

    /**
     * Creates a new {@link New}.
     *
     * @return a new instance of New.
     */
    public New createNew() {
        return new New();
    }

    /**
     * Creates a new {@link New}.
     *
     * @return a new instance of New.
     */
    public New createNew(ReferencePrefix accessPath, TypeReference constructorName,
            ASTList<Expression> arguments) {
        return new New(accessPath, constructorName, arguments);
    }

    /**
     * Creates a new {@link New}.
     *
     * @return a new instance of New.
     */
    public New createNew(ReferencePrefix accessPath, TypeReference constructorName,
            ASTList<Expression> arguments, ClassDeclaration anonymousClass) {
        return new New(accessPath, constructorName, arguments, anonymousClass);
    }

    /**
     * Creates a new {@link NewArray}.
     *
     * @return a new instance of NewArray.
     */
    public NewArray createNewArray() {
        return new NewArray();
    }

    /**
     * Creates a new {@link NewArray}.
     *
     * @return a new instance of NewArray.
     */
    public NewArray createNewArray(TypeReference arrayName, ASTList<Expression> dimExpr) {
        return new NewArray(arrayName, dimExpr);
    }

    /**
     * Creates a new {@link NewArray}.
     *
     * @return a new instance of NewArray.
     */
    public NewArray createNewArray(TypeReference arrayName, int dimensions,
            ArrayInitializer initializer) {
        return new NewArray(arrayName, dimensions, initializer);
    }

    /**
     * Creates a new {@link NotEquals}.
     *
     * @return a new instance of NotEquals.
     */
    public NotEquals createNotEquals() {
        return new NotEquals();
    }

    /**
     * Creates a new {@link NotEquals}.
     *
     * @return a new instance of NotEquals.
     */
    public NotEquals createNotEquals(Expression lhs, Expression rhs) {
        return new NotEquals(lhs, rhs);
    }

    /**
     * Creates a new {@link Plus}.
     *
     * @return a new instance of Plus.
     */
    public Plus createPlus() {
        return new Plus();
    }

    /**
     * Creates a new {@link Plus}.
     *
     * @return a new instance of Plus.
     */
    public Plus createPlus(Expression lhs, Expression rhs) {
        return new Plus(lhs, rhs);
    }

    /**
     * Creates a new {@link PlusAssignment}.
     *
     * @return a new instance of PlusAssignment.
     */
    public PlusAssignment createPlusAssignment() {
        return new PlusAssignment();
    }

    /**
     * Creates a new {@link PlusAssignment}.
     *
     * @return a new instance of PlusAssignment.
     */
    public PlusAssignment createPlusAssignment(Expression lhs, Expression rhs) {
        return new PlusAssignment(lhs, rhs);
    }

    /**
     * Creates a new {@link Positive}.
     *
     * @return a new instance of Positive.
     */
    public Positive createPositive() {
        return new Positive();
    }

    /**
     * Creates a new {@link Positive}.
     *
     * @return a new instance of Positive.
     */
    public Positive createPositive(Expression child) {
        return new Positive(child);
    }

    /**
     * Creates a new {@link PostDecrement}.
     *
     * @return a new instance of PostDecrement.
     */
    public PostDecrement createPostDecrement() {
        return new PostDecrement();
    }

    /**
     * Creates a new {@link PostDecrement}.
     *
     * @return a new instance of PostDecrement.
     */
    public PostDecrement createPostDecrement(Expression child) {
        return new PostDecrement(child);
    }

    /**
     * Creates a new {@link PostIncrement}.
     *
     * @return a new instance of PostIncrement.
     */
    public PostIncrement createPostIncrement() {
        return new PostIncrement();
    }

    /**
     * Creates a new {@link PostIncrement}.
     *
     * @return a new instance of PostIncrement.
     */
    public PostIncrement createPostIncrement(Expression child) {
        return new PostIncrement(child);
    }

    /**
     * Creates a new {@link PreDecrement}.
     *
     * @return a new instance of PreDecrement.
     */
    public PreDecrement createPreDecrement() {
        return new PreDecrement();
    }

    /**
     * Creates a new {@link PreDecrement}.
     *
     * @return a new instance of PreDecrement.
     */
    public PreDecrement createPreDecrement(Expression child) {
        return new PreDecrement(child);
    }

    /**
     * Creates a new {@link PreIncrement}.
     *
     * @return a new instance of PreIncrement.
     */
    public PreIncrement createPreIncrement() {
        return new PreIncrement();
    }

    /**
     * Creates a new {@link PreIncrement}.
     *
     * @return a new instance of PreIncrement.
     */
    public PreIncrement createPreIncrement(Expression child) {
        return new PreIncrement(child);
    }

    /**
     * Creates a new {@link ShiftLeft}.
     *
     * @return a new instance of ShiftLeft.
     */
    public ShiftLeft createShiftLeft() {
        return new ShiftLeft();
    }

    /**
     * Creates a new {@link ShiftLeft}.
     *
     * @return a new instance of ShiftLeft.
     */
    public ShiftLeft createShiftLeft(Expression lhs, Expression rhs) {
        return new ShiftLeft(lhs, rhs);
    }

    /**
     * Creates a new {@link ShiftLeftAssignment}.
     *
     * @return a new instance of ShiftLeftAssignment.
     */
    public ShiftLeftAssignment createShiftLeftAssignment() {
        return new ShiftLeftAssignment();
    }

    /**
     * Creates a new {@link ShiftLeftAssignment}.
     *
     * @return a new instance of ShiftLeftAssignment.
     */
    public ShiftLeftAssignment createShiftLeftAssignment(Expression lhs, Expression rhs) {
        return new ShiftLeftAssignment(lhs, rhs);
    }

    /**
     * Creates a new {@link ShiftRight}.
     *
     * @return a new instance of ShiftRight.
     */
    public ShiftRight createShiftRight() {
        return new ShiftRight();
    }

    /**
     * Creates a new {@link ShiftRight}.
     *
     * @return a new instance of ShiftRight.
     */
    public ShiftRight createShiftRight(Expression lhs, Expression rhs) {
        return new ShiftRight(lhs, rhs);
    }

    /**
     * Creates a new {@link ShiftRightAssignment}.
     *
     * @return a new instance of ShiftRightAssignment.
     */
    public ShiftRightAssignment createShiftRightAssignment() {
        return new ShiftRightAssignment();
    }

    /**
     * Creates a new {@link ShiftRightAssignment}.
     *
     * @return a new instance of ShiftRightAssignment.
     */
    public ShiftRightAssignment createShiftRightAssignment(Expression lhs, Expression rhs) {
        return new ShiftRightAssignment(lhs, rhs);
    }

    /**
     * Creates a new {@link Times}.
     *
     * @return a new instance of Times.
     */
    public Times createTimes() {
        return new Times();
    }

    /**
     * Creates a new {@link Times}.
     *
     * @return a new instance of Times.
     */
    public Times createTimes(Expression lhs, Expression rhs) {
        return new Times(lhs, rhs);
    }

    /**
     * Creates a new {@link TimesAssignment}.
     *
     * @return a new instance of TimesAssignment.
     */
    public TimesAssignment createTimesAssignment() {
        return new TimesAssignment();
    }

    /**
     * Creates a new {@link TimesAssignment}.
     *
     * @return a new instance of TimesAssignment.
     */
    public TimesAssignment createTimesAssignment(Expression lhs, Expression rhs) {
        return new TimesAssignment(lhs, rhs);
    }

    /**
     * Creates a new {@link TypeCast}.
     *
     * @return a new instance of TypeCast.
     */
    public TypeCast createTypeCast() {
        return new TypeCast();
    }

    /**
     * Creates a new {@link TypeCast}.
     *
     * @return a new instance of TypeCast.
     */
    public TypeCast createTypeCast(Expression child, TypeReference typeref) {
        return new TypeCast(child, typeref);
    }

    /**
     * Creates a new {@link UnsignedShiftRight}.
     *
     * @return a new instance of UnsignedShiftRight.
     */
    public UnsignedShiftRight createUnsignedShiftRight() {
        return new UnsignedShiftRight();
    }

    /**
     * Creates a new {@link UnsignedShiftRight}.
     *
     * @return a new instance of UnsignedShiftRight.
     */
    public UnsignedShiftRight createUnsignedShiftRight(Expression lhs, Expression rhs) {
        return new UnsignedShiftRight(lhs, rhs);
    }

    /**
     * Creates a new {@link UnsignedShiftRightAssignment}.
     *
     * @return a new instance of UnsignedShiftRightAssignment.
     */
    public UnsignedShiftRightAssignment createUnsignedShiftRightAssignment() {
        return new UnsignedShiftRightAssignment();
    }

    /**
     * Creates a new {@link UnsignedShiftRightAssignment}.
     *
     * @return a new instance of UnsignedShiftRightAssignment.
     */
    public UnsignedShiftRightAssignment createUnsignedShiftRightAssignment(Expression lhs,
            Expression rhs) {
        return new UnsignedShiftRightAssignment(lhs, rhs);
    }

    /**
     * Creates a new {@link Abstract}.
     *
     * @return a new instance of Abstract.
     */
    public Abstract createAbstract() {
        return new Abstract();
    }

    /**
     * Creates a new {@link Final}.
     *
     * @return a new instance of Final.
     */
    public Final createFinal() {
        return new Final();
    }

    /**
     * Creates a new {@link Native}.
     *
     * @return a new instance of Native.
     */
    public Native createNative() {
        return new Native();
    }

    /**
     * Creates a new {@link Private}.
     *
     * @return a new instance of Private.
     */
    public Private createPrivate() {
        return new Private();
    }

    /**
     * Creates a new {@link Protected}.
     *
     * @return a new instance of Protected.
     */
    public Protected createProtected() {
        return new Protected();
    }

    /**
     * Creates a new {@link Public}.
     *
     * @return a new instance of Public.
     */
    public Public createPublic() {
        return new Public();
    }

    /**
     * Creates a new {@link Static}.
     *
     * @return a new instance of Static.
     */
    public Static createStatic() {
        return new Static();
    }

    /**
     * Creates a new {@link Synchronized}.
     *
     * @return a new instance of Synchronized.
     */
    public Synchronized createSynchronized() {
        return new Synchronized();
    }

    /**
     * Creates a new {@link Transient}.
     *
     * @return a new instance of Transient.
     */
    public Transient createTransient() {
        return new Transient();
    }

    /**
     * Creates a new {@link StrictFp}.
     *
     * @return a new instance of StrictFp.
     */
    public StrictFp createStrictFp() {
        return new StrictFp();
    }

    /**
     * Creates a new {@link Volatile}.
     *
     * @return a new instance of Volatile.
     */
    public Volatile createVolatile() {
        return new Volatile();
    }

    public AnnotationUseSpecification createAnnotationUseSpecification() {
        return new AnnotationUseSpecification();
    }

    /**
     * Creates a new {@link Break}.
     *
     * @return a new instance of Break.
     */
    public Break createBreak() {
        return new Break();
    }

    /**
     * Creates a new {@link Break}.
     *
     * @return a new instance of Break.
     */
    public Break createBreak(Identifier label) {
        return new Break(label);
    }

    /**
     * Creates a new {@link Case}.
     *
     * @return a new instance of Case.
     */
    public Case createCase() {
        return new Case();
    }

    /**
     * Creates a new {@link Case}.
     *
     * @return a new instance of Case.
     */
    public Case createCase(Expression e) {
        return new Case(e);
    }

    /**
     * Creates a new {@link Case}.
     *
     * @return a new instance of Case.
     */
    public Case createCase(Expression e, ASTList<Statement> body) {
        return new Case(e, body);
    }

    /**
     * Creates a new {@link Catch}.
     *
     * @return a new instance of Catch.
     */
    public Catch createCatch() {
        return new Catch();
    }

    /**
     * Creates a new {@link Catch}.
     *
     * @return a new instance of Catch.
     */
    public Catch createCatch(ParameterDeclaration e, StatementBlock body) {
        return new Catch(e, body);
    }

    /**
     * Creates a new {@link Continue}.
     *
     * @return a new instance of Continue.
     */
    public Continue createContinue() {
        return new Continue();
    }

    /**
     * Creates a new {@link Continue}.
     *
     * @return a new instance of Continue.
     */
    public Continue createContinue(Identifier label) {
        return new Continue(label);
    }

    /**
     * Creates a new {@link Default}.
     *
     * @return a new instance of Default.
     */
    public Default createDefault() {
        return new Default();
    }

    /**
     * Creates a new {@link Default}.
     *
     * @return a new instance of Default.
     */
    public Default createDefault(ASTList<Statement> body) {
        return new Default(body);
    }

    /**
     * Creates a new {@link Do}.
     *
     * @return a new instance of Do.
     */
    public Do createDo() {
        return new Do();
    }

    /**
     * Creates a new {@link Do}.
     *
     * @return a new instance of Do.
     */
    public Do createDo(Expression guard) {
        return new Do(guard);
    }

    /**
     * Creates a new {@link Do}.
     *
     * @return a new instance of Do.
     */
    public Do createDo(Expression guard, Statement body) {
        return new Do(guard, body);
    }

    /**
     * Creates a new {@link Else}.
     *
     * @return a new instance of Else.
     */
    public Else createElse() {
        return new Else();
    }

    /**
     * Creates a new {@link Else}.
     *
     * @return a new instance of Else.
     */
    public Else createElse(Statement body) {
        return new Else(body);
    }

    /**
     * Creates a new {@link EmptyStatement}.
     *
     * @return a new instance of EmptyStatement.
     */
    public EmptyStatement createEmptyStatement() {
        return new EmptyStatement();
    }

    /**
     * Creates a new {@link Finally}.
     *
     * @return a new instance of Finally.
     */
    public Finally createFinally() {
        return new Finally();
    }

    /**
     * Creates a new {@link Finally}.
     *
     * @return a new instance of Finally.
     */
    public Finally createFinally(StatementBlock body) {
        return new Finally(body);
    }

    /**
     * Creates a new {@link For}.
     *
     * @return a new instance of For.
     */
    public For createFor() {
        return new For();
    }

    /**
     * Creates a new {@link For}.
     *
     * @return a new instance of For.
     */
    public For createFor(ASTList<LoopInitializer> inits, Expression guard,
            ASTList<Expression> updates, Statement body) {
        return new For(inits, guard, updates, body);
    }

    public EnhancedFor createEnhancedFor() {
        return new EnhancedFor();
    }

    /**
     * Creates a new {@link Assert}.
     *
     * @return a new instance of Assert.
     */
    public Assert createAssert() {
        return new Assert();
    }

    /**
     * Creates a new {@link Assert}.
     *
     * @return a new instance of Assert.
     */
    public Assert createAssert(Expression cond) {
        return new Assert(cond);
    }

    /**
     * Creates a new {@link Assert}.
     *
     * @return a new instance of Assert.
     */
    public Assert createAssert(Expression cond, Expression msg) {
        return new Assert(cond, msg);
    }

    /**
     * Creates a new {@link If}.
     *
     * @return a new instance of If.
     */
    public If createIf() {
        return new If();
    }

    /**
     * Creates a new {@link If}.
     *
     * @return a new instance of If.
     */
    public If createIf(Expression e, Statement thenStatement) {
        return new If(e, thenStatement);
    }

    /**
     * Creates a new {@link If}.
     *
     * @return a new instance of If.
     */
    public If createIf(Expression e, Then thenBranch) {
        return new If(e, thenBranch);
    }

    /**
     * Creates a new {@link If}.
     *
     * @return a new instance of If.
     */
    public If createIf(Expression e, Then thenBranch, Else elseBranch) {
        return new If(e, thenBranch, elseBranch);
    }

    /**
     * Creates a new {@link If}.
     *
     * @return a new instance of If.
     */
    public If createIf(Expression e, Statement thenStatement, Statement elseStatement) {
        return new If(e, thenStatement, elseStatement);
    }

    /**
     * Creates a new {@link LabeledStatement}.
     *
     * @return a new instance of LabeledStatement.
     */
    public LabeledStatement createLabeledStatement() {
        return new LabeledStatement();
    }

    /**
     * Creates a new {@link LabeledStatement}.
     *
     * @return a new instance of LabeledStatement.
     */
    public LabeledStatement createLabeledStatement(Identifier id) {
        return new LabeledStatement(id);
    }

    /**
     * Creates a new {@link LabeledStatement}.
     *
     * @return a new instance of LabeledStatement.
     */
    public LabeledStatement createLabeledStatement(Identifier id, Statement statement) {
        return new LabeledStatement(id, statement);
    }

    /**
     * Creates a new {@link Return}.
     *
     * @return a new instance of Return.
     */
    public Return createReturn() {
        return new Return();
    }

    /**
     * Creates a new {@link Return}.
     *
     * @return a new instance of Return.
     */
    public Return createReturn(Expression expr) {
        return new Return(expr);
    }

    /**
     * Creates a new {@link StatementBlock}.
     *
     * @return a new instance of StatementBlock.
     */
    public StatementBlock createStatementBlock() {
        return new StatementBlock();
    }

    /**
     * Creates a new {@link StatementBlock}.
     *
     * @return a new instance of StatementBlock.
     */
    public StatementBlock createStatementBlock(ASTList<Statement> block) {
        return new StatementBlock(block);
    }

    /**
     * Creates a new {@link Switch}.
     *
     * @return a new instance of Switch.
     */
    public Switch createSwitch() {
        return new Switch();
    }

    /**
     * Creates a new {@link Switch}.
     *
     * @return a new instance of Switch.
     */
    public Switch createSwitch(Expression e) {
        return new Switch(e);
    }

    /**
     * Creates a new {@link Switch}.
     *
     * @return a new instance of Switch.
     */
    public Switch createSwitch(Expression e, ASTList<Branch> branches) {
        return new Switch(e, branches);
    }

    /**
     * Creates a new {@link SynchronizedBlock}.
     *
     * @return a new instance of SynchronizedBlock.
     */
    public SynchronizedBlock createSynchronizedBlock() {
        return new SynchronizedBlock();
    }

    /**
     * Creates a new {@link SynchronizedBlock}.
     *
     * @return a new instance of SynchronizedBlock.
     */
    public SynchronizedBlock createSynchronizedBlock(StatementBlock body) {
        return new SynchronizedBlock(body);
    }

    /**
     * Creates a new {@link SynchronizedBlock}.
     *
     * @return a new instance of SynchronizedBlock.
     */
    public SynchronizedBlock createSynchronizedBlock(Expression e, StatementBlock body) {
        return new SynchronizedBlock(e, body);
    }

    /**
     * Creates a new {@link Then}.
     *
     * @return a new instance of Then.
     */
    public Then createThen() {
        return new Then();
    }

    /**
     * Creates a new {@link Then}.
     *
     * @return a new instance of Then.
     */
    public Then createThen(Statement body) {
        return new Then(body);
    }

    /**
     * Creates a new {@link Throw}.
     *
     * @return a new instance of Throw.
     */
    public Throw createThrow() {
        return new Throw();
    }

    /**
     * Creates a new {@link Throw}.
     *
     * @return a new instance of Throw.
     */
    public Throw createThrow(Expression expr) {
        return new Throw(expr);
    }

    /**
     * Creates a new {@link Try}.
     *
     * @return a new instance of Try.
     */
    public Try createTry() {
        return new Try();
    }

    /**
     * Creates a new {@link Try}.
     *
     * @return a new instance of Try.
     */
    public Try createTry(StatementBlock body) {
        return new Try(body);
    }

    /**
     * Creates a new {@link Try}.
     *
     * @return a new instance of Try.
     */
    public Try createTry(StatementBlock body, ASTList<Branch> branches) {
        return new Try(body, branches);
    }

    /**
     * Creates a new {@link While}.
     *
     * @return a new instance of While.
     */
    public While createWhile() {
        return new While();
    }

    /**
     * Creates a new {@link While}.
     *
     * @return a new instance of While.
     */
    public While createWhile(Expression guard) {
        return new While(guard);
    }

    /**
     * Creates a new {@link While}.
     *
     * @return a new instance of While.
     */
    public While createWhile(Expression guard, Statement body) {
        return new While(guard, body);
    }

    private static class AddNewlineReader extends Reader {
        private final Reader reader;
        private boolean added = false;

        AddNewlineReader(Reader reader) {
            this.reader = reader;
        }

        @Override
        public void mark(int readAheadLimit) throws IOException {
            reader.mark(readAheadLimit);
        }

        @Override
        public boolean markSupported() {
            return reader.markSupported();
        }

        @Override
        public int read() throws IOException {
            return reader.read();
        }

        @Override
        public int read(char[] cbuf) throws IOException {
            return reader.read(cbuf);
        }

        @Override
        public int read(CharBuffer target) throws IOException {
            return reader.read(target);
        }

        @Override
        public boolean ready() throws IOException {
            return reader.ready();
        }

        @Override
        public void reset() throws IOException {
            reader.reset();
        }

        @Override
        public long skip(long n) throws IOException {
            return reader.skip(n);
        }

        @Override
        public void close() throws IOException {
            reader.close();
        }

        @Override
        public int read(char[] cbuf, int off, int len) throws IOException {
            if (added) {
                return -1;
            }
            int result = reader.read(cbuf, off, len);
            if (!added && result < len) {
                if (result == -1) {
                    result++;
                }
                cbuf[off + result++] = '\n';
                added = true;
            }
            return result;
        }
    }
}
