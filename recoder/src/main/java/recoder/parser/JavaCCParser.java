/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.parser;

import java.io.Reader;
import java.util.ArrayList;
import java.util.List;

import recoder.abstraction.TypeArgument.WildcardMode;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.Final;
import recoder.java.declaration.modifier.Static;
import recoder.java.expression.*;
import recoder.java.expression.literal.BooleanLiteral;
import recoder.java.expression.literal.NullLiteral;
import recoder.java.expression.literal.StringLiteral;
import recoder.java.expression.operator.*;
import recoder.java.reference.*;
import recoder.java.statement.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;


/**
 * JavaCC AST generation specification based on the original Java1.1 grammar that comes with javacc,
 * and includes the modification of D. Williams to accept the Java 1.2 strictfp modifier. Several
 * patches have been added to allow semicola after member declarations.
 *
 * @author RN
 * @author AL
 * @author Tobias Gutzmann
 */
public class JavaCCParser implements JavaCCParserConstants {

    static final private int[] jj_la1 = new int[173];
    static final private JJCalls[] jj_2_rtns = new JJCalls[62];
    static final private LookaheadSuccess jj_ls = new LookaheadSuccess();
    /**
     * the JavaProgramFactory instance that is used to create parse results
     */
    private static final JavaProgramFactory factory = JavaProgramFactory.getInstance();
    /**
     * all comments in a global list.
     */
    private static final List<Comment> comments = new ArrayList<>();
    /**
     * reuseable position object.
     */
    private static final SourceElement.Position position = new SourceElement.Position(0, 0);
    static private final java.util.Vector jj_expentries = new java.util.Vector();
    static private final int[] jj_lasttokens = new int[100];
    static public JavaCCParserTokenManager token_source;
    static public Token token, jj_nt;
    static public boolean lookingAhead = false;
    static boolean superAllowed = true;
    static boolean jdk1_4 = false;
    static boolean jdk1_5 = false;
    /**
     * return value containers for primary expression. need only be allocated once per parser.
     */
    static PrimarySuffixReturnValue suffix = new PrimarySuffixReturnValue();
    static PrimaryPrefixReturnValue prefix = new PrimaryPrefixReturnValue();
    static JavaCharStream jj_input_stream;
    /**
     * temporary valid variable that is used to return an additional argument from parser method
     * VariableDeclaratorId, since such an id may have a dimension
     */
    private static int tmpDimension;
    /**
     * current token, follows the next links when necessary
     */
    private static Token current;
    static private boolean jj_initialized_once = false;
    static private int jj_ntk;
    static private Token jj_scanpos, jj_lastpos;
    static private int jj_la;
    static private boolean jj_semLA;
    static private int jj_gen;
    static private int[] jj_la1_0;
    static private int[] jj_la1_1;
    static private int[] jj_la1_2;
    static private int[] jj_la1_3;
    static private boolean jj_rescan = false;
    static private int jj_gc = 0;
    static private int[] jj_expentry;
    static private int jj_kind = -1;
    static private int jj_endpos;

    static {
        jj_la1_0();
        jj_la1_1();
        jj_la1_2();
        jj_la1_3();
    }

    public JavaCCParser(java.io.InputStream stream) {
        this(stream, null);
    }

    public JavaCCParser(java.io.InputStream stream, String encoding) {
        if (jj_initialized_once) {
            System.out.println("ERROR: Second call to constructor of static parser.  You must");
            System.out
                    .println("       either use ReInit() or set the JavaCC option STATIC to false");
            System.out.println("       during parser generation.");
            throw new Error();
        }
        jj_initialized_once = true;
        try {
            jj_input_stream = new JavaCharStream(stream, encoding, 1, 1);
        } catch (java.io.UnsupportedEncodingException e) {
            throw new RuntimeException(e);
        }
        token_source = new JavaCCParserTokenManager(jj_input_stream);
        token = new Token();
        jj_ntk = -1;
        jj_gen = 0;
        for (int i = 0; i < 173; i++) {
            jj_la1[i] = -1;
        }
        for (int i = 0; i < jj_2_rtns.length; i++) {
            jj_2_rtns[i] = new JJCalls();
        }
    }

    public JavaCCParser(java.io.Reader stream) {
        if (jj_initialized_once) {
            System.out.println("ERROR: Second call to constructor of static parser.  You must");
            System.out
                    .println("       either use ReInit() or set the JavaCC option STATIC to false");
            System.out.println("       during parser generation.");
            throw new Error();
        }
        jj_initialized_once = true;
        jj_input_stream = new JavaCharStream(stream, 1, 1);
        token_source = new JavaCCParserTokenManager(jj_input_stream);
        token = new Token();
        jj_ntk = -1;
        jj_gen = 0;
        for (int i = 0; i < 173; i++) {
            jj_la1[i] = -1;
        }
        for (int i = 0; i < jj_2_rtns.length; i++) {
            jj_2_rtns[i] = new JJCalls();
        }
    }

    public JavaCCParser(JavaCCParserTokenManager tm) {
        if (jj_initialized_once) {
            System.out.println("ERROR: Second call to constructor of static parser.  You must");
            System.out
                    .println("       either use ReInit() or set the JavaCC option STATIC to false");
            System.out.println("       during parser generation.");
            throw new Error();
        }
        jj_initialized_once = true;
        token_source = tm;
        token = new Token();
        jj_ntk = -1;
        jj_gen = 0;
        for (int i = 0; i < 173; i++) {
            jj_la1[i] = -1;
        }
        for (int i = 0; i < jj_2_rtns.length; i++) {
            jj_2_rtns[i] = new JJCalls();
        }
    }

    public final static void initialize(Reader r) {
        current = null;
        comments.clear();
        ReInit(r);
    }

    private static boolean isSuperAllowed() {
        return superAllowed;
    }

    private static void setAllowSuper(boolean b) {
        superAllowed = b;
    }

    public static boolean isAwareOfAssert() {
        return jdk1_4;
    }

    public static void setAwareOfAssert(boolean yes) {
        jdk1_4 = yes;
        if (!yes) {
            jdk1_5 = false;
        }
    }

    public static boolean isJava5() {
        return jdk1_5;
    }

    public static void setJava5(boolean yes) {
        jdk1_5 = yes;
        if (yes) {
            jdk1_4 = true;
        }
    }

    public static int getTabSize() {
        return JavaCharStream.getTabSize(0); // whatever...
    }

    public static void setTabSize(int tabSize) {
        JavaCharStream.setTabSize(tabSize);
    }

    private static void copyPrefixInfo(SourceElement oldResult, SourceElement newResult) {
        newResult.setRelativePosition(oldResult.getRelativePosition());
        newResult.setStartPosition(oldResult.getStartPosition());
        newResult.setEndPosition(oldResult.getEndPosition());
    }

    private static void shiftToken() {
        if (current != token) {
            if (current != null) {
                while (current.next != token) {
                    current = current.next;
                }
            }
            Token prev;
            if (token.specialToken != null) {
                prev = token.specialToken;
            } else {
                prev = current;
            }
            if (prev != null) {
                int col = token.beginColumn - 1;
                int lf = token.beginLine - prev.endLine;
                if (lf <= 0) {
                    col -= prev.endColumn; // - 1;
                    if (col < 0) {
                        col = 0;
                    }
                }
                position.setPosition(lf, col);
            }
            current = token;
        }
    }

    /**
     * Sets indentation information.
     */
    private static void setPrefixInfo(SourceElement constrResult) {
        position.setPosition(0, 0);
        shiftToken();
        constrResult.setRelativePosition(position);
        position.setPosition(current.beginLine, current.beginColumn);
        constrResult.setStartPosition(position);
    }

    private static void setPostfixInfo(SourceElement constrResult) {
        shiftToken();
        position.setPosition(current.endLine, current.endColumn);
        constrResult.setEndPosition(position);
    }

    private static void addComment(Comment c, Token tok) {
        Token prev = tok.specialToken;
        if (prev == null) {
            prev = token;
            // in case we are inside a lookahead we skip to the last known
            // non-special token
            while (prev.next != null) {
                prev = prev.next;
            }
        }
        position.setPosition(0, 0);

        int internalIndentation = 0;
        int internalLinefeeds = 0;
        if (prev.image != null) {
            int col = tok.beginColumn - 1;
            int lf = tok.beginLine - prev.endLine;
            if (lf <= 0) {
                col -= prev.endColumn; // - 1;
            }
            position.setPosition(lf, col);
        }
        c.setRelativePosition(position);
        position.setPosition(tok.endLine, tok.endColumn);
        c.setEndPosition(position);
        position.setPosition(tok.beginLine, tok.beginColumn);
        c.setStartPosition(position);
        if (!(c instanceof DocComment)) {
            boolean hasEmptyLine = c.getRelativePosition().getLine() > 1;
            c.setPrefixed(hasEmptyLine);
            if (tok.specialToken != null && !hasEmptyLine) {
                c.setPrefixed(comments.get(comments.size() - 1).isPrefixed());
            }
        }
        comments.add(c);
    }

    static void addSingleLineComment(Token tok) {
        addComment(factory.createSingleLineComment(tok.image.trim()), tok);
    }

    static void addMultiLineComment(Token tok) {
        addComment(factory.createComment(tok.image), tok);
    }

    static void addDocComment(Token tok) {
        addComment(factory.createDocComment(tok.image), tok);
    }

    public static List<Comment> getComments() {
        return comments;
    }

    /*****************************************
     * THE JAVA LANGUAGE GRAMMAR STARTS HERE *
     *****************************************/

    /*
     * Program structuring syntax follows.
     */
    static final public CompilationUnit CompilationUnit() throws ParseException {
        CompilationUnit result;
        PackageSpecification ps = null;
        ASTList<Import> il = new ASTArrayList<>();
        Import imp;
        ASTList<TypeDeclaration> tdl = new ASTArrayList<>();
        TypeDeclaration td;
        if (jj_2_1(2147483647)) {
            ps = PackageDeclaration();
            label_1: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case IMPORT:
                    break;
                default:
                    jj_la1[0] = jj_gen;
                    break label_1;
                }
                imp = ImportDeclaration();
                il.add(imp);
            }
            label_2: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case ABSTRACT:
                case AT:
                case CLASS:
                case ENUM:
                case FINAL:
                case INTERFACE:
                case PRIVATE:
                case PROTECTED:
                case PUBLIC:
                case STATIC:
                case STRICTFP:
                case SEMICOLON:
                    break;
                default:
                    jj_la1[1] = jj_gen;
                    break label_2;
                }
                td = TypeDeclaration();
                if (td != null) {
                    tdl.add(td);
                }
            }
        } else {
            label_3: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case IMPORT:
                    break;
                default:
                    jj_la1[2] = jj_gen;
                    break label_3;
                }
                imp = ImportDeclaration();
                il.add(imp);
            }
            label_4: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case ABSTRACT:
                case AT:
                case CLASS:
                case ENUM:
                case FINAL:
                case INTERFACE:
                case PRIVATE:
                case PROTECTED:
                case PUBLIC:
                case STATIC:
                case STRICTFP:
                case SEMICOLON:
                    break;
                default:
                    jj_la1[3] = jj_gen;
                    break label_4;
                }
                td = TypeDeclaration();
                if (td != null) {
                    tdl.add(td);
                }
            }
        }
        jj_consume_token(0);
        result = factory.createCompilationUnit(ps, il, tdl);
        setPostfixInfo(result);
        setPrefixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public PackageSpecification PackageDeclaration() throws ParseException {
        PackageSpecification result;
        UncollatedReferenceQualifier qn;
        ASTList<AnnotationUseSpecification> annotations =
            new ASTArrayList<>();
        AnnotationUseSpecification annot;
        label_5: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case AT:
                break;
            default:
                jj_la1[4] = jj_gen;
                break label_5;
            }
            annot = AnnotationUse();
            annotations.add(annot);
        }
        annotations.trimToSize();
        jj_consume_token(PACKAGE);
        result = factory.createPackageSpecification();
        setPrefixInfo(result);
        result.setAnnotations(annotations);
        qn = Name();
        jj_consume_token(SEMICOLON);
        result.setPackageReference(qn.toPackageReference());
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Import ImportDeclaration() throws ParseException {
        Import result;
        UncollatedReferenceQualifier qn;
        String hs = null;
        boolean wildcard = false;
        boolean isStatic = false;
        jj_consume_token(IMPORT);
        result = factory.createImport();
        setPrefixInfo(result);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case STATIC:
            jj_consume_token(STATIC);
            isStatic = true;
            break;
        default:
            jj_la1[5] = jj_gen;
        }
        qn = Name();
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case DOT:
            jj_consume_token(DOT);
            jj_consume_token(STAR);
            wildcard = true;
            break;
        default:
            jj_la1[6] = jj_gen;
        }
        jj_consume_token(SEMICOLON);
        // "*" will be thrown away immediately since the package name is sufficient
        result.setMultiImport(wildcard);
        if (isStatic) {
            result.setStaticImport(true);
            if (wildcard) {
                result.setReference(qn.toTypeReference());
            } else {
                result.setStaticIdentifier(qn.getIdentifier());
                UncollatedReferenceQualifier urq =
                    (UncollatedReferenceQualifier) qn.getReferencePrefix();
                urq.setReferenceSuffix(null);
                result.setReference(urq.toTypeReference());
            }
        } else if (wildcard) {
            result.setReference(qn);
        } else {
            result.setReference(qn.toTypeReference());
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public TypeDeclaration TypeDeclaration() throws ParseException {
        TypeDeclaration result = null;
        if (jj_2_2(2147483647)) {
            result = ClassDeclaration();
        } else if (jj_2_3(2147483647)) {
            result = InterfaceDeclaration();
        } else if (jj_2_4(2147483647)) {
            result = EnumDeclaration();
        } else if (jj_2_5(2147483647)) {
            result = AnnotationTypeDeclaration();
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case SEMICOLON:
                jj_consume_token(SEMICOLON);
                break;
            default:
                jj_la1[7] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
        }
        if (result != null) { // may be removed as soon as Recoder fully understands Java5
            setPostfixInfo(result);
        }
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    /*
     * Declaration syntax follows.
     */
    static final public AnnotationDeclaration AnnotationTypeDeclaration() throws ParseException {
        ASTList<MemberDeclaration> members = new ASTArrayList<>();
        MethodDeclaration md;
        FieldDeclaration fd;
        TypeDeclaration td;
        ASTList<DeclarationSpecifier> declSpecs = new ASTArrayList<>(),
                methodDs;
        DeclarationSpecifier ds;
        Identifier name, methodName;
        TypeReference methodRes;
        Expression methodDefExpr;
        AnnotationDeclaration result = new AnnotationDeclaration();
        while (true) {
            if (jj_2_6(2)) {
            } else {
                break;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case STRICTFP:
                jj_consume_token(STRICTFP);
                ds = factory.createStrictFp();
                break;
            case PUBLIC:
                jj_consume_token(PUBLIC);
                ds = factory.createPublic();
                break;
            case PROTECTED:
                jj_consume_token(PROTECTED);
                ds = factory.createProtected();
                break;
            case PRIVATE:
                jj_consume_token(PRIVATE);
                ds = factory.createPrivate();
                break;
            case STATIC:
                jj_consume_token(STATIC);
                ds = factory.createStatic();
                break;
            case ABSTRACT:
                jj_consume_token(ABSTRACT);
                ds = factory.createAbstract();
                break;
            case AT:
                ds = AnnotationUse();
                break;
            default:
                jj_la1[8] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
            declSpecs.add(ds);
        }
        jj_consume_token(AT);
        setPrefixInfo(result);
        jj_consume_token(INTERFACE);
        jj_consume_token(IDENTIFIER);
        name = factory.createIdentifier(token.image);
        jj_consume_token(LBRACE);
        label_7: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case ABSTRACT:
            case AT:
            case BOOLEAN:
            case BYTE:
            case CHAR:
            case CLASS:
            case DOUBLE:
            case ENUM:
            case FINAL:
            case FLOAT:
            case INT:
            case INTERFACE:
            case LONG:
            case PRIVATE:
            case PROTECTED:
            case PUBLIC:
            case SHORT:
            case STATIC:
            case TRANSIENT:
            case VOLATILE:
            case STRICTFP:
            case IDENTIFIER:
            case SEMICOLON:
                break;
            default:
                jj_la1[9] = jj_gen;
                break label_7;
            }
            if (jj_2_7(2147483647)) {
                methodDs = new ASTArrayList<>();
                label_8: while (true) {
                    switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case ABSTRACT:
                    case AT:
                    case PUBLIC:
                        break;
                    default:
                        jj_la1[10] = jj_gen;
                        break label_8;
                    }
                    switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case AT:
                        ds = AnnotationUse();
                        break;
                    case PUBLIC:
                        jj_consume_token(PUBLIC);
                        ds = factory.createPublic();
                        break;
                    case ABSTRACT:
                        jj_consume_token(ABSTRACT);
                        ds = factory.createAbstract();
                        break;
                    default:
                        jj_la1[11] = jj_gen;
                        jj_consume_token(-1);
                        throw new ParseException();
                    }
                    methodDs.add(ds);
                }
                methodRes = Type();
                jj_consume_token(IDENTIFIER);
                methodName = factory.createIdentifier(token.image);
                jj_consume_token(LPAREN);
                jj_consume_token(RPAREN);
                methodDefExpr = null;
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case _DEFAULT:
                    jj_consume_token(_DEFAULT);
                    methodDefExpr = ElementValue();
                    break;
                default:
                    jj_la1[12] = jj_gen;
                }
                md = factory.createAnnotationPropertyDeclaration(methodDs, methodRes, methodName,
                    methodDefExpr);
                members.add(md);
            } else if (jj_2_8(2147483647)) {
                fd = FieldDeclaration();
                members.add(fd);
            } else if (jj_2_9(2147483647)) {
                td = NestedClassDeclaration();
                members.add(td);
            } else if (jj_2_10(2147483647)) {
                td = EnumDeclaration();
                members.add(td);
            } else if (jj_2_11(2147483647)) {
                td = NestedInterfaceDeclaration();
                members.add(td);
            } else if (jj_2_12(2147483647)) {
                td = AnnotationTypeDeclaration();
                members.add(td);
            } else {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case SEMICOLON:
                    jj_consume_token(SEMICOLON);
                    break;
                default:
                    jj_la1[13] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
                }
            }
        }
        jj_consume_token(RBRACE);
        result.setDeclarationSpecifiers(declSpecs);
        result.setIdentifier(name);
        result.setMembers(members);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public EnumDeclaration EnumDeclaration() throws ParseException {
        DeclarationSpecifier ds;
        ASTList<DeclarationSpecifier> declSpecs = new ASTArrayList<>();
        EnumDeclaration result;
        ASTList<MemberDeclaration> members = new ASTArrayList<>();
        MemberDeclaration md;
        Implements im;
        ASTList<UncollatedReferenceQualifier> nl;
        EnumConstantDeclaration constant;
        while (true) {
            if (jj_2_13(2)) {
            } else {
                break;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case STRICTFP:
                jj_consume_token(STRICTFP);
                ds = factory.createStrictFp();
                break;
            case PUBLIC:
                jj_consume_token(PUBLIC);
                ds = factory.createPublic();
                break;
            case PROTECTED:
                jj_consume_token(PROTECTED);
                ds = factory.createProtected();
                break;
            case PRIVATE:
                jj_consume_token(PRIVATE);
                ds = factory.createPrivate();
                break;
            case STATIC:
                jj_consume_token(STATIC);
                ds = factory.createStatic();
                break;
            case AT:
                ds = AnnotationUse();
                break;
            default:
                jj_la1[14] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
            setPrefixInfo(ds);
            setPostfixInfo(ds);
            declSpecs.add(ds);
        }
        jj_consume_token(ENUM);
        result = new EnumDeclaration();
        setPrefixInfo(result);
        if (declSpecs.size() != 0) {
            result.setDeclarationSpecifiers(declSpecs);
        }
        jj_consume_token(IDENTIFIER);
        Identifier id = factory.createIdentifier(token.image);
        setPrefixInfo(id);
        setPostfixInfo(id);
        result.setIdentifier(id);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case IMPLEMENTS:
            jj_consume_token(IMPLEMENTS);
            im = factory.createImplements();
            setPrefixInfo(im);
            nl = TypedNameList();
            ASTList<TypeReference> trl = new ASTArrayList<>();
            for (UncollatedReferenceQualifier uncollatedReferenceQualifier : nl) {
                TypeReference tr = uncollatedReferenceQualifier.toTypeReference();
                trl.add(tr);
            }
            im.setSupertypes(trl);
            result.setImplementedTypes(im);
            break;
        default:
            jj_la1[15] = jj_gen;
        }
        jj_consume_token(LBRACE);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case AT:
        case IDENTIFIER:
            constant = EnumConstant();
            members.add(constant);
            while (true) {
                if (jj_2_14(2)) {
                } else {
                    break;
                }
                jj_consume_token(COMMA);
                constant = EnumConstant();
                members.add(constant);
            }
            break;
        default:
            jj_la1[16] = jj_gen;
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case COMMA:
            jj_consume_token(COMMA);
            break;
        default:
            jj_la1[17] = jj_gen;
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case SEMICOLON:
            jj_consume_token(SEMICOLON);
            label_11: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case ABSTRACT:
                case AT:
                case BOOLEAN:
                case BYTE:
                case CHAR:
                case CLASS:
                case DOUBLE:
                case ENUM:
                case FINAL:
                case FLOAT:
                case INT:
                case INTERFACE:
                case LONG:
                case NATIVE:
                case PRIVATE:
                case PROTECTED:
                case PUBLIC:
                case SHORT:
                case STATIC:
                case SYNCHRONIZED:
                case TRANSIENT:
                case VOID:
                case VOLATILE:
                case STRICTFP:
                case IDENTIFIER:
                case LBRACE:
                case LT:
                    break;
                default:
                    jj_la1[18] = jj_gen;
                    break label_11;
                }
                md = ClassBodyDeclaration();
                members.add(md);
            }
            break;
        default:
            jj_la1[19] = jj_gen;
        }
        jj_consume_token(RBRACE);
        result.setMembers(members);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public EnumConstantDeclaration EnumConstant() throws ParseException {
        AnnotationUseSpecification annot;
        ASTArrayList<DeclarationSpecifier> annotations = null;
        Identifier id;
        ASTList<Expression> args = null;
        ClassDeclaration cd = null;
        ASTList<MemberDeclaration> body = null;
        EnumConstantSpecification spec;
        EnumConstructorReference ref = null;
        EnumConstantDeclaration result = new EnumConstantDeclaration();
        setPrefixInfo(result);
        label_12: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case AT:
                break;
            default:
                jj_la1[20] = jj_gen;
                break label_12;
            }
            if (annotations == null) {
                annotations = new ASTArrayList<>();
            }
            annot = AnnotationUse();
            annotations.add(annot);
        }
        jj_consume_token(IDENTIFIER);
        id = factory.createIdentifier(token.image);
        setPrefixInfo(id);
        setPostfixInfo(id);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case LPAREN:
            args = Arguments();
            break;
        default:
            jj_la1[21] = jj_gen;
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case LBRACE:
            cd = factory.createClassDeclaration();
            setPrefixInfo(cd);
            body = ClassBody();
            cd.setMembers(body);
            setPostfixInfo(cd);
            break;
        default:
            jj_la1[22] = jj_gen;
        }
        ref = new EnumConstructorReference(args, cd);
        setPrefixInfo(ref); // TODO this maybe too late ?!
        setPostfixInfo(ref);
        spec = new EnumConstantSpecification(id, ref);
        setPrefixInfo(spec); // TODO this maybe too late ?!
        setPostfixInfo(spec);
        setPostfixInfo(result);
        result.setEnumConstantSpecification(spec);
        result.setDeclarationSpecifiers(annotations);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public ClassDeclaration ClassDeclaration() throws ParseException {
        ClassDeclaration result = null;
        ASTList<DeclarationSpecifier> ml = new ASTArrayList<>();
        DeclarationSpecifier m;
        label_13: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case ABSTRACT:
            case AT:
            case FINAL:
            case PUBLIC:
            case STRICTFP:
                break;
            default:
                jj_la1[23] = jj_gen;
                break label_13;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case ABSTRACT:
                jj_consume_token(ABSTRACT);
                m = factory.createAbstract();
                break;
            case FINAL:
                jj_consume_token(FINAL);
                m = factory.createFinal();
                break;
            case PUBLIC:
                jj_consume_token(PUBLIC);
                m = factory.createPublic();
                break;
            case STRICTFP:
                jj_consume_token(STRICTFP);
                m = factory.createStrictFp();
                break;
            case AT:
                m = AnnotationUse();
                break;
            default:
                jj_la1[24] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
            setPrefixInfo(m);
            setPostfixInfo(m);
            ml.add(m);
        }
        result = UnmodifiedClassDeclaration();
        result.setDeclarationSpecifiers(ml);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public ClassDeclaration UnmodifiedClassDeclaration() throws ParseException {
        ClassDeclaration result;
        UncollatedReferenceQualifier qn;
        ASTList<UncollatedReferenceQualifier> nl;
        ASTList<MemberDeclaration> mdl;
        Extends ex;
        Implements im;
        ASTList<TypeParameterDeclaration> typeParams = null;
        jj_consume_token(CLASS);
        result = factory.createClassDeclaration();
        setPrefixInfo(result);
        jj_consume_token(IDENTIFIER);
        Identifier id = factory.createIdentifier(token.image);
        setPrefixInfo(id);
        setPostfixInfo(id);
        result.setIdentifier(id);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case LT:
            typeParams = TypeParameters();
            result.setTypeParameters(typeParams);
            break;
        default:
            jj_la1[25] = jj_gen;
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case EXTENDS:
            jj_consume_token(EXTENDS);
            ex = factory.createExtends();
            setPrefixInfo(ex);
            qn = TypedName();
            ex.setSupertypes(new ASTArrayList<>(1));
            ex.getSupertypes().add(qn.toTypeReference());
            result.setExtendedTypes(ex);
            break;
        default:
            jj_la1[26] = jj_gen;
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case IMPLEMENTS:
            jj_consume_token(IMPLEMENTS);
            im = factory.createImplements();
            setPrefixInfo(im);
            nl = TypedNameList();
            ASTList<TypeReference> trl = new ASTArrayList<>();
            for (UncollatedReferenceQualifier uncollatedReferenceQualifier : nl) {
                TypeReference tr = uncollatedReferenceQualifier.toTypeReference();
                trl.add(tr);
            }
            im.setSupertypes(trl);
            result.setImplementedTypes(im);
            break;
        default:
            jj_la1[27] = jj_gen;
        }
        mdl = ClassBody();
        result.setMembers(mdl);
        setPostfixInfo(result); // coordinate of "}" ?!
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public ASTList<MemberDeclaration> ClassBody() throws ParseException {
        ASTList<MemberDeclaration> result = new ASTArrayList<>();
        MemberDeclaration md;
        jj_consume_token(LBRACE);
        label_14: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case ABSTRACT:
            case AT:
            case BOOLEAN:
            case BYTE:
            case CHAR:
            case CLASS:
            case DOUBLE:
            case ENUM:
            case FINAL:
            case FLOAT:
            case INT:
            case INTERFACE:
            case LONG:
            case NATIVE:
            case PRIVATE:
            case PROTECTED:
            case PUBLIC:
            case SHORT:
            case STATIC:
            case SYNCHRONIZED:
            case TRANSIENT:
            case VOID:
            case VOLATILE:
            case STRICTFP:
            case IDENTIFIER:
            case LBRACE:
            case LT:
                break;
            default:
                jj_la1[28] = jj_gen;
                break label_14;
            }
            md = ClassBodyDeclaration();
            result.add(md);
        }
        jj_consume_token(RBRACE);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public ClassDeclaration NestedClassDeclaration() throws ParseException {
        ClassDeclaration result;
        ASTList<DeclarationSpecifier> ml = new ASTArrayList<>();
        DeclarationSpecifier m;
        label_15: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case ABSTRACT:
            case AT:
            case FINAL:
            case PRIVATE:
            case PROTECTED:
            case PUBLIC:
            case STATIC:
            case STRICTFP:
                break;
            default:
                jj_la1[29] = jj_gen;
                break label_15;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case STATIC:
                jj_consume_token(STATIC);
                m = factory.createStatic();
                break;
            case ABSTRACT:
                jj_consume_token(ABSTRACT);
                m = factory.createAbstract();
                break;
            case FINAL:
                jj_consume_token(FINAL);
                m = factory.createFinal();
                break;
            case PUBLIC:
                jj_consume_token(PUBLIC);
                m = factory.createPublic();
                break;
            case PROTECTED:
                jj_consume_token(PROTECTED);
                m = factory.createProtected();
                break;
            case PRIVATE:
                jj_consume_token(PRIVATE);
                m = factory.createPrivate();
                break;
            case STRICTFP:
                jj_consume_token(STRICTFP);
                m = factory.createStrictFp();
                break;
            case AT:
                m = AnnotationUse();
                break;
            default:
                jj_la1[30] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
            setPrefixInfo(m);
            setPostfixInfo(m);
            ml.add(m);
        }
        result = UnmodifiedClassDeclaration();
        result.setDeclarationSpecifiers(ml);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public MemberDeclaration ClassBodyDeclaration() throws ParseException {
        MemberDeclaration result;
        if (jj_2_15(2)) {
            result = Initializer();
            label_16: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case SEMICOLON:
                    break;
                default:
                    jj_la1[31] = jj_gen;
                    break label_16;
                }
                jj_consume_token(SEMICOLON);
            }
        } else if (jj_2_16(2147483647)) {
            result = NestedClassDeclaration();
            label_17: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case SEMICOLON:
                    break;
                default:
                    jj_la1[32] = jj_gen;
                    break label_17;
                }
                jj_consume_token(SEMICOLON);
            }
        } else if (jj_2_17(2147483647)) {
            result = NestedInterfaceDeclaration();
            label_18: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case SEMICOLON:
                    break;
                default:
                    jj_la1[33] = jj_gen;
                    break label_18;
                }
                jj_consume_token(SEMICOLON);
            }
        } else if (jj_2_18(2147483647)) {
            result = ConstructorDeclaration();
            label_19: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case SEMICOLON:
                    break;
                default:
                    jj_la1[34] = jj_gen;
                    break label_19;
                }
                jj_consume_token(SEMICOLON);
            }
        } else if (jj_2_19(2147483647)) {
            result = MethodDeclaration();
            label_20: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case SEMICOLON:
                    break;
                default:
                    jj_la1[35] = jj_gen;
                    break label_20;
                }
                jj_consume_token(SEMICOLON);
            }
        } else if (jj_2_20(2147483647)) {
            result = EnumDeclaration();
            label_21: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case SEMICOLON:
                    break;
                default:
                    jj_la1[36] = jj_gen;
                    break label_21;
                }
                jj_consume_token(SEMICOLON);
            }
        } else if (jj_2_21(2147483647)) {
            result = AnnotationTypeDeclaration();
            label_22: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case SEMICOLON:
                    break;
                default:
                    jj_la1[37] = jj_gen;
                    break label_22;
                }
                jj_consume_token(SEMICOLON);
            }
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case AT:
            case BOOLEAN:
            case BYTE:
            case CHAR:
            case DOUBLE:
            case FINAL:
            case FLOAT:
            case INT:
            case LONG:
            case PRIVATE:
            case PROTECTED:
            case PUBLIC:
            case SHORT:
            case STATIC:
            case TRANSIENT:
            case VOLATILE:
            case IDENTIFIER:
                result = FieldDeclaration();
                label_23: while (true) {
                    switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case SEMICOLON:
                        break;
                    default:
                        jj_la1[38] = jj_gen;
                        break label_23;
                    }
                    jj_consume_token(SEMICOLON);
                }
                break;
            default:
                jj_la1[39] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public InterfaceDeclaration InterfaceDeclaration() throws ParseException {
        InterfaceDeclaration result;
        ASTList<DeclarationSpecifier> ml = new ASTArrayList<>();
        DeclarationSpecifier m;
        label_24: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case ABSTRACT:
            case AT:
            case PUBLIC:
            case STRICTFP:
                break;
            default:
                jj_la1[40] = jj_gen;
                break label_24;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case ABSTRACT:
                jj_consume_token(ABSTRACT);
                m = factory.createAbstract();
                break;
            case PUBLIC:
                jj_consume_token(PUBLIC);
                m = factory.createPublic();
                break;
            case STRICTFP:
                jj_consume_token(STRICTFP);
                m = factory.createStrictFp();
                break;
            case AT:
                m = AnnotationUse();
                break;
            default:
                jj_la1[41] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
            setPrefixInfo(m);
            setPostfixInfo(m);
            ml.add(m);
        }
        result = UnmodifiedInterfaceDeclaration();
        result.setDeclarationSpecifiers(ml);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public InterfaceDeclaration NestedInterfaceDeclaration() throws ParseException {
        InterfaceDeclaration result;
        ASTList<DeclarationSpecifier> ml = new ASTArrayList<>();
        DeclarationSpecifier m;
        label_25: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case ABSTRACT:
            case AT:
            case FINAL:
            case PRIVATE:
            case PROTECTED:
            case PUBLIC:
            case STATIC:
            case STRICTFP:
                break;
            default:
                jj_la1[42] = jj_gen;
                break label_25;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case STATIC:
                jj_consume_token(STATIC);
                m = factory.createStatic();
                break;
            case ABSTRACT:
                jj_consume_token(ABSTRACT);
                m = factory.createAbstract();
                break;
            case FINAL:
                jj_consume_token(FINAL);
                m = factory.createFinal();
                break;
            case PUBLIC:
                jj_consume_token(PUBLIC);
                m = factory.createPublic();
                break;
            case PROTECTED:
                jj_consume_token(PROTECTED);
                m = factory.createProtected();
                break;
            case PRIVATE:
                jj_consume_token(PRIVATE);
                m = factory.createPrivate();
                break;
            case STRICTFP:
                jj_consume_token(STRICTFP);
                m = factory.createStrictFp();
                break;
            case AT:
                m = AnnotationUse();
                break;
            default:
                jj_la1[43] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
            setPrefixInfo(m);
            setPostfixInfo(m);
            ml.add(m);
        }
        result = UnmodifiedInterfaceDeclaration();
        result.setDeclarationSpecifiers(ml);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public InterfaceDeclaration UnmodifiedInterfaceDeclaration()
            throws ParseException {
        InterfaceDeclaration result;
        ASTList<UncollatedReferenceQualifier> nl;
        ASTList<MemberDeclaration> mdl = new ASTArrayList<>();
        MemberDeclaration md;
        Extends ex;
        ASTList<TypeParameterDeclaration> typeParams = null;
        jj_consume_token(INTERFACE);
        result = factory.createInterfaceDeclaration();
        setPrefixInfo(result);
        jj_consume_token(IDENTIFIER);
        Identifier id = factory.createIdentifier(token.image);
        setPrefixInfo(id);
        setPostfixInfo(id);
        result.setIdentifier(id);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case LT:
            typeParams = TypeParameters();
            result.setTypeParameters(typeParams);
            break;
        default:
            jj_la1[44] = jj_gen;
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case EXTENDS:
            jj_consume_token(EXTENDS);
            ex = factory.createExtends();
            setPrefixInfo(ex);
            nl = TypedNameList();
            ASTList<TypeReference> trl = new ASTArrayList<>();
            for (UncollatedReferenceQualifier uncollatedReferenceQualifier : nl) {
                TypeReference tr = uncollatedReferenceQualifier.toTypeReference();
                trl.add(tr);
            }
            ex.setSupertypes(trl);
            result.setExtendedTypes(ex);
            break;
        default:
            jj_la1[45] = jj_gen;
        }
        jj_consume_token(LBRACE);
        label_26: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case ABSTRACT:
            case AT:
            case BOOLEAN:
            case BYTE:
            case CHAR:
            case CLASS:
            case DOUBLE:
            case ENUM:
            case FINAL:
            case FLOAT:
            case INT:
            case INTERFACE:
            case LONG:
            case NATIVE:
            case PRIVATE:
            case PROTECTED:
            case PUBLIC:
            case SHORT:
            case STATIC:
            case SYNCHRONIZED:
            case TRANSIENT:
            case VOID:
            case VOLATILE:
            case STRICTFP:
            case IDENTIFIER:
            case LT:
                break;
            default:
                jj_la1[46] = jj_gen;
                break label_26;
            }
            md = InterfaceMemberDeclaration();
            mdl.add(md);
        }
        jj_consume_token(RBRACE);
        result.setMembers(mdl);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public MemberDeclaration InterfaceMemberDeclaration() throws ParseException {
        MemberDeclaration result;
        if (jj_2_22(2147483647)) {
            result = NestedClassDeclaration();
            label_27: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case SEMICOLON:
                    break;
                default:
                    jj_la1[47] = jj_gen;
                    break label_27;
                }
                jj_consume_token(SEMICOLON);
            }
        } else if (jj_2_23(2147483647)) {
            result = NestedInterfaceDeclaration();
            label_28: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case SEMICOLON:
                    break;
                default:
                    jj_la1[48] = jj_gen;
                    break label_28;
                }
                jj_consume_token(SEMICOLON);
            }
        } else if (jj_2_24(2147483647)) {
            result = MethodDeclaration();
            label_29: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case SEMICOLON:
                    break;
                default:
                    jj_la1[49] = jj_gen;
                    break label_29;
                }
                jj_consume_token(SEMICOLON);
            }
        } else if (jj_2_25(2147483647)) {
            result = EnumDeclaration();
            label_30: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case SEMICOLON:
                    break;
                default:
                    jj_la1[50] = jj_gen;
                    break label_30;
                }
                jj_consume_token(SEMICOLON);
            }
        } else if (jj_2_26(2147483647)) {
            result = AnnotationTypeDeclaration();
            label_31: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case SEMICOLON:
                    break;
                default:
                    jj_la1[51] = jj_gen;
                    break label_31;
                }
                jj_consume_token(SEMICOLON);
            }
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case AT:
            case BOOLEAN:
            case BYTE:
            case CHAR:
            case DOUBLE:
            case FINAL:
            case FLOAT:
            case INT:
            case LONG:
            case PRIVATE:
            case PROTECTED:
            case PUBLIC:
            case SHORT:
            case STATIC:
            case TRANSIENT:
            case VOLATILE:
            case IDENTIFIER:
                result = FieldDeclaration();
                label_32: while (true) {
                    switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case SEMICOLON:
                        break;
                    default:
                        jj_la1[52] = jj_gen;
                        break label_32;
                    }
                    jj_consume_token(SEMICOLON);
                }
                break;
            default:
                jj_la1[53] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public FieldDeclaration FieldDeclaration() throws ParseException {
        FieldDeclaration result;
        ASTList<DeclarationSpecifier> ml = new ASTArrayList<>();
        DeclarationSpecifier m = null;
        TypeReference tr;
        ASTArrayList<FieldSpecification> vl = new ASTArrayList<>();
        VariableSpecification var;
        boolean hasPrefixInfo = false;
        result = factory.createFieldDeclaration();
        label_33: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case AT:
            case FINAL:
            case PRIVATE:
            case PROTECTED:
            case PUBLIC:
            case STATIC:
            case TRANSIENT:
            case VOLATILE:
                break;
            default:
                jj_la1[54] = jj_gen;
                break label_33;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case PUBLIC:
                jj_consume_token(PUBLIC);
                m = factory.createPublic();
                break;
            case PROTECTED:
                jj_consume_token(PROTECTED);
                m = factory.createProtected();
                break;
            case PRIVATE:
                jj_consume_token(PRIVATE);
                m = factory.createPrivate();
                break;
            case STATIC:
                jj_consume_token(STATIC);
                m = factory.createStatic();
                break;
            case FINAL:
                jj_consume_token(FINAL);
                m = factory.createFinal();
                break;
            case TRANSIENT:
                jj_consume_token(TRANSIENT);
                m = factory.createTransient();
                break;
            case VOLATILE:
                jj_consume_token(VOLATILE);
                m = factory.createVolatile();
                break;
            case AT:
                m = AnnotationUse();
                break;
            default:
                jj_la1[55] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
            setPrefixInfo(m);
            setPostfixInfo(m);
            ml.add(m);
            if (!hasPrefixInfo) {
                copyPrefixInfo(m, result);
                hasPrefixInfo = true;
            }
        }
        tr = Type();
        if (!hasPrefixInfo) {
            copyPrefixInfo(tr, result);
        }
        result.setDeclarationSpecifiers(ml);
        result.setTypeReference(tr);
        var = VariableDeclarator(true);
        vl.add((FieldSpecification) var);
        label_34: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case COMMA:
                break;
            default:
                jj_la1[56] = jj_gen;
                break label_34;
            }
            jj_consume_token(COMMA);
            var = VariableDeclarator(true);
            vl.add((FieldSpecification) var);
        }
        jj_consume_token(SEMICOLON);
        result.setFieldSpecifications(vl);
        // setPrefixInfo(result);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public VariableSpecification VariableDeclarator(boolean isForField)
            throws ParseException {
        Identifier id;
        int dim = 0;
        Expression init = null;
        VariableSpecification result;
        id = VariableDeclaratorId();
        dim = tmpDimension;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case ASSIGN:
            jj_consume_token(ASSIGN);
            init = VariableInitializer();
            break;
        default:
            jj_la1[57] = jj_gen;
        }
        if (isForField) {
            result = factory.createFieldSpecification(id, dim, init);
        } else {
            result = factory.createVariableSpecification(id, dim, init);
        }
        // setPrefixInfo(result); // only after "=" !!!!!!!!!!!!!!!
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Identifier VariableDeclaratorId() throws ParseException {
        Identifier result;
        jj_consume_token(IDENTIFIER);
        result = factory.createIdentifier(token.image);
        setPrefixInfo(result);
        setPostfixInfo(result);
        tmpDimension = 0;
        label_35: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case LBRACKET:
                break;
            default:
                jj_la1[58] = jj_gen;
                break label_35;
            }
            jj_consume_token(LBRACKET);
            jj_consume_token(RBRACKET);
            tmpDimension++;
        }
        setPostfixInfo(result);
        // setPrefixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Expression VariableInitializer() throws ParseException {
        Expression result;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case LBRACE:
            result = ArrayInitializer();
            break;
        case BOOLEAN:
        case BYTE:
        case CHAR:
        case DOUBLE:
        case FALSE:
        case FLOAT:
        case INT:
        case LONG:
        case NEW:
        case NULL:
        case SHORT:
        case SUPER:
        case THIS:
        case TRUE:
        case VOID:
        case INTEGER_LITERAL:
        case FLOATING_POINT_LITERAL:
        case CHARACTER_LITERAL:
        case STRING_LITERAL:
        case IDENTIFIER:
        case LPAREN:
        case BANG:
        case TILDE:
        case INCR:
        case DECR:
        case PLUS:
        case MINUS:
            result = Expression();
            break;
        default:
            jj_la1[59] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public ArrayInitializer ArrayInitializer() throws ParseException {
        ArrayInitializer result;
        ASTList<Expression> el = new ASTArrayList<>();
        Expression init;
        jj_consume_token(LBRACE);
        result = factory.createArrayInitializer();
        setPrefixInfo(result);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case BOOLEAN:
        case BYTE:
        case CHAR:
        case DOUBLE:
        case FALSE:
        case FLOAT:
        case INT:
        case LONG:
        case NEW:
        case NULL:
        case SHORT:
        case SUPER:
        case THIS:
        case TRUE:
        case VOID:
        case INTEGER_LITERAL:
        case FLOATING_POINT_LITERAL:
        case CHARACTER_LITERAL:
        case STRING_LITERAL:
        case IDENTIFIER:
        case LPAREN:
        case LBRACE:
        case BANG:
        case TILDE:
        case INCR:
        case DECR:
        case PLUS:
        case MINUS:
            init = VariableInitializer();
            el.add(init);
            while (true) {
                if (jj_2_27(2)) {
                } else {
                    break;
                }
                jj_consume_token(COMMA);
                init = VariableInitializer();
                el.add(init);
            }
            break;
        default:
            jj_la1[60] = jj_gen;
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case COMMA:
            jj_consume_token(COMMA);
            break;
        default:
            jj_la1[61] = jj_gen;
        }
        jj_consume_token(RBRACE);
        result.setArguments(el);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public MethodDeclaration MethodDeclaration() throws ParseException {
        ASTList<DeclarationSpecifier> ml = new ASTArrayList<>();
        DeclarationSpecifier m = null;
        TypeReference tr;
        ASTList<UncollatedReferenceQualifier> nl = null;
        Throws th = null;
        StatementBlock body = null;
        MethodDeclaration result;
        ASTList<TypeParameterDeclaration> typeParams = null;
        SourceElement dummy = null;
        label_37: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case ABSTRACT:
            case AT:
            case FINAL:
            case NATIVE:
            case PRIVATE:
            case PROTECTED:
            case PUBLIC:
            case STATIC:
            case SYNCHRONIZED:
            case STRICTFP:
                break;
            default:
                jj_la1[62] = jj_gen;
                break label_37;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case PUBLIC:
                jj_consume_token(PUBLIC);
                m = factory.createPublic();
                break;
            case PROTECTED:
                jj_consume_token(PROTECTED);
                m = factory.createProtected();
                break;
            case PRIVATE:
                jj_consume_token(PRIVATE);
                m = factory.createPrivate();
                break;
            case STATIC:
                jj_consume_token(STATIC);
                m = factory.createStatic();
                break;
            case FINAL:
                jj_consume_token(FINAL);
                m = factory.createFinal();
                break;
            case ABSTRACT:
                jj_consume_token(ABSTRACT);
                m = factory.createAbstract();
                break;
            case NATIVE:
                jj_consume_token(NATIVE);
                m = factory.createNative();
                break;
            case SYNCHRONIZED:
                jj_consume_token(SYNCHRONIZED);
                m = factory.createSynchronized();
                break;
            case STRICTFP:
                jj_consume_token(STRICTFP);
                m = factory.createStrictFp();
                break;
            case AT:
                m = AnnotationUse();
                break;
            default:
                jj_la1[63] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
            setPrefixInfo(m);
            setPostfixInfo(m);
            ml.add(m);
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case LT:
            jj_consume_token(LT);
            if (ml.size() == 0) { // '<' of MethodDeclaration is first element then. Need to store
                                  // the result somewhere...
                dummy = factory.createPublic();
                setPrefixInfo(dummy); /* HACK */
            }
            typeParams = TypeParametersNoLE();
            break;
        default:
            jj_la1[64] = jj_gen;
        }
        tr = ResultType();
        result = MethodDeclarator(tr);
        if (dummy != null) {
            copyPrefixInfo(dummy, result);
            dummy = null;
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case THROWS:
            jj_consume_token(THROWS);
            th = factory.createThrows();
            setPrefixInfo(th);
            nl = TypedNameList();
            break;
        default:
            jj_la1[65] = jj_gen;
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case LBRACE:
            body = Block();
            break;
        case SEMICOLON:
            jj_consume_token(SEMICOLON);
            break;
        default:
            jj_la1[66] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        if (nl != null) {
            ASTList<TypeReference> trl = new ASTArrayList<>();
            for (UncollatedReferenceQualifier uncollatedReferenceQualifier : nl) {
                trl.add(uncollatedReferenceQualifier.toTypeReference());
            }
            th.setExceptions(trl);
            // Throws th = factory.createThrows(trl);
            result.setThrown(th);
        }
        result.setTypeParameters(typeParams);
        result.setDeclarationSpecifiers(ml);
        result.setBody(body);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    // This production is to determine lookahead only.
    static final public void MethodDeclarationLookahead() throws ParseException {
        label_38: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case ABSTRACT:
            case AT:
            case FINAL:
            case NATIVE:
            case PRIVATE:
            case PROTECTED:
            case PUBLIC:
            case STATIC:
            case SYNCHRONIZED:
            case STRICTFP:
                break;
            default:
                jj_la1[67] = jj_gen;
                break label_38;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case PUBLIC:
                jj_consume_token(PUBLIC);
                break;
            case PROTECTED:
                jj_consume_token(PROTECTED);
                break;
            case PRIVATE:
                jj_consume_token(PRIVATE);
                break;
            case STATIC:
                jj_consume_token(STATIC);
                break;
            case ABSTRACT:
                jj_consume_token(ABSTRACT);
                break;
            case FINAL:
                jj_consume_token(FINAL);
                break;
            case NATIVE:
                jj_consume_token(NATIVE);
                break;
            case SYNCHRONIZED:
                jj_consume_token(SYNCHRONIZED);
                break;
            case STRICTFP:
                jj_consume_token(STRICTFP);
                break;
            case AT:
                AnnotationUse();
                break;
            default:
                jj_la1[68] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case LT:
            TypeParameters();
            break;
        default:
            jj_la1[69] = jj_gen;
        }
        ResultType();
        jj_consume_token(IDENTIFIER);
        jj_consume_token(LPAREN);
    }

    static final public MethodDeclaration MethodDeclarator(TypeReference tr) throws ParseException {
        Identifier id;
        ASTList<ParameterDeclaration> pdl;
        MethodDeclaration result;
        jj_consume_token(IDENTIFIER);
        id = factory.createIdentifier(token.image);
        setPrefixInfo(id);
        setPostfixInfo(id);
        pdl = FormalParameters();
        label_39: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case LBRACKET:
                break;
            default:
                jj_la1[70] = jj_gen;
                break label_39;
            }
            jj_consume_token(LBRACKET);
            jj_consume_token(RBRACKET);
            if (tr != null) {
                tr.setDimensions(tr.getDimensions() + 1);
            }
        }
        result = factory.createMethodDeclaration();
        result.setIdentifier(id);
        result.setTypeReference(tr);
        result.setParameters(pdl);
        setPrefixInfo(result);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public ASTList<ParameterDeclaration> FormalParameters() throws ParseException {
        ParameterDeclaration pd;
        ASTList<ParameterDeclaration> result = new ASTArrayList<>();
        jj_consume_token(LPAREN);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case AT:
        case BOOLEAN:
        case BYTE:
        case CHAR:
        case DOUBLE:
        case FINAL:
        case FLOAT:
        case INT:
        case LONG:
        case SHORT:
        case IDENTIFIER:
            pd = FormalParameter();
            result.add(pd);
            label_40: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case COMMA:
                    break;
                default:
                    jj_la1[71] = jj_gen;
                    break label_40;
                }
                jj_consume_token(COMMA);
                pd = FormalParameter();
                // check if more params are admissible (no more after a vararg) occurs in
                // FormalParameter()
                result.add(pd);
            }
            break;
        default:
            jj_la1[72] = jj_gen;
        }
        jj_consume_token(RPAREN);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public ParameterDeclaration FormalParameter() throws ParseException {
        ParameterDeclaration result;
        TypeReference tr;
        DeclarationSpecifier mod = null;
        Identifier id;
        VariableSpecification vspec;
        int dim;
        ASTList<DeclarationSpecifier> ml = null;
        boolean isVarArg = false;
        label_41: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case AT:
                break;
            default:
                jj_la1[73] = jj_gen;
                break label_41;
            }
            mod = AnnotationUse();
            if (ml == null) {
                ml = new ASTArrayList<>();
            }
            setPrefixInfo(mod);
            setPostfixInfo(mod);
            ml.add(mod);
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case FINAL:
            jj_consume_token(FINAL);
            mod = factory.createFinal();
            setPrefixInfo(mod);
            setPostfixInfo(mod);
            if (ml == null) {
                ml = new ASTArrayList<>();
            }
            ml.add(mod);
            label_42: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case AT:
                    break;
                default:
                    jj_la1[74] = jj_gen;
                    break label_42;
                }
                mod = AnnotationUse();
                setPrefixInfo(mod);
                setPostfixInfo(mod);
                ml.add(mod);
            }
            break;
        default:
            jj_la1[75] = jj_gen;
        }
        tr = Type();
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case VARARGDENOTER:
            jj_consume_token(VARARGDENOTER);
            isVarArg = true;
            break;
        default:
            jj_la1[76] = jj_gen;
        }
        id = VariableDeclaratorId();
        dim = tmpDimension; /* if (varArgSpec != null) dim++; */
        result = factory.createParameterDeclaration(tr, id);
        if (ml != null) {
            result.setDeclarationSpecifiers(ml);
        }
        vspec = result.getVariables().get(0);
        vspec.setDimensions(dim);
        setPostfixInfo(result);
        setPrefixInfo(result);
        result.setVarArg(isVarArg);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public ConstructorDeclaration ConstructorDeclaration() throws ParseException {
        ConstructorDeclaration result;
        DeclarationSpecifier m = null;
        ASTList<DeclarationSpecifier> ml = new ASTArrayList<>();
        Identifier id;
        ASTList<ParameterDeclaration> pdl;
        ASTList<UncollatedReferenceQualifier> nl = null;
        SpecialConstructorReference scr = null;
        StatementBlock body;
        ASTList<Statement> stats = new ASTArrayList<>();
        Statement stat;
        result = factory.createConstructorDeclaration();
        label_43: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case AT:
                break;
            default:
                jj_la1[77] = jj_gen;
                break label_43;
            }
            m = AnnotationUse();
            setPrefixInfo(m);
            setPostfixInfo(m);
            ml.add(m);
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case PRIVATE:
        case PROTECTED:
        case PUBLIC:
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case PUBLIC:
                jj_consume_token(PUBLIC);
                m = factory.createPublic();
                break;
            case PROTECTED:
                jj_consume_token(PROTECTED);
                m = factory.createProtected();
                break;
            case PRIVATE:
                jj_consume_token(PRIVATE);
                m = factory.createPrivate();
                break;
            default:
                jj_la1[78] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
            setPrefixInfo(m);
            setPostfixInfo(m);
            ml.add(m);
            label_44: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case AT:
                    break;
                default:
                    jj_la1[79] = jj_gen;
                    break label_44;
                }
                m = AnnotationUse();
                setPrefixInfo(m);
                setPostfixInfo(m);
                ml.add(m);
            }
            break;
        default:
            jj_la1[80] = jj_gen;
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case LT:
            TypeParameters();
            break;
        default:
            jj_la1[81] = jj_gen;
        }
        jj_consume_token(IDENTIFIER);
        id = factory.createIdentifier(token.image);
        setPrefixInfo(id);
        setPostfixInfo(id);
        pdl = FormalParameters();
        setPrefixInfo(result);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case THROWS:
            jj_consume_token(THROWS);
            nl = TypedNameList();
            break;
        default:
            jj_la1[82] = jj_gen;
        }
        jj_consume_token(LBRACE);
        body = factory.createStatementBlock();
        setPrefixInfo(body);
        body.setBody(stats);
        setAllowSuper(false);
        if (jj_2_28(2147483647)) {
            scr = ExplicitConstructorInvocation();
            stats.add(scr);
        } else {
        }
        setAllowSuper(true);
        label_45: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case ASSERT:
            case AT:
            case BOOLEAN:
            case BREAK:
            case BYTE:
            case CHAR:
            case CLASS:
            case CONTINUE:
            case DO:
            case DOUBLE:
            case FALSE:
            case FINAL:
            case FLOAT:
            case FOR:
            case IF:
            case INT:
            case LONG:
            case NEW:
            case NULL:
            case RETURN:
            case SHORT:
            case SUPER:
            case SWITCH:
            case SYNCHRONIZED:
            case THIS:
            case THROW:
            case TRUE:
            case TRY:
            case VOID:
            case WHILE:
            case INTEGER_LITERAL:
            case FLOATING_POINT_LITERAL:
            case CHARACTER_LITERAL:
            case STRING_LITERAL:
            case IDENTIFIER:
            case LPAREN:
            case LBRACE:
            case SEMICOLON:
            case INCR:
            case DECR:
                break;
            default:
                jj_la1[83] = jj_gen;
                break label_45;
            }
            stat = BlockStatement();
            stats.add(stat);
        }
        jj_consume_token(RBRACE);
        setPostfixInfo(body);
        result.setIdentifier(id);
        result.setParameters(pdl);
        if (!ml.isEmpty()) {
            result.setDeclarationSpecifiers(ml);
        }
        if (nl != null) {
            int s = nl.size();
            ASTList<TypeReference> trl = new ASTArrayList<>(s);
            for (UncollatedReferenceQualifier uncollatedReferenceQualifier : nl) {
                trl.add(uncollatedReferenceQualifier.toTypeReference());
            }
            Throws th = factory.createThrows(trl);
            setPrefixInfo(th);
            result.setThrown(th);
        }
        result.setBody(body);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public SpecialConstructorReference ExplicitConstructorInvocation()
            throws ParseException {
        SpecialConstructorReference result;
        ASTList<Expression> args;
        Expression expr = null;
        if (jj_2_30(2147483647)) {
            jj_consume_token(THIS);
            result = factory.createThisConstructorReference();
            setPrefixInfo(result);
            args = Arguments();
            jj_consume_token(SEMICOLON);
            result.setArguments(args);
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case BOOLEAN:
            case BYTE:
            case CHAR:
            case DOUBLE:
            case FALSE:
            case FLOAT:
            case INT:
            case LONG:
            case NEW:
            case NULL:
            case SHORT:
            case SUPER:
            case THIS:
            case TRUE:
            case VOID:
            case INTEGER_LITERAL:
            case FLOATING_POINT_LITERAL:
            case CHARACTER_LITERAL:
            case STRING_LITERAL:
            case IDENTIFIER:
            case LPAREN:
                if (jj_2_29(2)) {
                    expr = PrimaryExpression();
                    jj_consume_token(DOT);
                } else {
                }
                jj_consume_token(SUPER);
                result = factory.createSuperConstructorReference();
                setPrefixInfo(result);
                args = Arguments();
                jj_consume_token(SEMICOLON);
                result.setArguments(args);
                ((SuperConstructorReference) result).setReferencePrefix((ReferencePrefix) expr);
                break;
            default:
                jj_la1[84] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public ClassInitializer Initializer() throws ParseException {
        ClassInitializer result;
        ASTList<DeclarationSpecifier> ml = null;
        StatementBlock block;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case STATIC:
            jj_consume_token(STATIC);
            ml = new ASTArrayList<>();
            Static s = factory.createStatic();
            setPrefixInfo(s);
            setPostfixInfo(s);
            ml.add(s);
            break;
        default:
            jj_la1[85] = jj_gen;
        }
        block = Block();
        result = factory.createClassInitializer(block);
        setPrefixInfo(result);
        if (ml != null) {
            result.setDeclarationSpecifiers(ml);
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    /*
     * Type, name and expression syntax follows.
     */
    static final public TypeReference Type() throws ParseException {
        TypeReference result;
        UncollatedReferenceQualifier qn;
        int dimension = 0;
        if (jj_2_31(2147483647)) {
            // try to match typed name FIRST
            qn = TypedName();
            result = qn.toTypeReference();
            label_46: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case LBRACKET:
                    break;
                default:
                    jj_la1[86] = jj_gen;
                    break label_46;
                }
                jj_consume_token(LBRACKET);
                jj_consume_token(RBRACKET);
                if (dimension == 0) {
                    setPrefixInfo(result);
                }
                dimension++;
            }
            result.setDimensions(dimension);
            setPostfixInfo(result);
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case BOOLEAN:
            case BYTE:
            case CHAR:
            case DOUBLE:
            case FLOAT:
            case INT:
            case LONG:
            case SHORT:
            case IDENTIFIER:
                result = RawType();
                break;
            default:
                jj_la1[87] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
        }
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public TypeReference RawType() throws ParseException {
        TypeReference result;
        UncollatedReferenceQualifier qn;
        int dimension = 0;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case BOOLEAN:
        case BYTE:
        case CHAR:
        case DOUBLE:
        case FLOAT:
        case INT:
        case LONG:
        case SHORT:
            result = PrimitiveType();
            break;
        case IDENTIFIER:
            qn = Name();
            result = qn.toTypeReference();
            break;
        default:
            jj_la1[88] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        label_47: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case LBRACKET:
                break;
            default:
                jj_la1[89] = jj_gen;
                break label_47;
            }
            jj_consume_token(LBRACKET);
            jj_consume_token(RBRACKET);
            if (dimension == 0) {
                setPrefixInfo(result);
            }
            dimension++;
        }
        result.setDimensions(dimension);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public TypeReference PrimitiveType() throws ParseException {
        TypeReference result;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case BOOLEAN:
            jj_consume_token(BOOLEAN);
            break;
        case CHAR:
            jj_consume_token(CHAR);
            break;
        case BYTE:
            jj_consume_token(BYTE);
            break;
        case SHORT:
            jj_consume_token(SHORT);
            break;
        case INT:
            jj_consume_token(INT);
            break;
        case LONG:
            jj_consume_token(LONG);
            break;
        case FLOAT:
            jj_consume_token(FLOAT);
            break;
        case DOUBLE:
            jj_consume_token(DOUBLE);
            break;
        default:
            jj_la1[90] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        Identifier id = factory.createIdentifier(token.image);
        setPrefixInfo(id);
        setPostfixInfo(id);
        result = factory.createTypeReference(id);
        setPostfixInfo(result);
        // setPrefixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public TypeReference ResultType() throws ParseException {
        TypeReference result;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case VOID:
            jj_consume_token(VOID);
            Identifier id = factory.createIdentifier(token.image);
            setPrefixInfo(id);
            setPostfixInfo(id);
            result = factory.createTypeReference(id);
            setPrefixInfo(result);
            break;
        case BOOLEAN:
        case BYTE:
        case CHAR:
        case DOUBLE:
        case FLOAT:
        case INT:
        case LONG:
        case SHORT:
        case IDENTIFIER:
            result = Type();
            break;
        default:
            jj_la1[91] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public UncollatedReferenceQualifier Name() throws ParseException {
        UncollatedReferenceQualifier result;
        Identifier id;
        jj_consume_token(IDENTIFIER);
        id = factory.createIdentifier(token.image);
        setPrefixInfo(id);
        setPostfixInfo(id);
        result = factory.createUncollatedReferenceQualifier(id);
        while (true) {
            if (jj_2_32(2)) {
            } else {
                break;
            }
            jj_consume_token(DOT);
            setPrefixInfo(result);
            setPostfixInfo(result);
            jj_consume_token(IDENTIFIER);
            id = factory.createIdentifier(token.image);
            setPrefixInfo(id);
            setPostfixInfo(id);
            result = factory.createUncollatedReferenceQualifier(result, id);
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public UncollatedReferenceQualifier TypedName() throws ParseException {
        UncollatedReferenceQualifier result;
        Identifier id;
        ASTList<TypeArgumentDeclaration> typeArguments = null;
        jj_consume_token(IDENTIFIER);
        id = factory.createIdentifier(token.image);
        setPrefixInfo(id);
        setPostfixInfo(id);
        if (jj_2_33(2)) {
            typeArguments = TypeArguments();
        } else {
        }
        result = factory.createUncollatedReferenceQualifier(id);
        result.setTypeArguments(typeArguments);
        while (true) {
            if (jj_2_34(2)) {
            } else {
                break;
            }
            jj_consume_token(DOT);
            setPrefixInfo(result);
            setPostfixInfo(result);
            jj_consume_token(IDENTIFIER);
            id = factory.createIdentifier(token.image);
            setPrefixInfo(id);
            setPostfixInfo(id);
            typeArguments = null; // reset!

            if (jj_2_35(2)) {
                typeArguments = TypeArguments();
            } else {
            }
            result = factory.createUncollatedReferenceQualifier(result, id);
            result.setTypeArguments(typeArguments);
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public ASTList<TypeArgumentDeclaration> TypeArguments() throws ParseException {
        ASTList<TypeArgumentDeclaration> args = new ASTArrayList<>();
        TypeArgumentDeclaration ta;
        jj_consume_token(LT);
        ta = TypeArgument();
        args.add(ta);
        label_50: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case COMMA:
                break;
            default:
                jj_la1[92] = jj_gen;
                break label_50;
            }
            jj_consume_token(COMMA);
            ta = TypeArgument();
            args.add(ta);
        }
        jj_consume_token(GT);
        {
            if (true) {
                return args;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public TypeArgumentDeclaration TypeArgument() throws ParseException {
        WildcardMode wm = WildcardMode.None;
        TypeReference t = null;
        TypeArgumentDeclaration result = new TypeArgumentDeclaration();
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case BOOLEAN:
        case BYTE:
        case CHAR:
        case DOUBLE:
        case FLOAT:
        case INT:
        case LONG:
        case SHORT:
        case IDENTIFIER:
            t = Type();
            setPrefixInfo(result);
            break;
        case HOOK:
            jj_consume_token(HOOK);
            wm = WildcardMode.Any;
            setPrefixInfo(result);
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case EXTENDS:
            case SUPER:
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case EXTENDS:
                    jj_consume_token(EXTENDS);
                    wm = WildcardMode.Extends;
                    break;
                case SUPER:
                    jj_consume_token(SUPER);
                    wm = WildcardMode.Super;
                    break;
                default:
                    jj_la1[93] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
                }
                t = Type();
                break;
            default:
                jj_la1[94] = jj_gen;
            }
            break;
        default:
            jj_la1[95] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        setPostfixInfo(result);
        result.setWildcardMode(wm);
        result.setTypeReference(t);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    /*
     * ASTList<UncollatedReferenceQualifier> NameList() : { ASTList<UncollatedReferenceQualifier>
     * result = new ASTArrayList<UncollatedReferenceQualifier>(); UncollatedReferenceQualifier qn; }
     * { qn = Name() { result.add(qn); } ( "," qn = Name() { result.add(qn); } )* { return result; }
     * }
     */
    static final public ASTList<UncollatedReferenceQualifier> TypedNameList()
            throws ParseException {
        ASTList<UncollatedReferenceQualifier> result =
            new ASTArrayList<>();
        UncollatedReferenceQualifier qn;
        qn = TypedName();
        result.add(qn);
        label_51: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case COMMA:
                break;
            default:
                jj_la1[96] = jj_gen;
                break label_51;
            }
            jj_consume_token(COMMA);
            qn = TypedName();
            result.add(qn);
        }
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    /*
     * Expression syntax follows.
     */
    static final public Expression Expression() throws ParseException {
        Expression result;
        Expression expr;
        Assignment op;
        ASTList<Expression> leftRight = new ASTArrayList<>();
        result = ConditionalExpression();
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case ASSIGN:
        case PLUSASSIGN:
        case MINUSASSIGN:
        case STARASSIGN:
        case SLASHASSIGN:
        case ANDASSIGN:
        case ORASSIGN:
        case XORASSIGN:
        case REMASSIGN:
        case LSHIFTASSIGN:
        case RSIGNEDSHIFTASSIGN:
        case RUNSIGNEDSHIFTASSIGN:
            op = AssignmentOperator();
            expr = Expression();
            leftRight.add(result);
            leftRight.add(expr);
            op.setArguments(leftRight);
            result = op;
            break;
        default:
            jj_la1[97] = jj_gen;
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Assignment AssignmentOperator() throws ParseException {
        Assignment result;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case ASSIGN:
            jj_consume_token(ASSIGN);
            result = factory.createCopyAssignment();
            break;
        case STARASSIGN:
            jj_consume_token(STARASSIGN);
            result = factory.createTimesAssignment();
            break;
        case SLASHASSIGN:
            jj_consume_token(SLASHASSIGN);
            result = factory.createDivideAssignment();
            break;
        case REMASSIGN:
            jj_consume_token(REMASSIGN);
            result = factory.createModuloAssignment();
            break;
        case PLUSASSIGN:
            jj_consume_token(PLUSASSIGN);
            result = factory.createPlusAssignment();
            break;
        case MINUSASSIGN:
            jj_consume_token(MINUSASSIGN);
            result = factory.createMinusAssignment();
            break;
        case LSHIFTASSIGN:
            jj_consume_token(LSHIFTASSIGN);
            result = factory.createShiftLeftAssignment();
            break;
        case RSIGNEDSHIFTASSIGN:
            jj_consume_token(RSIGNEDSHIFTASSIGN);
            result = factory.createShiftRightAssignment();
            break;
        case RUNSIGNEDSHIFTASSIGN:
            jj_consume_token(RUNSIGNEDSHIFTASSIGN);
            result = factory.createUnsignedShiftRightAssignment();
            break;
        case ANDASSIGN:
            jj_consume_token(ANDASSIGN);
            result = factory.createBinaryAndAssignment();
            break;
        case XORASSIGN:
            jj_consume_token(XORASSIGN);
            result = factory.createBinaryXOrAssignment();
            break;
        case ORASSIGN:
            jj_consume_token(ORASSIGN);
            result = factory.createBinaryOrAssignment();
            break;
        default:
            jj_la1[98] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        setPostfixInfo(result);
        setPrefixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Expression ConditionalExpression() throws ParseException {
        Expression result;
        Expression expr1;
        Expression expr2;
        Operator op;
        result = ConditionalOrExpression();
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case HOOK:
            jj_consume_token(HOOK);
            op = factory.createConditional();
            setPrefixInfo(op);
            expr1 = Expression();
            jj_consume_token(COLON);
            expr2 = ConditionalExpression();
            ASTList<Expression> args = new ASTArrayList<>(3);
            args.add(result);
            args.add(expr1);
            args.add(expr2);
            op.setArguments(args);
            result = op;
            break;
        default:
            jj_la1[99] = jj_gen;
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Expression ConditionalOrExpression() throws ParseException {
        Expression result;
        Expression expr;
        Operator op;
        result = ConditionalAndExpression();
        label_52: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case SC_OR:
                break;
            default:
                jj_la1[100] = jj_gen;
                break label_52;
            }
            jj_consume_token(SC_OR);
            op = factory.createLogicalOr();
            setPrefixInfo(op);
            expr = ConditionalAndExpression();
            ASTList<Expression> args = new ASTArrayList<>(2);
            args.add(result);
            args.add(expr);
            op.setArguments(args);
            result = op;
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Expression ConditionalAndExpression() throws ParseException {
        Expression result;
        Expression expr;
        Operator op;
        result = InclusiveOrExpression();
        label_53: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case SC_AND:
                break;
            default:
                jj_la1[101] = jj_gen;
                break label_53;
            }
            jj_consume_token(SC_AND);
            op = factory.createLogicalAnd();
            setPrefixInfo(op);
            expr = InclusiveOrExpression();
            ASTList<Expression> args = new ASTArrayList<>(2);
            args.add(result);
            args.add(expr);
            op.setArguments(args);
            result = op;
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Expression InclusiveOrExpression() throws ParseException {
        Expression result;
        Expression expr;
        Operator op;
        result = ExclusiveOrExpression();
        label_54: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case BIT_OR:
                break;
            default:
                jj_la1[102] = jj_gen;
                break label_54;
            }
            jj_consume_token(BIT_OR);
            op = factory.createBinaryOr();
            setPrefixInfo(op);
            expr = ExclusiveOrExpression();
            ASTList<Expression> args = new ASTArrayList<>(2);
            args.add(result);
            args.add(expr);
            op.setArguments(args);
            result = op;
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Expression ExclusiveOrExpression() throws ParseException {
        Expression result;
        Expression expr;
        Operator op;
        result = AndExpression();
        label_55: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case XOR:
                break;
            default:
                jj_la1[103] = jj_gen;
                break label_55;
            }
            jj_consume_token(XOR);
            op = factory.createBinaryXOr();
            setPrefixInfo(op);
            expr = AndExpression();
            ASTList<Expression> args = new ASTArrayList<>(2);
            args.add(result);
            args.add(expr);
            op.setArguments(args);
            result = op;
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Expression AndExpression() throws ParseException {
        Expression result;
        Expression expr;
        Operator op;
        result = EqualityExpression();
        label_56: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case BIT_AND:
                break;
            default:
                jj_la1[104] = jj_gen;
                break label_56;
            }
            jj_consume_token(BIT_AND);
            op = factory.createBinaryAnd();
            setPrefixInfo(op);
            expr = EqualityExpression();
            ASTList<Expression> args = new ASTArrayList<>(2);
            args.add(result);
            args.add(expr);
            op.setArguments(args);
            result = op;
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Expression EqualityExpression() throws ParseException {
        Expression result;
        Expression expr;
        Operator cmp;
        result = InstanceOfExpression();
        label_57: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case EQ:
            case NE:
                break;
            default:
                jj_la1[105] = jj_gen;
                break label_57;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case EQ:
                jj_consume_token(EQ);
                cmp = factory.createEquals();
                setPrefixInfo(cmp);
                break;
            case NE:
                jj_consume_token(NE);
                cmp = factory.createNotEquals();
                setPrefixInfo(cmp);
                break;
            default:
                jj_la1[106] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
            expr = InstanceOfExpression();
            ASTList<Expression> args = new ASTArrayList<>(2);
            args.add(result);
            args.add(expr);
            cmp.setArguments(args);
            result = cmp;
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Expression InstanceOfExpression() throws ParseException {
        Expression result;
        TypeReference tr;
        result = RelationalExpression();
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case INSTANCEOF:
            jj_consume_token(INSTANCEOF);
            tr = Type();
            result = factory.createInstanceof(result, tr);
            setPrefixInfo(result);
            break;
        default:
            jj_la1[107] = jj_gen;
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Expression RelationalExpression() throws ParseException {
        Expression result;
        Operator cmp;
        Expression expr;
        result = ShiftExpression();
        label_58: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case LT:
            case LE:
            case GE:
            case GT:
                break;
            default:
                jj_la1[108] = jj_gen;
                break label_58;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case LT:
                jj_consume_token(LT);
                cmp = factory.createLessThan();
                setPrefixInfo(cmp);
                break;
            case GT:
                jj_consume_token(GT);
                cmp = factory.createGreaterThan();
                setPrefixInfo(cmp);
                break;
            case LE:
                jj_consume_token(LE);
                cmp = factory.createLessOrEquals();
                setPrefixInfo(cmp);
                break;
            case GE:
                jj_consume_token(GE);
                cmp = factory.createGreaterOrEquals();
                setPrefixInfo(cmp);
                break;
            default:
                jj_la1[109] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
            expr = ShiftExpression();
            ASTList<Expression> args = new ASTArrayList<>(2);
            args.add(result);
            args.add(expr);
            cmp.setArguments(args);
            result = cmp;
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Expression ShiftExpression() throws ParseException {
        Expression result;
        Operator shift;
        Expression expr;
        result = AdditiveExpression();
        while (true) {
            if (jj_2_36(1)) {
            } else {
                break;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case LSHIFT:
                jj_consume_token(LSHIFT);
                shift = factory.createShiftLeft();
                setPrefixInfo(shift);
                break;
            default:
                jj_la1[110] = jj_gen;
                if (jj_2_37(1)) {
                    RSIGNEDSHIFT();
                    shift = factory.createShiftRight();
                    setPrefixInfo(shift);
                } else if (jj_2_38(1)) {
                    RUNSIGNEDSHIFT();
                    shift = factory.createUnsignedShiftRight();
                    setPrefixInfo(shift);
                } else {
                    jj_consume_token(-1);
                    throw new ParseException();
                }
            }
            expr = AdditiveExpression();
            ASTList<Expression> args = new ASTArrayList<>(2);
            args.add(result);
            args.add(expr);
            shift.setArguments(args);
            result = shift;
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Expression AdditiveExpression() throws ParseException {
        Expression result;
        Operator add;
        Expression expr;
        result = MultiplicativeExpression();
        label_60: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case PLUS:
            case MINUS:
                break;
            default:
                jj_la1[111] = jj_gen;
                break label_60;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case PLUS:
                jj_consume_token(PLUS);
                add = factory.createPlus();
                setPrefixInfo(add);
                break;
            case MINUS:
                jj_consume_token(MINUS);
                add = factory.createMinus();
                setPrefixInfo(add);
                break;
            default:
                jj_la1[112] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
            expr = MultiplicativeExpression();
            ASTList<Expression> args = new ASTArrayList<>(2);
            args.add(result);
            args.add(expr);
            add.setArguments(args);
            result = add;
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Expression MultiplicativeExpression() throws ParseException {
        Expression result = null;
        Operator mult = null;
        Expression expr;
        result = UnaryExpression();
        label_61: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case STAR:
            case SLASH:
            case REM:
                break;
            default:
                jj_la1[113] = jj_gen;
                break label_61;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case STAR:
                jj_consume_token(STAR);
                mult = factory.createTimes();
                setPrefixInfo(mult);
                break;
            case SLASH:
                jj_consume_token(SLASH);
                mult = factory.createDivide();
                setPrefixInfo(mult);
                break;
            case REM:
                jj_consume_token(REM);
                mult = factory.createModulo();
                setPrefixInfo(mult);
                break;
            default:
                jj_la1[114] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
            expr = UnaryExpression();
            ASTList<Expression> args = new ASTArrayList<>(2);
            args.add(result);
            args.add(expr);
            mult.setArguments(args);
            result = mult;
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Expression UnaryExpression() throws ParseException {
        Expression result;
        Expression expr;
        boolean negative = false;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case PLUS:
        case MINUS:
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case PLUS:
                jj_consume_token(PLUS);
                result = factory.createPositive();
                setPrefixInfo(result);
                break;
            case MINUS:
                jj_consume_token(MINUS);
                result = factory.createNegative();
                setPrefixInfo(result);
                break;
            default:
                jj_la1[115] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
            expr = UnaryExpression();
            ((Operator) result).setArguments(new ASTArrayList<>(expr));
            break;
        case INCR:
            result = PreIncrementExpression();
            break;
        case DECR:
            result = PreDecrementExpression();
            break;
        case BOOLEAN:
        case BYTE:
        case CHAR:
        case DOUBLE:
        case FALSE:
        case FLOAT:
        case INT:
        case LONG:
        case NEW:
        case NULL:
        case SHORT:
        case SUPER:
        case THIS:
        case TRUE:
        case VOID:
        case INTEGER_LITERAL:
        case FLOATING_POINT_LITERAL:
        case CHARACTER_LITERAL:
        case STRING_LITERAL:
        case IDENTIFIER:
        case LPAREN:
        case BANG:
        case TILDE:
            result = UnaryExpressionNotPlusMinus();
            break;
        default:
            jj_la1[116] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public PreIncrement PreIncrementExpression() throws ParseException {
        PreIncrement result;
        Expression expr;
        jj_consume_token(INCR);
        result = factory.createPreIncrement();
        setPrefixInfo(result);
        expr = PrimaryExpression();
        result.setArguments(new ASTArrayList<>(expr));
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public PreDecrement PreDecrementExpression() throws ParseException {
        PreDecrement result;
        Expression expr;
        jj_consume_token(DECR);
        result = factory.createPreDecrement();
        setPrefixInfo(result);
        expr = PrimaryExpression();
        result.setArguments(new ASTArrayList<>(expr));
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Expression UnaryExpressionNotPlusMinus() throws ParseException {
        Expression result;
        Expression expr;
        boolean not = false;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case BANG:
        case TILDE:
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case TILDE:
                jj_consume_token(TILDE);
                result = factory.createBinaryNot();
                setPrefixInfo(result);
                break;
            case BANG:
                jj_consume_token(BANG);
                result = factory.createLogicalNot();
                setPrefixInfo(result);
                break;
            default:
                jj_la1[117] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
            expr = UnaryExpression();
            ((Operator) result).setArguments(new ASTArrayList<>(expr));
            break;
        default:
            jj_la1[118] = jj_gen;
            if (jj_2_39(2147483647)) {
                result = CastExpression();
            } else {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case BOOLEAN:
                case BYTE:
                case CHAR:
                case DOUBLE:
                case FALSE:
                case FLOAT:
                case INT:
                case LONG:
                case NEW:
                case NULL:
                case SHORT:
                case SUPER:
                case THIS:
                case TRUE:
                case VOID:
                case INTEGER_LITERAL:
                case FLOATING_POINT_LITERAL:
                case CHARACTER_LITERAL:
                case STRING_LITERAL:
                case IDENTIFIER:
                case LPAREN:
                    result = PostfixExpression();
                    break;
                default:
                    jj_la1[119] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
                }
            }
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    // This production is to determine lookahead only. The LOOKAHEAD specifications
    // below are not used, but they are there just to indicate that we know about
    // this.
    static final public void CastLookahead() throws ParseException {
        if (jj_2_40(2147483647)) {
            jj_consume_token(LPAREN);
            PrimitiveType();
            label_62: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case LBRACKET:
                    break;
                default:
                    jj_la1[120] = jj_gen;
                    break label_62;
                }
                jj_consume_token(LBRACKET);
                jj_consume_token(RBRACKET);
            }
            jj_consume_token(RPAREN);
        } else if (jj_2_41(2147483647)) {
            jj_consume_token(LPAREN);
            TypedName();
            jj_consume_token(LBRACKET);
            jj_consume_token(RBRACKET);
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case LPAREN:
                jj_consume_token(LPAREN);
                TypedName();
                jj_consume_token(RPAREN);
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case TILDE:
                    jj_consume_token(TILDE);
                    break;
                case BANG:
                    jj_consume_token(BANG);
                    break;
                case LPAREN:
                    jj_consume_token(LPAREN);
                    break;
                case IDENTIFIER:
                    jj_consume_token(IDENTIFIER);
                    break;
                case THIS:
                    jj_consume_token(THIS);
                    break;
                case SUPER:
                    jj_consume_token(SUPER);
                    break;
                case NEW:
                    jj_consume_token(NEW);
                    break;
                case FALSE:
                case NULL:
                case TRUE:
                case INTEGER_LITERAL:
                case FLOATING_POINT_LITERAL:
                case CHARACTER_LITERAL:
                case STRING_LITERAL:
                    Literal();
                    break;
                default:
                    jj_la1[121] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
                }
                break;
            default:
                jj_la1[122] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
        }
    }

    static final public Expression PostfixExpression() throws ParseException {
        Expression result;
        result = PrimaryExpression();
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case INCR:
        case DECR:
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case INCR:
                jj_consume_token(INCR);
                result = factory.createPostIncrement(result);
                setPrefixInfo(result);
                break;
            case DECR:
                jj_consume_token(DECR);
                result = factory.createPostDecrement(result);
                setPrefixInfo(result);
                break;
            default:
                jj_la1[123] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
            break;
        default:
            jj_la1[124] = jj_gen;
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public TypeCast CastExpression() throws ParseException {
        TypeCast result = null;
        TypeReference tr;
        Expression expr;
        result = factory.createTypeCast();
        if (jj_2_42(2147483647)) {
            jj_consume_token(LPAREN);
            setPrefixInfo(result);
            tr = Type();
            jj_consume_token(RPAREN);
            expr = UnaryExpression();
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case LPAREN:
                jj_consume_token(LPAREN);
                setPrefixInfo(result);
                tr = Type();
                jj_consume_token(RPAREN);
                expr = UnaryExpressionNotPlusMinus();
                break;
            default:
                jj_la1[125] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
        }
        result.setTypeReference(tr);
        result.setArguments(new ASTArrayList<>(expr));
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Expression PrimaryExpression() throws ParseException {
        Expression result = null;
        ReferencePrefix tmpResult = null;
        prefix = PrimaryPrefix();
        // create initial AST construct from prefix only
        switch (prefix.type) {
        case PrimaryPrefixReturnValue.LITERAL:
            if (prefix.literal instanceof StringLiteral) {
                tmpResult = (StringLiteral) prefix.literal;
            } else {
                result = prefix.literal;
                setPostfixInfo(result);
                {
                    if (true) {
                        return result;
                    }
                }
                // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
            }
            break;
        case PrimaryPrefixReturnValue.THIS:
            tmpResult = factory.createThisReference();
            setPrefixInfo(tmpResult);
            setPostfixInfo(tmpResult);
            break;
        case PrimaryPrefixReturnValue.SUPER_MEMBER:
            tmpResult = prefix.name;
            break;
        case PrimaryPrefixReturnValue.PARENTHESIZED_EXPR:
            tmpResult = (ParenthesizedExpression) prefix.expr;
            break;
        case PrimaryPrefixReturnValue.ALLOCATION_EXPR:
            tmpResult = (ReferencePrefix) prefix.expr;
            break;
        case PrimaryPrefixReturnValue.CLASS_REF:
            tmpResult = factory.createMetaClassReference(prefix.typeref);
            setPrefixInfo(tmpResult);
            setPostfixInfo(tmpResult);
            break;
        case PrimaryPrefixReturnValue.QUALIFIED_NAME:
            tmpResult = prefix.name;
            break;
        default: {
            if (true) {
                throw new ParseException("Unknown prefix");
            }
        }
        }
        while (true) {
            if (jj_2_43(2)) {
            } else {
                break;
            }
            suffix = PrimarySuffix();
            switch (suffix.type) {
            case PrimarySuffixReturnValue.THIS:
                // the prefix MUST be a type expression!!!!!
                // we currently only create UncollatedReferenceQualifiers
                if (tmpResult instanceof TypeReference) {
                    tmpResult = factory.createThisReference((TypeReference) tmpResult);
                    setPrefixInfo(tmpResult);
                    setPostfixInfo(tmpResult);
                } else if (tmpResult instanceof UncollatedReferenceQualifier) {
                    tmpResult = factory.createThisReference(
                        ((UncollatedReferenceQualifier) tmpResult).toTypeReference());
                    setPrefixInfo(tmpResult);
                    setPostfixInfo(tmpResult);
                } else {
                    {
                        if (true) {
                            throw new ParseException("No type as prefix of `this'");
                        }
                    }
                }
                break;
            case PrimarySuffixReturnValue.SUPER:
                // the prefix MUST be a type expression!!!!!
                // we currently only create UncollatedReferenceQualifiers
                if (tmpResult instanceof TypeReference) {
                    tmpResult = factory.createSuperReference(tmpResult);
                    setPrefixInfo(tmpResult);
                    setPostfixInfo(tmpResult);
                } else if (tmpResult instanceof UncollatedReferenceQualifier) {
                    tmpResult = factory.createSuperReference(
                        ((UncollatedReferenceQualifier) tmpResult).toTypeReference());
                    setPrefixInfo(tmpResult);
                    setPostfixInfo(tmpResult);
                } else if (tmpResult instanceof ThisReference) {
                    tmpResult = factory.createSuperReference(tmpResult);
                    setPrefixInfo(tmpResult);
                    setPostfixInfo(tmpResult);
                } else {
                    {
                        if (true) {
                            throw new ParseException(
                                "No type as prefix of `super', was " + tmpResult.getClass());
                        }
                    }
                }
                break;
            case PrimarySuffixReturnValue.ALLOCATION_EXPR:
                if (suffix.expr instanceof New) {
                    ((New) suffix.expr).setReferencePrefix(tmpResult);
                    tmpResult = (New) suffix.expr;
                } else {
                    {
                        if (true) {
                            throw new ParseException("Allocation without new?");
                        }
                    }
                }
                break;
            case PrimarySuffixReturnValue.INDEX_EXPR:
                if (tmpResult instanceof UncollatedReferenceQualifier
                        || tmpResult instanceof MethodReference
                        || tmpResult instanceof ParenthesizedExpression
                        || tmpResult instanceof VariableReference) {
                    // Now we know that this is an array reference
                    ASTList<Expression> indicees = new ASTArrayList<>(1);
                    indicees.add(suffix.expr);
                    tmpResult = factory.createArrayReference(tmpResult, indicees);
                    setPrefixInfo(tmpResult);
                    setPostfixInfo(tmpResult);
                } else if (tmpResult instanceof ArrayReference) {
                    // we need to add another access dimension
                    ((ArrayReference) tmpResult).getDimensionExpressions().add(suffix.expr);
                } else {
                    {
                        if (true) {
                            throw new ParseException(
                                "Bad index context - " + tmpResult.getClass().getName() + "?!");
                        }
                    }
                    /*
                     * e.g. StringLiteral, TypeReference, NewArray (would have to be in
                     * parentheses), SuperReference, ...
                     */
                }
                break;
            case PrimarySuffixReturnValue.IDENTIFIER:
                tmpResult = factory.createUncollatedReferenceQualifier(tmpResult, suffix.id);
                ((UncollatedReferenceQualifier) tmpResult).setTypeArguments(suffix.typeArgs);
                suffix.typeArgs = null;
                setPrefixInfo(tmpResult);
                setPostfixInfo(tmpResult);
                break;
            case PrimarySuffixReturnValue.ARGUMENTS:
                // method call -determine the kind of method
                if (tmpResult instanceof UncollatedReferenceQualifier) {
                    // this is a normal method call
                    tmpResult = factory.createMethodReference(
                        ((UncollatedReferenceQualifier) tmpResult).getReferencePrefix(),
                        ((UncollatedReferenceQualifier) tmpResult).getIdentifier(), suffix.args,
                        ((UncollatedReferenceQualifier) tmpResult).getTypeArguments());

                    setPrefixInfo(tmpResult);
                    setPostfixInfo(tmpResult);
                } else {
                    {
                        if (true) {
                            throw new ParseException("Arguments without method name?");
                        }
                    }
                }
                break;
            default: {
                if (true) {
                    throw new ParseException("Unknown primary suffix type");
                }
            }
            }
        }
        if (tmpResult instanceof UncollatedReferenceQualifier) {
            result = (UncollatedReferenceQualifier) tmpResult;
            // should be a FieldReference?
        } else {
            result = (Expression) tmpResult;
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public PrimaryPrefixReturnValue PrimaryPrefix() throws ParseException {
        // reuses global prefix field
        Literal lit;
        Expression expr;
        TypeReference tr;
        UncollatedReferenceQualifier qn;
        SuperReference supRef = null;
        ParenthesizedExpression parExpr = null;
        Identifier id = null;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case FALSE:
        case NULL:
        case TRUE:
        case INTEGER_LITERAL:
        case FLOATING_POINT_LITERAL:
        case CHARACTER_LITERAL:
        case STRING_LITERAL:
            // LOOKAHEAD(NonWildcardTypeArguments() "this" Arguments())
            // NonWildcardTypeArguments() "this" /* Arguments() is a mandatory suffix here!*/
            // {
            // prefix.type = prefix.THIS;
            // System.err.println("Ignoring NonWildcardTypeArguments!");
            // }
            // |
            lit = Literal();
            prefix.type = PrimaryPrefixReturnValue.LITERAL;
            prefix.literal = lit;
            break;
        case THIS:
            jj_consume_token(THIS);
            prefix.type = PrimaryPrefixReturnValue.THIS;
            break;
        case SUPER:
            jj_consume_token(SUPER);
            supRef = factory.createSuperReference();
            setPrefixInfo(supRef);
            setPostfixInfo(supRef);
            jj_consume_token(DOT);
            jj_consume_token(IDENTIFIER);
            id = factory.createIdentifier(token.image);
            setPrefixInfo(id);
            setPostfixInfo(id);
            prefix.name = factory.createUncollatedReferenceQualifier(supRef, id);
            prefix.type = PrimaryPrefixReturnValue.SUPER_MEMBER;
            break;
        case LPAREN:
            jj_consume_token(LPAREN);
            parExpr = factory.createParenthesizedExpression();
            setPrefixInfo(parExpr);
            expr = Expression();
            jj_consume_token(RPAREN);
            setPostfixInfo(parExpr);
            parExpr.setArguments(new ASTArrayList<>(expr));
            prefix.expr = parExpr;
            prefix.type = PrimaryPrefixReturnValue.PARENTHESIZED_EXPR;
            break;
        case NEW:
            expr = AllocationExpression();
            prefix.type = PrimaryPrefixReturnValue.ALLOCATION_EXPR;
            prefix.expr = expr;
            break;
        default:
            jj_la1[126] = jj_gen;
            if (jj_2_44(2147483647)) {
                tr = ResultType();
                jj_consume_token(DOT);
                jj_consume_token(CLASS);
                prefix.type = PrimaryPrefixReturnValue.CLASS_REF;
                prefix.typeref = tr;
            } else {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case IDENTIFIER:
                    qn = Name();
                    prefix.type = PrimaryPrefixReturnValue.QUALIFIED_NAME;
                    prefix.name = qn;
                    break;
                default:
                    jj_la1[127] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
                }
            }
        }
        {
            if (true) {
                return prefix;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public PrimarySuffixReturnValue PrimarySuffix() throws ParseException {
        // reuses global suffix field
        Expression expr;
        ASTList<Expression> args;
        Identifier id;
        ASTList<TypeArgumentDeclaration> typeArgs;
        if (jj_2_45(2)) {
            jj_consume_token(DOT);
            jj_consume_token(THIS);
            suffix.type = PrimarySuffixReturnValue.THIS;
        } else if (jj_2_46(2) && (isSuperAllowed())) {
            jj_consume_token(DOT);
            jj_consume_token(SUPER);
            suffix.type = PrimarySuffixReturnValue.SUPER;
        } else if (jj_2_47(2)) {
            jj_consume_token(DOT);
            expr = AllocationExpression();
            suffix.type = PrimarySuffixReturnValue.ALLOCATION_EXPR;
            suffix.expr = expr;
        } else if (jj_2_48(3)) {
            jj_consume_token(DOT);
            suffix.typeArgs = NonWildcardTypeArguments();
            jj_consume_token(IDENTIFIER);
            suffix.type = PrimarySuffixReturnValue.IDENTIFIER;
            suffix.id = factory.createIdentifier(token.image);
            setPrefixInfo(suffix.id);
            setPostfixInfo(suffix.id);
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case LBRACKET:
                jj_consume_token(LBRACKET);
                expr = Expression();
                jj_consume_token(RBRACKET);
                suffix.type = PrimarySuffixReturnValue.INDEX_EXPR;
                suffix.expr = expr;
                break;
            case DOT:
                jj_consume_token(DOT);
                jj_consume_token(IDENTIFIER);
                suffix.type = PrimarySuffixReturnValue.IDENTIFIER;
                suffix.id = factory.createIdentifier(token.image);
                setPrefixInfo(suffix.id);
                setPostfixInfo(suffix.id);
                break;
            case LPAREN:
                args = Arguments();
                suffix.type = PrimarySuffixReturnValue.ARGUMENTS;
                suffix.args = args;
                break;
            default:
                jj_la1[128] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
        }
        {
            if (true) {
                return suffix;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Literal Literal() throws ParseException {
        Literal result;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case INTEGER_LITERAL:
            jj_consume_token(INTEGER_LITERAL);
            if (token.image.endsWith("L") || token.image.endsWith("l")) {
                result = factory.createLongLiteral(token.image);
            } else {
                result = factory.createIntLiteral(token.image);
            }
            setPrefixInfo(result);
            break;
        case FLOATING_POINT_LITERAL:
            jj_consume_token(FLOATING_POINT_LITERAL);
            if (token.image.endsWith("F") || token.image.endsWith("f")) {
                result = factory.createFloatLiteral(token.image);
            } else {
                result = factory.createDoubleLiteral(token.image);
            }
            setPrefixInfo(result);
            break;
        case CHARACTER_LITERAL:
            jj_consume_token(CHARACTER_LITERAL);
            result = factory.createCharLiteral(token.image);
            setPrefixInfo(result);
            break;
        case STRING_LITERAL:
            jj_consume_token(STRING_LITERAL);
            result = factory.createStringLiteral(token.image);
            setPrefixInfo(result);
            break;
        case FALSE:
        case TRUE:
            result = BooleanLiteral();
            break;
        case NULL:
            result = NullLiteral();
            break;
        default:
            jj_la1[129] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public BooleanLiteral BooleanLiteral() throws ParseException {
        BooleanLiteral result;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case TRUE:
            jj_consume_token(TRUE);
            result = factory.createBooleanLiteral(true);
            break;
        case FALSE:
            jj_consume_token(FALSE);
            result = factory.createBooleanLiteral(false);
            break;
        default:
            jj_la1[130] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        setPrefixInfo(result);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public NullLiteral NullLiteral() throws ParseException {
        NullLiteral result;
        jj_consume_token(NULL);
        result = factory.createNullLiteral();
        setPrefixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public ASTList<Expression> Arguments() throws ParseException {
        ASTList<Expression> result = null;
        jj_consume_token(LPAREN);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case BOOLEAN:
        case BYTE:
        case CHAR:
        case DOUBLE:
        case FALSE:
        case FLOAT:
        case INT:
        case LONG:
        case NEW:
        case NULL:
        case SHORT:
        case SUPER:
        case THIS:
        case TRUE:
        case VOID:
        case INTEGER_LITERAL:
        case FLOATING_POINT_LITERAL:
        case CHARACTER_LITERAL:
        case STRING_LITERAL:
        case IDENTIFIER:
        case LPAREN:
        case BANG:
        case TILDE:
        case INCR:
        case DECR:
        case PLUS:
        case MINUS:
            result = ArgumentList();
            break;
        default:
            jj_la1[131] = jj_gen;
        }
        jj_consume_token(RPAREN);
        // !!! should set end coordinates to parent, possibly
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public ASTList<Expression> ArgumentList() throws ParseException {
        ASTList<Expression> result = new ASTArrayList<>();
        Expression expr;
        expr = Expression();
        result.add(expr);
        while (true) {
            if (jj_2_49(2147483647)) {
            } else {
                break;
            }
            jj_consume_token(COMMA);
            expr = Expression();
            result.add(expr);
        }
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public TypeOperator AllocationExpression() throws ParseException {
        UncollatedReferenceQualifier qn;
        TypeOperator result;
        TypeReference tr;
        ASTList<Expression> args;
        ASTList<MemberDeclaration> body = null;
        ClassDeclaration cd = null;
        NewArray na;
        ASTList<TypeArgumentDeclaration> typeArgs;
        if (jj_2_50(2)) {
            jj_consume_token(NEW);
            na = factory.createNewArray();
            setPrefixInfo(na);
            tr = PrimitiveType();
            na.setTypeReference(tr);
            result = ArrayDimsAndInits(na);
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case NEW:
                jj_consume_token(NEW);
                result = factory.createNew();
                setPrefixInfo(result);
                qn = TypedName();
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case LT:
                    typeArgs = NonWildcardTypeArguments();
                    qn.setTypeArguments(typeArgs);
                    break;
                default:
                    jj_la1[132] = jj_gen;
                }
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case LPAREN:
                    args = Arguments();
                    switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case LBRACE:
                        cd = factory.createClassDeclaration();
                        setPrefixInfo(cd);
                        body = ClassBody();
                        cd.setMembers(body);
                        setPostfixInfo(cd);
                        break;
                    default:
                        jj_la1[133] = jj_gen;
                    }
                    result.setTypeReference(qn.toTypeReference());
                    result.setArguments(args);
                    if (cd != null) {
                        ((New) result).setClassDeclaration(cd);
                    }
                    break;
                case LBRACKET:
                    na = factory.createNewArray();
                    copyPrefixInfo(result, na);
                    na.setTypeReference(qn.toTypeReference());
                    result = ArrayDimsAndInits(na);
                    break;
                default:
                    jj_la1[134] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
                }
                break;
            default:
                jj_la1[135] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    /*
     * The third LOOKAHEAD specification below is to parse to PrimarySuffix if there is an
     * expression between the "[...]".
     */
    static final public NewArray ArrayDimsAndInits(NewArray result) throws ParseException {
        int dimensions = 0;
        Expression expr;
        ASTList<Expression> sizes = null;
        ArrayInitializer init = null;
        if (jj_2_53(2)) {
            while (true) {
                jj_consume_token(LBRACKET);
                expr = Expression();
                jj_consume_token(RBRACKET);
                sizes = (sizes == null) ? new ASTArrayList<>() : sizes;
                sizes.add(expr);
                dimensions++;
                if (jj_2_51(2)) {
                } else {
                    break;
                }
            }
            while (true) {
                if (jj_2_52(2)) {
                } else {
                    break;
                }
                jj_consume_token(LBRACKET);
                jj_consume_token(RBRACKET);
                dimensions++;
            }
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case LBRACKET:
                label_67: while (true) {
                    jj_consume_token(LBRACKET);
                    jj_consume_token(RBRACKET);
                    dimensions++;
                    switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case LBRACKET:
                        break;
                    default:
                        jj_la1[136] = jj_gen;
                        break label_67;
                    }
                }
                init = ArrayInitializer();
                break;
            default:
                jj_la1[137] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
        }
        // setPrefixInfo(result);
        result.setDimensions(dimensions);
        if (sizes != null) {
            result.setArguments(sizes);
        }
        result.setArrayInitializer(init);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    /*
     * Statement syntax follows.
     */
    static final public Statement Statement() throws ParseException {
        Statement result = null;
        Expression expr;
        if (jj_2_54(2)) {
            result = LabeledStatement();
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case LBRACE:
                result = Block();
                break;
            case SEMICOLON:
                result = EmptyStatement();
                break;
            case BOOLEAN:
            case BYTE:
            case CHAR:
            case DOUBLE:
            case FALSE:
            case FLOAT:
            case INT:
            case LONG:
            case NEW:
            case NULL:
            case SHORT:
            case SUPER:
            case THIS:
            case TRUE:
            case VOID:
            case INTEGER_LITERAL:
            case FLOATING_POINT_LITERAL:
            case CHARACTER_LITERAL:
            case STRING_LITERAL:
            case IDENTIFIER:
            case LPAREN:
            case INCR:
            case DECR:
                expr = StatementExpression();
                jj_consume_token(SEMICOLON);
                try {
                    result = (ExpressionStatement) expr;
                } catch (ClassCastException cce) {
                    // this is a semantical error!!!
                    {
                        if (true) {
                            throw new ParseException(
                                "Class cast error: ExpressionStatement expected - found "
                                    + recoder.convenience.Format.toString("%c @%p %s", expr));
                        }
                    }
                }
                break;
            case SWITCH:
                result = SwitchStatement();
                break;
            case IF:
                result = IfStatement();
                break;
            case WHILE:
                result = WhileStatement();
                break;
            case DO:
                result = DoStatement();
                break;
            case FOR:
                result = ForStatement();
                break;
            case BREAK:
                result = BreakStatement();
                break;
            case CONTINUE:
                result = ContinueStatement();
                break;
            case RETURN:
                result = ReturnStatement();
                break;
            case THROW:
                result = ThrowStatement();
                break;
            case SYNCHRONIZED:
                result = SynchronizedStatement();
                break;
            case TRY:
                result = TryStatement();
                break;
            case ASSERT:
                result = AssertStatement();
                break;
            default:
                jj_la1[138] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public LabeledStatement LabeledStatement() throws ParseException {
        LabeledStatement result;
        Identifier id;
        Statement stat;
        jj_consume_token(IDENTIFIER);
        id = factory.createIdentifier(token.image);
        setPrefixInfo(id);
        setPostfixInfo(id);
        jj_consume_token(COLON);
        result = factory.createLabeledStatement();
        setPrefixInfo(result);
        result.setIdentifier(id);
        stat = Statement();
        result.setBody(stat);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public StatementBlock Block() throws ParseException {
        StatementBlock result;
        ASTList<Statement> sl = new ASTArrayList<>();
        Statement stat;
        jj_consume_token(LBRACE);
        result = factory.createStatementBlock();
        setPrefixInfo(result);
        label_68: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case ASSERT:
            case AT:
            case BOOLEAN:
            case BREAK:
            case BYTE:
            case CHAR:
            case CLASS:
            case CONTINUE:
            case DO:
            case DOUBLE:
            case FALSE:
            case FINAL:
            case FLOAT:
            case FOR:
            case IF:
            case INT:
            case LONG:
            case NEW:
            case NULL:
            case RETURN:
            case SHORT:
            case SUPER:
            case SWITCH:
            case SYNCHRONIZED:
            case THIS:
            case THROW:
            case TRUE:
            case TRY:
            case VOID:
            case WHILE:
            case INTEGER_LITERAL:
            case FLOATING_POINT_LITERAL:
            case CHARACTER_LITERAL:
            case STRING_LITERAL:
            case IDENTIFIER:
            case LPAREN:
            case LBRACE:
            case SEMICOLON:
            case INCR:
            case DECR:
                break;
            default:
                jj_la1[139] = jj_gen;
                break label_68;
            }
            stat = BlockStatement();
            sl.add(stat);
        }
        jj_consume_token(RBRACE);
        result.setBody(sl);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Statement BlockStatement() throws ParseException {
        Statement result;
        if (jj_2_55(2147483647)) {
            result = LocalVariableDeclaration();
            jj_consume_token(SEMICOLON);
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case ASSERT:
            case BOOLEAN:
            case BREAK:
            case BYTE:
            case CHAR:
            case CONTINUE:
            case DO:
            case DOUBLE:
            case FALSE:
            case FLOAT:
            case FOR:
            case IF:
            case INT:
            case LONG:
            case NEW:
            case NULL:
            case RETURN:
            case SHORT:
            case SUPER:
            case SWITCH:
            case SYNCHRONIZED:
            case THIS:
            case THROW:
            case TRUE:
            case TRY:
            case VOID:
            case WHILE:
            case INTEGER_LITERAL:
            case FLOATING_POINT_LITERAL:
            case CHARACTER_LITERAL:
            case STRING_LITERAL:
            case IDENTIFIER:
            case LPAREN:
            case LBRACE:
            case SEMICOLON:
            case INCR:
            case DECR:
                result = Statement();
                break;
            case CLASS:
                result = UnmodifiedClassDeclaration();
                break;
            default:
                jj_la1[140] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public LocalVariableDeclaration LocalVariableDeclaration() throws ParseException {
        LocalVariableDeclaration result;
        ASTList<VariableSpecification> vl = new ASTArrayList<>(1);
        TypeReference tr;
        VariableSpecification var;
        ASTArrayList<DeclarationSpecifier> declSpecs = new ASTArrayList<>();
        AnnotationUseSpecification annot;
        result = factory.createLocalVariableDeclaration();
        setPrefixInfo(result);
        label_69: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case AT:
                break;
            default:
                jj_la1[141] = jj_gen;
                break label_69;
            }
            annot = AnnotationUse();
            declSpecs.add(annot);
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case FINAL:
            jj_consume_token(FINAL);
            Final fi = factory.createFinal();
            setPrefixInfo(fi);
            setPostfixInfo(fi);
            declSpecs.add(fi);
            label_70: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case AT:
                    break;
                default:
                    jj_la1[142] = jj_gen;
                    break label_70;
                }
                annot = AnnotationUse();
                declSpecs.add(annot);
            }
            break;
        default:
            jj_la1[143] = jj_gen;
        }
        if (declSpecs.size() != 0) {
            result.setDeclarationSpecifiers(declSpecs);
        }
        tr = Type();
        var = VariableDeclarator(false);
        vl.add(var);
        label_71: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case COMMA:
                break;
            default:
                jj_la1[144] = jj_gen;
                break label_71;
            }
            jj_consume_token(COMMA);
            var = VariableDeclarator(false);
            vl.add(var);
        }
        result.setTypeReference(tr);
        result.setVariableSpecifications(vl);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public EmptyStatement EmptyStatement() throws ParseException {
        EmptyStatement result;
        jj_consume_token(SEMICOLON);
        result = factory.createEmptyStatement();
        setPrefixInfo(result);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Expression StatementExpression() throws ParseException {
        Expression result;
        Expression expr;
        Assignment op;
        ASTList<Expression> leftRight;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case INCR:
            result = PreIncrementExpression();
            break;
        case DECR:
            result = PreDecrementExpression();
            break;
        case BOOLEAN:
        case BYTE:
        case CHAR:
        case DOUBLE:
        case FALSE:
        case FLOAT:
        case INT:
        case LONG:
        case NEW:
        case NULL:
        case SHORT:
        case SUPER:
        case THIS:
        case TRUE:
        case VOID:
        case INTEGER_LITERAL:
        case FLOATING_POINT_LITERAL:
        case CHARACTER_LITERAL:
        case STRING_LITERAL:
        case IDENTIFIER:
        case LPAREN:
            result = PrimaryExpression();
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case ASSIGN:
            case INCR:
            case DECR:
            case PLUSASSIGN:
            case MINUSASSIGN:
            case STARASSIGN:
            case SLASHASSIGN:
            case ANDASSIGN:
            case ORASSIGN:
            case XORASSIGN:
            case REMASSIGN:
            case LSHIFTASSIGN:
            case RSIGNEDSHIFTASSIGN:
            case RUNSIGNEDSHIFTASSIGN:
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case INCR:
                    jj_consume_token(INCR);
                    result = factory.createPostIncrement(result);
                    setPrefixInfo(result);
                    break;
                case DECR:
                    jj_consume_token(DECR);
                    result = factory.createPostDecrement(result);
                    setPrefixInfo(result);
                    break;
                case ASSIGN:
                case PLUSASSIGN:
                case MINUSASSIGN:
                case STARASSIGN:
                case SLASHASSIGN:
                case ANDASSIGN:
                case ORASSIGN:
                case XORASSIGN:
                case REMASSIGN:
                case LSHIFTASSIGN:
                case RSIGNEDSHIFTASSIGN:
                case RUNSIGNEDSHIFTASSIGN:
                    op = AssignmentOperator();
                    expr = Expression();
                    leftRight = new ASTArrayList<>(2);
                    leftRight.add(result);
                    leftRight.add(expr);
                    op.setArguments(leftRight);
                    result = op;
                    break;
                default:
                    jj_la1[145] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
                }
                break;
            default:
                jj_la1[146] = jj_gen;
            }
            break;
        default:
            jj_la1[147] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Switch SwitchStatement() throws ParseException {
        Switch result;
        Expression expr;
        ASTList<Branch> branches = new ASTArrayList<>(2);
        Branch branch;
        ASTList<Statement> stats;
        Statement stat;
        jj_consume_token(SWITCH);
        result = factory.createSwitch();
        setPrefixInfo(result);
        jj_consume_token(LPAREN);
        expr = Expression();
        jj_consume_token(RPAREN);
        jj_consume_token(LBRACE);
        label_72: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case CASE:
            case _DEFAULT:
                break;
            default:
                jj_la1[148] = jj_gen;
                break label_72;
            }
            branch = SwitchLabel();
            stats = new ASTArrayList<>();
            label_73: while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case ASSERT:
                case AT:
                case BOOLEAN:
                case BREAK:
                case BYTE:
                case CHAR:
                case CLASS:
                case CONTINUE:
                case DO:
                case DOUBLE:
                case FALSE:
                case FINAL:
                case FLOAT:
                case FOR:
                case IF:
                case INT:
                case LONG:
                case NEW:
                case NULL:
                case RETURN:
                case SHORT:
                case SUPER:
                case SWITCH:
                case SYNCHRONIZED:
                case THIS:
                case THROW:
                case TRUE:
                case TRY:
                case VOID:
                case WHILE:
                case INTEGER_LITERAL:
                case FLOATING_POINT_LITERAL:
                case CHARACTER_LITERAL:
                case STRING_LITERAL:
                case IDENTIFIER:
                case LPAREN:
                case LBRACE:
                case SEMICOLON:
                case INCR:
                case DECR:
                    break;
                default:
                    jj_la1[149] = jj_gen;
                    break label_73;
                }
                stat = BlockStatement();
                stats.add(stat);
            }
            if (branch instanceof Case) {
                ((Case) branch).setBody(stats);
            } else {
                ((Default) branch).setBody(stats);
            }
            branches.add(branch);
        }
        jj_consume_token(RBRACE);
        result.setExpression(expr);
        result.setBranchList(branches);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Branch SwitchLabel() throws ParseException {
        Branch result;
        Expression expr;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case CASE:
            jj_consume_token(CASE);
            result = factory.createCase();
            setPrefixInfo(result);
            expr = Expression();
            jj_consume_token(COLON);
            ((Case) result).setExpression(expr);
            break;
        case _DEFAULT:
            jj_consume_token(_DEFAULT);
            result = factory.createDefault();
            setPrefixInfo(result);
            jj_consume_token(COLON);
            break;
        default:
            jj_la1[150] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Assert AssertStatement() throws ParseException {
        Assert result;
        Expression cond = null;
        Expression msg = null;
        jj_consume_token(ASSERT);
        result = factory.createAssert();
        setPrefixInfo(result);
        cond = Expression();
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case COLON:
            jj_consume_token(COLON);
            msg = Expression();
            break;
        default:
            jj_la1[151] = jj_gen;
        }
        jj_consume_token(SEMICOLON);
        result.setCondition(cond);
        result.setMessage(msg);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public If IfStatement() throws ParseException {
        If result;
        Expression cond;
        Then thenStat;
        Else elseStat = null;
        Statement trueStat;
        Statement falseStat = null;
        jj_consume_token(IF);
        result = factory.createIf();
        setPrefixInfo(result);
        jj_consume_token(LPAREN);
        cond = Expression();
        jj_consume_token(RPAREN);
        thenStat = factory.createThen();
        setPrefixInfo(thenStat);
        trueStat = Statement();
        thenStat.setBody(trueStat);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case ELSE:
            jj_consume_token(ELSE);
            elseStat = factory.createElse();
            setPrefixInfo(elseStat);
            falseStat = Statement();
            elseStat.setBody(falseStat);
            break;
        default:
            jj_la1[152] = jj_gen;
        }
        result.setExpression(cond);
        result.setThen(thenStat);
        if (elseStat != null) {
            result.setElse(elseStat);
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public While WhileStatement() throws ParseException {
        While result;
        Expression expr;
        Statement stat;
        jj_consume_token(WHILE);
        result = factory.createWhile();
        setPrefixInfo(result);
        jj_consume_token(LPAREN);
        expr = Expression();
        jj_consume_token(RPAREN);
        stat = Statement();
        result.setGuard(expr);
        result.setBody(stat);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Do DoStatement() throws ParseException {
        Do result;
        Expression expr;
        Statement stat;
        jj_consume_token(DO);
        result = factory.createDo();
        setPrefixInfo(result);
        stat = Statement();
        jj_consume_token(WHILE);
        jj_consume_token(LPAREN);
        expr = Expression();
        jj_consume_token(RPAREN);
        jj_consume_token(SEMICOLON);
        result.setGuard(expr);
        result.setBody(stat);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public LoopStatement ForStatement() throws ParseException {
        LoopStatement result;
        ASTList<LoopInitializer> init = null;
        Expression guard = null;
        ASTList<Expression> update = null;
        Statement body;
        jj_consume_token(FOR);
        if (jj_2_56(2147483647)) {
            result = factory.createFor();
            setPrefixInfo(result);
            jj_consume_token(LPAREN);
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case AT:
            case BOOLEAN:
            case BYTE:
            case CHAR:
            case DOUBLE:
            case FALSE:
            case FINAL:
            case FLOAT:
            case INT:
            case LONG:
            case NEW:
            case NULL:
            case SHORT:
            case SUPER:
            case THIS:
            case TRUE:
            case VOID:
            case INTEGER_LITERAL:
            case FLOATING_POINT_LITERAL:
            case CHARACTER_LITERAL:
            case STRING_LITERAL:
            case IDENTIFIER:
            case LPAREN:
            case INCR:
            case DECR:
                init = ForInit();
                break;
            default:
                jj_la1[153] = jj_gen;
            }
            jj_consume_token(SEMICOLON);
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case BOOLEAN:
            case BYTE:
            case CHAR:
            case DOUBLE:
            case FALSE:
            case FLOAT:
            case INT:
            case LONG:
            case NEW:
            case NULL:
            case SHORT:
            case SUPER:
            case THIS:
            case TRUE:
            case VOID:
            case INTEGER_LITERAL:
            case FLOATING_POINT_LITERAL:
            case CHARACTER_LITERAL:
            case STRING_LITERAL:
            case IDENTIFIER:
            case LPAREN:
            case BANG:
            case TILDE:
            case INCR:
            case DECR:
            case PLUS:
            case MINUS:
                guard = Expression();
                break;
            default:
                jj_la1[154] = jj_gen;
            }
            jj_consume_token(SEMICOLON);
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case BOOLEAN:
            case BYTE:
            case CHAR:
            case DOUBLE:
            case FALSE:
            case FLOAT:
            case INT:
            case LONG:
            case NEW:
            case NULL:
            case SHORT:
            case SUPER:
            case THIS:
            case TRUE:
            case VOID:
            case INTEGER_LITERAL:
            case FLOATING_POINT_LITERAL:
            case CHARACTER_LITERAL:
            case STRING_LITERAL:
            case IDENTIFIER:
            case LPAREN:
            case INCR:
            case DECR:
                update = ForUpdate();
                break;
            default:
                jj_la1[155] = jj_gen;
            }
        } else if (jj_2_57(2147483647)) {
            result = factory.createEnhancedFor();
            setPrefixInfo(result);
            jj_consume_token(LPAREN);
            init = ForInit();
            jj_consume_token(COLON);
            guard = Expression();
        } else {
            jj_consume_token(-1);
            throw new ParseException();
        }
        jj_consume_token(RPAREN);
        body = Statement();
        result.setInitializers(init);
        result.setGuard(guard);
        result.setUpdates(update);
        result.setBody(body);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public ASTList<LoopInitializer> ForInit() throws ParseException {
        ASTList<LoopInitializer> result = new ASTArrayList<>();
        LocalVariableDeclaration varDecl = null;
        ASTList<Expression> exprs = null;
        if (jj_2_58(2147483647)) {
            varDecl = LocalVariableDeclaration();
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case BOOLEAN:
            case BYTE:
            case CHAR:
            case DOUBLE:
            case FALSE:
            case FLOAT:
            case INT:
            case LONG:
            case NEW:
            case NULL:
            case SHORT:
            case SUPER:
            case THIS:
            case TRUE:
            case VOID:
            case INTEGER_LITERAL:
            case FLOATING_POINT_LITERAL:
            case CHARACTER_LITERAL:
            case STRING_LITERAL:
            case IDENTIFIER:
            case LPAREN:
            case INCR:
            case DECR:
                exprs = StatementExpressionList();
                break;
            default:
                jj_la1[156] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
            }
        }
        if (varDecl != null) {
            result.add(varDecl);
        } else {
            for (Expression expr : exprs) {
                result.add((LoopInitializer) expr);
            }
        }
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public ASTList<Expression> StatementExpressionList() throws ParseException {
        ASTList<Expression> result = new ASTArrayList<>();
        Expression expr;
        expr = StatementExpression();
        result.add(expr);
        label_74: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case COMMA:
                break;
            default:
                jj_la1[157] = jj_gen;
                break label_74;
            }
            jj_consume_token(COMMA);
            expr = StatementExpression();
            result.add(expr);
        }
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public ASTList<Expression> ForUpdate() throws ParseException {
        ASTList<Expression> result;
        result = StatementExpressionList();
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Break BreakStatement() throws ParseException {
        Identifier id = null;
        Break result;
        jj_consume_token(BREAK);
        result = factory.createBreak();
        setPrefixInfo(result);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case IDENTIFIER:
            jj_consume_token(IDENTIFIER);
            id = factory.createIdentifier(token.image);
            setPrefixInfo(id);
            setPostfixInfo(id);
            result.setIdentifier(id);
            break;
        default:
            jj_la1[158] = jj_gen;
        }
        jj_consume_token(SEMICOLON);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Continue ContinueStatement() throws ParseException {
        Identifier id = null;
        Continue result;
        jj_consume_token(CONTINUE);
        result = factory.createContinue();
        setPrefixInfo(result);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case IDENTIFIER:
            jj_consume_token(IDENTIFIER);
            id = factory.createIdentifier(token.image);
            setPrefixInfo(id);
            setPostfixInfo(id);
            result.setIdentifier(id);
            break;
        default:
            jj_la1[159] = jj_gen;
        }
        jj_consume_token(SEMICOLON);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Return ReturnStatement() throws ParseException {
        Expression expr = null;
        Return result;
        jj_consume_token(RETURN);
        result = factory.createReturn();
        setPrefixInfo(result);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case BOOLEAN:
        case BYTE:
        case CHAR:
        case DOUBLE:
        case FALSE:
        case FLOAT:
        case INT:
        case LONG:
        case NEW:
        case NULL:
        case SHORT:
        case SUPER:
        case THIS:
        case TRUE:
        case VOID:
        case INTEGER_LITERAL:
        case FLOATING_POINT_LITERAL:
        case CHARACTER_LITERAL:
        case STRING_LITERAL:
        case IDENTIFIER:
        case LPAREN:
        case BANG:
        case TILDE:
        case INCR:
        case DECR:
        case PLUS:
        case MINUS:
            expr = Expression();
            result.setExpression(expr);
            break;
        default:
            jj_la1[160] = jj_gen;
        }
        jj_consume_token(SEMICOLON);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Throw ThrowStatement() throws ParseException {
        Throw result;
        Expression expr;
        jj_consume_token(THROW);
        result = factory.createThrow();
        setPrefixInfo(result);
        expr = Expression();
        jj_consume_token(SEMICOLON);
        result.setExpression(expr);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public SynchronizedBlock SynchronizedStatement() throws ParseException {
        SynchronizedBlock result;
        Expression expr;
        StatementBlock block;
        jj_consume_token(SYNCHRONIZED);
        result = factory.createSynchronizedBlock();
        setPrefixInfo(result);
        jj_consume_token(LPAREN);
        expr = Expression();
        jj_consume_token(RPAREN);
        block = Block();
        result.setExpression(expr);
        result.setBody(block);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Try TryStatement() throws ParseException {
        Try result;
        StatementBlock block;
        ParameterDeclaration param;
        ASTList<Branch> branches = new ASTArrayList<>(1);
        Catch cat;
        Finally fin;
        jj_consume_token(TRY);
        result = factory.createTry();
        setPrefixInfo(result);
        block = Block();
        result.setBody(block);
        label_75: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case CATCH:
                break;
            default:
                jj_la1[161] = jj_gen;
                break label_75;
            }
            jj_consume_token(CATCH);
            cat = factory.createCatch();
            setPrefixInfo(cat);
            jj_consume_token(LPAREN);
            param = FormalParameter();
            jj_consume_token(RPAREN);
            block = Block();
            cat.setParameterDeclaration(param);
            cat.setBody(block);
            branches.add(cat);
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case FINALLY:
            jj_consume_token(FINALLY);
            fin = factory.createFinally();
            setPrefixInfo(fin);
            block = Block();
            fin.setBody(block);
            branches.add(fin);
            break;
        default:
            jj_la1[162] = jj_gen;
        }
        result.setBranchList(branches);
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    /**
     * For partial parsing ONLY. Allows this()/super() calls, as in constructor bodies.
     */
    static final public ASTList<Statement> GeneralizedStatements() throws ParseException {
        ASTList<Statement> result = new ASTArrayList<>();
        SpecialConstructorReference scr = null;
        Statement stat = null;
        if (jj_2_59(2147483647)) {
            scr = ExplicitConstructorInvocation();
            result.add(scr);
        } else {
        }
        label_76: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case ASSERT:
            case AT:
            case BOOLEAN:
            case BREAK:
            case BYTE:
            case CHAR:
            case CLASS:
            case CONTINUE:
            case DO:
            case DOUBLE:
            case FALSE:
            case FINAL:
            case FLOAT:
            case FOR:
            case IF:
            case INT:
            case LONG:
            case NEW:
            case NULL:
            case RETURN:
            case SHORT:
            case SUPER:
            case SWITCH:
            case SYNCHRONIZED:
            case THIS:
            case THROW:
            case TRUE:
            case TRY:
            case VOID:
            case WHILE:
            case INTEGER_LITERAL:
            case FLOATING_POINT_LITERAL:
            case CHARACTER_LITERAL:
            case STRING_LITERAL:
            case IDENTIFIER:
            case LPAREN:
            case LBRACE:
            case SEMICOLON:
            case INCR:
            case DECR:
                break;
            default:
                jj_la1[163] = jj_gen;
                break label_76;
            }
            stat = BlockStatement();
            result.add(stat);
        }
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    // Java 5 specific
    static final public AnnotationUseSpecification AnnotationUse() throws ParseException {
        TypeReference tr;
        AnnotationUseSpecification result = factory.createAnnotationUseSpecification();
        Expression ev = null;
        ASTList<AnnotationElementValuePair> list = null;
        Identifier ident;
        AnnotationPropertyReference id;
        AnnotationElementValuePair evp;
        jj_consume_token(AT);
        setPrefixInfo(result);
        tr = Type();
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case LPAREN:
            jj_consume_token(LPAREN);
            list = new ASTArrayList<>();
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case AT:
            case BOOLEAN:
            case BYTE:
            case CHAR:
            case DOUBLE:
            case FALSE:
            case FLOAT:
            case INT:
            case LONG:
            case NEW:
            case NULL:
            case SHORT:
            case SUPER:
            case THIS:
            case TRUE:
            case VOID:
            case INTEGER_LITERAL:
            case FLOATING_POINT_LITERAL:
            case CHARACTER_LITERAL:
            case STRING_LITERAL:
            case IDENTIFIER:
            case LPAREN:
            case LBRACE:
            case BANG:
            case TILDE:
            case INCR:
            case DECR:
            case PLUS:
            case MINUS:
                if (jj_2_60(2147483647)) {
                    jj_consume_token(IDENTIFIER);
                    ident = factory.createIdentifier(token.image);
                    setPrefixInfo(ident);
                    setPostfixInfo(ident);
                    id = factory.createAnnotationPropertyReference(ident);
                    copyPrefixInfo(ident, id);
                    setPostfixInfo(id);
                    jj_consume_token(ASSIGN);
                    ev = ElementValue();
                    evp = new AnnotationElementValuePair(id, ev);
                    copyPrefixInfo(ident, evp);
                    setPostfixInfo(evp);
                    list.add(evp);
                    label_77: while (true) {
                        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                        case COMMA:
                            break;
                        default:
                            jj_la1[164] = jj_gen;
                            break label_77;
                        }
                        jj_consume_token(COMMA);
                        jj_consume_token(IDENTIFIER);
                        ident = factory.createIdentifier(token.image);
                        setPrefixInfo(ident);
                        setPostfixInfo(ident);
                        id = factory.createAnnotationPropertyReference(ident);
                        copyPrefixInfo(ident, id);
                        setPostfixInfo(id);
                        jj_consume_token(ASSIGN);
                        ev = ElementValue();
                        evp = new AnnotationElementValuePair(id, ev);
                        copyPrefixInfo(ident, evp);
                        setPostfixInfo(evp);
                        list.add(evp);
                    }
                } else if (jj_2_61(2147483647)) {
                    ev = ElementValue();
                    evp = new AnnotationElementValuePair(null, ev);
                    copyPrefixInfo(ev, evp);
                    setPostfixInfo(evp);
                    list.add(evp);
                } else {
                    jj_consume_token(-1);
                    throw new ParseException();
                }
                break;
            default:
                jj_la1[165] = jj_gen;
            }
            jj_consume_token(RPAREN);
            break;
        default:
            jj_la1[166] = jj_gen;
        }
        result.setTypeReference(tr);
        if (list != null) {
            result.setElementValuePairs(list);
        }
        setPostfixInfo(result);
        {
            if (true) {
                return result;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public Expression ElementValue() throws ParseException {
        Expression res = null;
        Expression tmp;
        ASTList<Expression> elist = null;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case BOOLEAN:
        case BYTE:
        case CHAR:
        case DOUBLE:
        case FALSE:
        case FLOAT:
        case INT:
        case LONG:
        case NEW:
        case NULL:
        case SHORT:
        case SUPER:
        case THIS:
        case TRUE:
        case VOID:
        case INTEGER_LITERAL:
        case FLOATING_POINT_LITERAL:
        case CHARACTER_LITERAL:
        case STRING_LITERAL:
        case IDENTIFIER:
        case LPAREN:
        case BANG:
        case TILDE:
        case INCR:
        case DECR:
        case PLUS:
        case MINUS:
            res = Expression();
            break;
        case AT:
            res = AnnotationUse();
            break;
        case LBRACE:
            jj_consume_token(LBRACE);
            res = new ElementValueArrayInitializer();
            setPrefixInfo(res);
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case AT:
            case BOOLEAN:
            case BYTE:
            case CHAR:
            case DOUBLE:
            case FALSE:
            case FLOAT:
            case INT:
            case LONG:
            case NEW:
            case NULL:
            case SHORT:
            case SUPER:
            case THIS:
            case TRUE:
            case VOID:
            case INTEGER_LITERAL:
            case FLOATING_POINT_LITERAL:
            case CHARACTER_LITERAL:
            case STRING_LITERAL:
            case IDENTIFIER:
            case LPAREN:
            case LBRACE:
            case BANG:
            case TILDE:
            case INCR:
            case DECR:
            case PLUS:
            case MINUS:
                tmp = ElementValue();
                elist = new ASTArrayList<>();
                elist.add(tmp);
                while (true) {
                    if (jj_2_62(2)) {
                    } else {
                        break;
                    }
                    jj_consume_token(COMMA);
                    tmp = ElementValue();
                    elist.add(tmp);
                }
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case COMMA:
                    jj_consume_token(COMMA);
                    break;
                default:
                    jj_la1[167] = jj_gen;
                }
                break;
            default:
                jj_la1[168] = jj_gen;
            }
            jj_consume_token(RBRACE);
            setPostfixInfo(res);
            ((ElementValueArrayInitializer) res).setElementValues(elist);
            break;
        default:
            jj_la1[169] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        {
            if (true) {
                return res;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public ASTList<TypeArgumentDeclaration> NonWildcardTypeArguments()
            throws ParseException {
        ASTList<UncollatedReferenceQualifier> nl;
        ASTList<TypeArgumentDeclaration> res = new ASTArrayList<>();
        TypeArgumentDeclaration ta;
        jj_consume_token(LT);
        nl = TypedNameList();
        jj_consume_token(GT);
        for (UncollatedReferenceQualifier uncollatedReferenceQualifier : nl) {
            ta = new TypeArgumentDeclaration(uncollatedReferenceQualifier.toTypeReference());
            res.add(ta);
        }
        {
            if (true) {
                return res;
            }
        }
        throw new Error("Missing return statement in function");
    }

    // HACK for handling position of methodDeclarations correctly
    static final public ASTList<TypeParameterDeclaration> TypeParametersNoLE()
            throws ParseException {
        ASTList<TypeParameterDeclaration> res = new ASTArrayList<>();
        TypeParameterDeclaration tp;
        tp = TypeParameter();
        res.add(tp);
        label_79: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case COMMA:
                break;
            default:
                jj_la1[170] = jj_gen;
                break label_79;
            }
            jj_consume_token(COMMA);
            tp = TypeParameter();
            res.add(tp);
        }
        jj_consume_token(GT);
        {
            if (true) {
                return res;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public ASTList<TypeParameterDeclaration> TypeParameters() throws ParseException {
        ASTList<TypeParameterDeclaration> res = new ASTArrayList<>();
        jj_consume_token(LT);
        res = TypeParametersNoLE();
        {
            if (true) {
                return res;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public TypeParameterDeclaration TypeParameter() throws ParseException {
        TypeParameterDeclaration res = new TypeParameterDeclaration();
        Identifier id;
        ASTList<TypeReference> bound = null;
        jj_consume_token(IDENTIFIER);
        id = factory.createIdentifier(token.image);
        setPrefixInfo(id);
        setPostfixInfo(id);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
        case EXTENDS:
            jj_consume_token(EXTENDS);
            bound = Bound();
            break;
        default:
            jj_la1[171] = jj_gen;
        }
        res.setIdentifier(id);
        res.setBound(bound);
        {
            if (true) {
                return res;
            }
        }
        throw new Error("Missing return statement in function");
    }

    static final public ASTList<TypeReference> Bound() throws ParseException {
        TypeReference tr;
        ASTList<TypeReference> res = new ASTArrayList<>();
        tr = Type();
        res.add(tr);
        label_80: while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case BIT_AND:
                break;
            default:
                jj_la1[172] = jj_gen;
                break label_80;
            }
            jj_consume_token(BIT_AND);
            tr = Type();
            res.add(tr);
        }
        {
            if (true) {
                return res;
            }
        }
        throw new Error("Missing return statement in function");
    }

    /*
     * We use productions to match >>>, >> and > so that we can keep the type declaration syntax
     * with generics clean
     */
    static final public void RUNSIGNEDSHIFT() throws ParseException {
        if (getToken(1).kind == GT && ((Token.GTToken) getToken(1)).realKind == RUNSIGNEDSHIFT) {

        } else {
            jj_consume_token(-1);
            throw new ParseException();
        }
        jj_consume_token(GT);
        jj_consume_token(GT);
        jj_consume_token(GT);
    }

    static final public void RSIGNEDSHIFT() throws ParseException {
        if (getToken(1).kind == GT && ((Token.GTToken) getToken(1)).realKind == RSIGNEDSHIFT) {

        } else {
            jj_consume_token(-1);
            throw new ParseException();
        }
        jj_consume_token(GT);
        jj_consume_token(GT);
    }

    static final private boolean jj_2_1(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_1();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(0, xla);
        }
    }

    static final private boolean jj_2_2(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_2();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(1, xla);
        }
    }

    static final private boolean jj_2_3(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_3();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(2, xla);
        }
    }

    static final private boolean jj_2_4(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_4();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(3, xla);
        }
    }

    static final private boolean jj_2_5(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_5();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(4, xla);
        }
    }

    static final private boolean jj_2_6(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_6();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(5, xla);
        }
    }

    static final private boolean jj_2_7(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_7();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(6, xla);
        }
    }

    static final private boolean jj_2_8(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_8();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(7, xla);
        }
    }

    static final private boolean jj_2_9(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_9();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(8, xla);
        }
    }

    static final private boolean jj_2_10(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_10();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(9, xla);
        }
    }

    static final private boolean jj_2_11(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_11();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(10, xla);
        }
    }

    static final private boolean jj_2_12(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_12();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(11, xla);
        }
    }

    static final private boolean jj_2_13(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_13();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(12, xla);
        }
    }

    static final private boolean jj_2_14(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_14();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(13, xla);
        }
    }

    static final private boolean jj_2_15(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_15();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(14, xla);
        }
    }

    static final private boolean jj_2_16(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_16();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(15, xla);
        }
    }

    static final private boolean jj_2_17(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_17();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(16, xla);
        }
    }

    static final private boolean jj_2_18(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_18();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(17, xla);
        }
    }

    static final private boolean jj_2_19(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_19();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(18, xla);
        }
    }

    static final private boolean jj_2_20(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_20();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(19, xla);
        }
    }

    static final private boolean jj_2_21(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_21();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(20, xla);
        }
    }

    static final private boolean jj_2_22(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_22();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(21, xla);
        }
    }

    static final private boolean jj_2_23(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_23();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(22, xla);
        }
    }

    static final private boolean jj_2_24(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_24();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(23, xla);
        }
    }

    static final private boolean jj_2_25(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_25();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(24, xla);
        }
    }

    static final private boolean jj_2_26(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_26();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(25, xla);
        }
    }

    static final private boolean jj_2_27(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_27();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(26, xla);
        }
    }

    static final private boolean jj_2_28(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_28();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(27, xla);
        }
    }

    static final private boolean jj_2_29(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_29();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(28, xla);
        }
    }

    static final private boolean jj_2_30(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_30();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(29, xla);
        }
    }

    static final private boolean jj_2_31(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_31();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(30, xla);
        }
    }

    static final private boolean jj_2_32(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_32();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(31, xla);
        }
    }

    static final private boolean jj_2_33(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_33();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(32, xla);
        }
    }

    static final private boolean jj_2_34(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_34();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(33, xla);
        }
    }

    static final private boolean jj_2_35(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_35();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(34, xla);
        }
    }

    static final private boolean jj_2_36(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_36();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(35, xla);
        }
    }

    static final private boolean jj_2_37(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_37();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(36, xla);
        }
    }

    static final private boolean jj_2_38(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_38();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(37, xla);
        }
    }

    static final private boolean jj_2_39(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_39();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(38, xla);
        }
    }

    static final private boolean jj_2_40(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_40();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(39, xla);
        }
    }

    static final private boolean jj_2_41(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_41();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(40, xla);
        }
    }

    static final private boolean jj_2_42(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_42();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(41, xla);
        }
    }

    static final private boolean jj_2_43(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_43();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(42, xla);
        }
    }

    static final private boolean jj_2_44(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_44();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(43, xla);
        }
    }

    static final private boolean jj_2_45(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_45();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(44, xla);
        }
    }

    static final private boolean jj_2_46(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_46();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(45, xla);
        }
    }

    static final private boolean jj_2_47(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_47();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(46, xla);
        }
    }

    static final private boolean jj_2_48(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_48();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(47, xla);
        }
    }

    static final private boolean jj_2_49(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_49();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(48, xla);
        }
    }

    static final private boolean jj_2_50(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_50();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(49, xla);
        }
    }

    static final private boolean jj_2_51(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_51();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(50, xla);
        }
    }

    static final private boolean jj_2_52(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_52();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(51, xla);
        }
    }

    static final private boolean jj_2_53(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_53();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(52, xla);
        }
    }

    static final private boolean jj_2_54(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_54();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(53, xla);
        }
    }

    static final private boolean jj_2_55(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_55();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(54, xla);
        }
    }

    static final private boolean jj_2_56(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_56();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(55, xla);
        }
    }

    static final private boolean jj_2_57(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_57();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(56, xla);
        }
    }

    static final private boolean jj_2_58(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_58();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(57, xla);
        }
    }

    static final private boolean jj_2_59(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_59();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(58, xla);
        }
    }

    static final private boolean jj_2_60(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_60();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(59, xla);
        }
    }

    static final private boolean jj_2_61(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_61();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(60, xla);
        }
    }

    static final private boolean jj_2_62(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_62();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(61, xla);
        }
    }

    static final private boolean jj_3R_352() {
        return jj_3R_117();
    }

    static final private boolean jj_3R_296() {
        if (jj_scan_token(COMMA)) {
            return true;
        }
        return jj_3R_149();
    }

    static final private boolean jj_3R_220() {
        return jj_3R_269();
    }

    static final private boolean jj_3_14() {
        if (jj_scan_token(COMMA)) {
            return true;
        }
        return jj_3R_106();
    }

    static final private boolean jj_3R_344() {
        if (jj_scan_token(DECR)) {
            return true;
        }
        return jj_3R_118();
    }

    static final private boolean jj_3R_155() {
        if (jj_scan_token(SEMICOLON)) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_220()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_351() {
        if (jj_scan_token(THROWS)) {
            return true;
        }
        return jj_3R_188();
    }

    static final private boolean jj_3R_329() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_374() {
        if (jj_scan_token(BIT_AND)) {
            return true;
        }
        return jj_3R_94();
    }

    static final private boolean jj_3R_177() {
        return false;
    }

    static final private boolean jj_3R_154() {
        if (jj_3R_106()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3_14()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_295() {
        if (jj_scan_token(FINAL)) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_329()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_294() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_349() {
        return jj_3R_165();
    }

    static final private boolean jj_3R_178() {
        return false;
    }

    static final private boolean jj_3R_387() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_258() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_294()) {
                jj_scanpos = xsp;
                break;
            }
        }
        xsp = jj_scanpos;
        if (jj_3R_295()) {
            jj_scanpos = xsp;
        }
        if (jj_3R_94()) {
            return true;
        }
        if (jj_3R_149()) {
            return true;
        }
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_296()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_123() {
        Token xsp;
        xsp = jj_scanpos;
        lookingAhead = true;
        jj_semLA = getToken(1).kind == GT && ((Token.GTToken) getToken(1)).realKind == RSIGNEDSHIFT;
        lookingAhead = false;
        if (!jj_semLA || jj_3R_177()) {
            return true;
        }
        if (jj_scan_token(GT)) {
            return true;
        }
        return jj_scan_token(GT);
    }

    static final private boolean jj_3R_343() {
        if (jj_scan_token(INCR)) {
            return true;
        }
        return jj_3R_118();
    }

    static final private boolean jj_3R_386() {
        return jj_scan_token(PRIVATE);
    }

    static final private boolean jj_3R_385() {
        return jj_scan_token(PROTECTED);
    }

    static final private boolean jj_3R_384() {
        return jj_scan_token(PUBLIC);
    }

    static final private boolean jj_3R_124() {
        Token xsp;
        xsp = jj_scanpos;
        lookingAhead = true;
        jj_semLA =
            getToken(1).kind == GT && ((Token.GTToken) getToken(1)).realKind == RUNSIGNEDSHIFT;
        lookingAhead = false;
        if (!jj_semLA || jj_3R_178()) {
            return true;
        }
        if (jj_scan_token(GT)) {
            return true;
        }
        if (jj_scan_token(GT)) {
            return true;
        }
        return jj_scan_token(GT);
    }

    static final private boolean jj_3R_348() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_384()) {
            jj_scanpos = xsp;
            if (jj_3R_385()) {
                jj_scanpos = xsp;
                if (jj_3R_386()) {
                    return true;
                }
            }
        }
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_387()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_153() {
        if (jj_scan_token(IMPLEMENTS)) {
            return true;
        }
        return jj_3R_188();
    }

    static final private boolean jj_3R_134() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_347() {
        return jj_3R_144();
    }

    static final private boolean jj_3_55() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_134()) {
                jj_scanpos = xsp;
                break;
            }
        }
        xsp = jj_scanpos;
        if (jj_scan_token(32)) {
            jj_scanpos = xsp;
        }
        if (jj_3R_94()) {
            return true;
        }
        return jj_scan_token(IDENTIFIER);
    }

    static final private boolean jj_3R_468() {
        return jj_3R_474();
    }

    static final private boolean jj_3R_337() {
        if (jj_3R_94()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_374()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_333() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_347()) {
                jj_scanpos = xsp;
                break;
            }
        }
        xsp = jj_scanpos;
        if (jj_3R_348()) {
            jj_scanpos = xsp;
        }
        xsp = jj_scanpos;
        if (jj_3R_349()) {
            jj_scanpos = xsp;
        }
        if (jj_scan_token(IDENTIFIER)) {
            return true;
        }
        if (jj_3R_350()) {
            return true;
        }
        xsp = jj_scanpos;
        if (jj_3R_351()) {
            jj_scanpos = xsp;
        }
        if (jj_scan_token(LBRACE)) {
            return true;
        }
        xsp = jj_scanpos;
        if (jj_3R_352()) {
            jj_scanpos = xsp;
        }
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_353()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return jj_scan_token(RBRACE);
    }

    static final private boolean jj_3R_467() {
        return jj_3R_344();
    }

    static final private boolean jj_3R_317() {
        return jj_3R_152();
    }

    static final private boolean jj_3R_466() {
        return jj_3R_343();
    }

    static final private boolean jj_3R_316() {
        return jj_3R_335();
    }

    static final private boolean jj_3R_315() {
        if (jj_3R_258()) {
            return true;
        }
        return jj_scan_token(SEMICOLON);
    }

    static final private boolean jj_3R_276() {
        if (jj_scan_token(COMMA)) {
            return true;
        }
        return jj_3R_275();
    }

    static final private boolean jj_3R_473() {
        return jj_scan_token(MINUS);
    }

    static final private boolean jj_3R_472() {
        return jj_scan_token(PLUS);
    }

    static final private boolean jj_3R_273() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_315()) {
            jj_scanpos = xsp;
            if (jj_3R_316()) {
                jj_scanpos = xsp;
                return jj_3R_317();
            }
        }
        return false;
    }

    static final private boolean jj_3R_465() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_472()) {
            jj_scanpos = xsp;
            if (jj_3R_473()) {
                return true;
            }
        }
        return jj_3R_458();
    }

    static final private boolean jj_3R_320() {
        if (jj_scan_token(EXTENDS)) {
            return true;
        }
        return jj_3R_337();
    }

    static final private boolean jj_3R_458() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_465()) {
            jj_scanpos = xsp;
            if (jj_3R_466()) {
                jj_scanpos = xsp;
                if (jj_3R_467()) {
                    jj_scanpos = xsp;
                    return jj_3R_468();
                }
            }
        }
        return false;
    }

    static final private boolean jj_3R_105() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_104() {
        return jj_scan_token(STATIC);
    }

    static final private boolean jj_3R_103() {
        return jj_scan_token(PRIVATE);
    }

    static final private boolean jj_3R_102() {
        return jj_scan_token(PROTECTED);
    }

    static final private boolean jj_3R_275() {
        if (jj_scan_token(IDENTIFIER)) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_320()) {
            jj_scanpos = xsp;
        }
        return false;
    }

    static final private boolean jj_3R_101() {
        return jj_scan_token(PUBLIC);
    }

    static final private boolean jj_3R_241() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_100() {
        return jj_scan_token(STRICTFP);
    }

    static final private boolean jj_3R_238() {
        return jj_3R_273();
    }

    static final private boolean jj_3_13() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_100()) {
            jj_scanpos = xsp;
            if (jj_3R_101()) {
                jj_scanpos = xsp;
                if (jj_3R_102()) {
                    jj_scanpos = xsp;
                    if (jj_3R_103()) {
                        jj_scanpos = xsp;
                        if (jj_3R_104()) {
                            jj_scanpos = xsp;
                            return jj_3R_105();
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3R_97() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3_13()) {
                jj_scanpos = xsp;
                break;
            }
        }
        if (jj_scan_token(ENUM)) {
            return true;
        }
        if (jj_scan_token(IDENTIFIER)) {
            return true;
        }
        xsp = jj_scanpos;
        if (jj_3R_153()) {
            jj_scanpos = xsp;
        }
        if (jj_scan_token(LBRACE)) {
            return true;
        }
        xsp = jj_scanpos;
        if (jj_3R_154()) {
            jj_scanpos = xsp;
        }
        xsp = jj_scanpos;
        if (jj_scan_token(86)) {
            jj_scanpos = xsp;
        }
        xsp = jj_scanpos;
        if (jj_3R_155()) {
            jj_scanpos = xsp;
        }
        return jj_scan_token(RBRACE);
    }

    static final private boolean jj_3R_161() {
        if (jj_scan_token(LBRACE)) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_238()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return jj_scan_token(RBRACE);
    }

    static final private boolean jj_3R_471() {
        return jj_scan_token(REM);
    }

    static final private boolean jj_3R_470() {
        return jj_scan_token(SLASH);
    }

    static final private boolean jj_3_12() {
        return jj_3R_99();
    }

    static final private boolean jj_3R_469() {
        return jj_scan_token(STAR);
    }

    static final private boolean jj_3R_425() {
        return jj_scan_token(VARARGDENOTER);
    }

    static final private boolean jj_3_11() {
        return jj_3R_98();
    }

    static final private boolean jj_3R_165() {
        if (jj_scan_token(LT)) {
            return true;
        }
        return jj_3R_240();
    }

    static final private boolean jj_3R_459() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_469()) {
            jj_scanpos = xsp;
            if (jj_3R_470()) {
                jj_scanpos = xsp;
                if (jj_3R_471()) {
                    return true;
                }
            }
        }
        return jj_3R_458();
    }

    static final private boolean jj_3_10() {
        return jj_3R_97();
    }

    static final private boolean jj_3R_451() {
        if (jj_3R_458()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_459()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3_9() {
        return jj_3R_96();
    }

    static final private boolean jj_3R_432() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_237() {
        return jj_3R_99();
    }

    static final private boolean jj_3_8() {
        return jj_3R_95();
    }

    static final private boolean jj_3R_236() {
        return jj_3R_98();
    }

    static final private boolean jj_3R_240() {
        if (jj_3R_275()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_276()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return jj_scan_token(GT);
    }

    static final private boolean jj_3R_235() {
        return jj_3R_97();
    }

    static final private boolean jj_3R_143() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_234() {
        return jj_3R_96();
    }

    static final private boolean jj_3R_424() {
        if (jj_scan_token(FINAL)) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_432()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_233() {
        return jj_3R_95();
    }

    static final private boolean jj_3R_272() {
        if (jj_scan_token(_DEFAULT)) {
            return true;
        }
        return jj_3R_137();
    }

    static final private boolean jj_3R_133() {
        if (jj_scan_token(IDENTIFIER)) {
            return true;
        }
        if (jj_scan_token(COLON)) {
            return true;
        }
        return jj_3R_335();
    }

    static final private boolean jj_3R_131() {
        if (jj_scan_token(LT)) {
            return true;
        }
        if (jj_3R_188()) {
            return true;
        }
        return jj_scan_token(GT);
    }

    static final private boolean jj_3R_461() {
        return jj_scan_token(MINUS);
    }

    static final private boolean jj_3R_460() {
        return jj_scan_token(PLUS);
    }

    static final private boolean jj_3R_145() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_93() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_145()) {
            jj_scanpos = xsp;
            if (jj_scan_token(50)) {
                jj_scanpos = xsp;
                return jj_scan_token(13);
            }
        }
        return false;
    }

    static final private boolean jj_3_7() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_93()) {
                jj_scanpos = xsp;
                break;
            }
        }
        if (jj_3R_94()) {
            return true;
        }
        return jj_scan_token(IDENTIFIER);
    }

    static final private boolean jj_3R_452() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_460()) {
            jj_scanpos = xsp;
            if (jj_3R_461()) {
                return true;
            }
        }
        return jj_3R_451();
    }

    static final private boolean jj_3R_423() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_314() {
        return jj_scan_token(ABSTRACT);
    }

    static final private boolean jj_3R_313() {
        return jj_scan_token(PUBLIC);
    }

    static final private boolean jj_3_62() {
        if (jj_scan_token(COMMA)) {
            return true;
        }
        return jj_3R_137();
    }

    static final private boolean jj_3R_312() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_436() {
        if (jj_3R_451()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_452()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_271() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_312()) {
            jj_scanpos = xsp;
            if (jj_3R_313()) {
                jj_scanpos = xsp;
                return jj_3R_314();
            }
        }
        return false;
    }

    static final private boolean jj_3R_415() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_423()) {
                jj_scanpos = xsp;
                break;
            }
        }
        xsp = jj_scanpos;
        if (jj_3R_424()) {
            jj_scanpos = xsp;
        }
        if (jj_3R_94()) {
            return true;
        }
        xsp = jj_scanpos;
        if (jj_3R_425()) {
            jj_scanpos = xsp;
        }
        return jj_3R_206();
    }

    static final private boolean jj_3R_142() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_158() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_232()) {
            jj_scanpos = xsp;
            if (jj_3R_233()) {
                jj_scanpos = xsp;
                if (jj_3R_234()) {
                    jj_scanpos = xsp;
                    if (jj_3R_235()) {
                        jj_scanpos = xsp;
                        if (jj_3R_236()) {
                            jj_scanpos = xsp;
                            if (jj_3R_237()) {
                                jj_scanpos = xsp;
                                return jj_scan_token(85);
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3R_232() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_271()) {
                jj_scanpos = xsp;
                break;
            }
        }
        if (jj_3R_94()) {
            return true;
        }
        if (jj_scan_token(IDENTIFIER)) {
            return true;
        }
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        if (jj_scan_token(RPAREN)) {
            return true;
        }
        xsp = jj_scanpos;
        if (jj_3R_272()) {
            jj_scanpos = xsp;
        }
        return false;
    }

    static final private boolean jj_3R_373() {
        return jj_3R_412();
    }

    static final private boolean jj_3R_372() {
        return jj_3R_411();
    }

    static final private boolean jj_3R_371() {
        return jj_3R_410();
    }

    static final private boolean jj_3R_370() {
        return jj_3R_409();
    }

    static final private boolean jj_3R_369() {
        return jj_3R_408();
    }

    static final private boolean jj_3R_368() {
        return jj_3R_407();
    }

    static final private boolean jj_3R_260() {
        if (jj_3R_137()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3_62()) {
                jj_scanpos = xsp;
                break;
            }
        }
        xsp = jj_scanpos;
        if (jj_scan_token(86)) {
            jj_scanpos = xsp;
        }
        return false;
    }

    static final private boolean jj_3R_367() {
        return jj_3R_406();
    }

    static final private boolean jj_3R_366() {
        return jj_3R_405();
    }

    static final private boolean jj_3R_388() {
        if (jj_3R_415()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_416()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_365() {
        return jj_3R_404();
    }

    static final private boolean jj_3R_364() {
        return jj_3R_403();
    }

    static final private boolean jj_3R_363() {
        return jj_3R_402();
    }

    static final private boolean jj_3R_195() {
        if (jj_scan_token(LBRACE)) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_260()) {
            jj_scanpos = xsp;
        }
        return jj_scan_token(RBRACE);
    }

    static final private boolean jj_3R_416() {
        if (jj_scan_token(COMMA)) {
            return true;
        }
        return jj_3R_415();
    }

    static final private boolean jj_3R_362() {
        return jj_3R_401();
    }

    static final private boolean jj_3R_194() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_193() {
        return jj_3R_132();
    }

    static final private boolean jj_3_38() {
        return jj_3R_124();
    }

    static final private boolean jj_3_61() {
        return jj_3R_137();
    }

    static final private boolean jj_3R_140() {
        return jj_3R_144();
    }

    static final private boolean jj_3_37() {
        return jj_3R_123();
    }

    static final private boolean jj_3R_137() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_193()) {
            jj_scanpos = xsp;
            if (jj_3R_194()) {
                jj_scanpos = xsp;
                return jj_3R_195();
            }
        }
        return false;
    }

    static final private boolean jj_3R_122() {
        return jj_scan_token(LSHIFT);
    }

    static final private boolean jj_3R_361() {
        if (jj_3R_297()) {
            return true;
        }
        return jj_scan_token(SEMICOLON);
    }

    static final private boolean jj_3R_350() {
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_388()) {
            jj_scanpos = xsp;
        }
        return jj_scan_token(RPAREN);
    }

    static final private boolean jj_3R_92() {
        return jj_3R_144();
    }

    static final private boolean jj_3_36() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_122()) {
            jj_scanpos = xsp;
            if (jj_3_37()) {
                jj_scanpos = xsp;
                if (jj_3_38()) {
                    return true;
                }
            }
        }
        return jj_3R_436();
    }

    static final private boolean jj_3R_360() {
        return jj_3R_400();
    }

    static final private boolean jj_3R_141() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_91() {
        return jj_scan_token(ABSTRACT);
    }

    static final private boolean jj_3R_359() {
        return jj_3R_161();
    }

    static final private boolean jj_3R_90() {
        return jj_scan_token(STATIC);
    }

    static final private boolean jj_3R_434() {
        if (jj_3R_436()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3_36()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_319() {
        return jj_3R_137();
    }

    static final private boolean jj_3R_89() {
        return jj_scan_token(PRIVATE);
    }

    static final private boolean jj_3R_88() {
        return jj_scan_token(PROTECTED);
    }

    static final private boolean jj_3_54() {
        return jj_3R_133();
    }

    static final private boolean jj_3R_87() {
        return jj_scan_token(PUBLIC);
    }

    static final private boolean jj_3R_336() {
        if (jj_scan_token(COMMA)) {
            return true;
        }
        if (jj_scan_token(IDENTIFIER)) {
            return true;
        }
        if (jj_scan_token(ASSIGN)) {
            return true;
        }
        return jj_3R_137();
    }

    static final private boolean jj_3R_86() {
        return jj_scan_token(STRICTFP);
    }

    static final private boolean jj_3R_335() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3_54()) {
            jj_scanpos = xsp;
            if (jj_3R_359()) {
                jj_scanpos = xsp;
                if (jj_3R_360()) {
                    jj_scanpos = xsp;
                    if (jj_3R_361()) {
                        jj_scanpos = xsp;
                        if (jj_3R_362()) {
                            jj_scanpos = xsp;
                            if (jj_3R_363()) {
                                jj_scanpos = xsp;
                                if (jj_3R_364()) {
                                    jj_scanpos = xsp;
                                    if (jj_3R_365()) {
                                        jj_scanpos = xsp;
                                        if (jj_3R_366()) {
                                            jj_scanpos = xsp;
                                            if (jj_3R_367()) {
                                                jj_scanpos = xsp;
                                                if (jj_3R_368()) {
                                                    jj_scanpos = xsp;
                                                    if (jj_3R_369()) {
                                                        jj_scanpos = xsp;
                                                        if (jj_3R_370()) {
                                                            jj_scanpos = xsp;
                                                            if (jj_3R_371()) {
                                                                jj_scanpos = xsp;
                                                                if (jj_3R_372()) {
                                                                    jj_scanpos = xsp;
                                                                    return jj_3R_373();
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3_6() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_86()) {
            jj_scanpos = xsp;
            if (jj_3R_87()) {
                jj_scanpos = xsp;
                if (jj_3R_88()) {
                    jj_scanpos = xsp;
                    if (jj_3R_89()) {
                        jj_scanpos = xsp;
                        if (jj_3R_90()) {
                            jj_scanpos = xsp;
                            if (jj_3R_91()) {
                                jj_scanpos = xsp;
                                return jj_3R_92();
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3R_99() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3_6()) {
                jj_scanpos = xsp;
                break;
            }
        }
        if (jj_scan_token(AT)) {
            return true;
        }
        if (jj_scan_token(INTERFACE)) {
            return true;
        }
        if (jj_scan_token(IDENTIFIER)) {
            return true;
        }
        if (jj_scan_token(LBRACE)) {
            return true;
        }
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_158()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return jj_scan_token(RBRACE);
    }

    static final private boolean jj_3R_399() {
        if (jj_scan_token(LBRACKET)) {
            return true;
        }
        return jj_scan_token(RBRACKET);
    }

    static final private boolean jj_3R_440() {
        return jj_scan_token(GE);
    }

    static final private boolean jj_3R_439() {
        return jj_scan_token(LE);
    }

    static final private boolean jj_3R_438() {
        return jj_scan_token(GT);
    }

    static final private boolean jj_3R_437() {
        return jj_scan_token(LT);
    }

    static final private boolean jj_3_60() {
        if (jj_scan_token(IDENTIFIER)) {
            return true;
        }
        return jj_scan_token(ASSIGN);
    }

    static final private boolean jj_3R_435() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_437()) {
            jj_scanpos = xsp;
            if (jj_3R_438()) {
                jj_scanpos = xsp;
                if (jj_3R_439()) {
                    jj_scanpos = xsp;
                    if (jj_3R_440()) {
                        return true;
                    }
                }
            }
        }
        return jj_3R_434();
    }

    static final private boolean jj_3R_433() {
        if (jj_scan_token(LBRACKET)) {
            return true;
        }
        return jj_scan_token(RBRACKET);
    }

    static final private boolean jj_3R_356() {
        if (jj_scan_token(IDENTIFIER)) {
            return true;
        }
        if (jj_3R_350()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_399()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_426() {
        Token xsp;
        if (jj_3R_433()) {
            return true;
        }
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_433()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return jj_3R_242();
    }

    static final private boolean jj_3R_428() {
        if (jj_3R_434()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_435()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3_52() {
        if (jj_scan_token(LBRACKET)) {
            return true;
        }
        return jj_scan_token(RBRACKET);
    }

    static final private boolean jj_3R_85() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_scan_token(67)) {
            jj_scanpos = xsp;
            if (jj_scan_token(50)) {
                jj_scanpos = xsp;
                if (jj_scan_token(49)) {
                    jj_scanpos = xsp;
                    if (jj_scan_token(48)) {
                        jj_scanpos = xsp;
                        if (jj_scan_token(53)) {
                            jj_scanpos = xsp;
                            if (jj_scan_token(13)) {
                                jj_scanpos = xsp;
                                return jj_3R_143();
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3_5() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_85()) {
                jj_scanpos = xsp;
                break;
            }
        }
        if (jj_scan_token(AT)) {
            return true;
        }
        return jj_scan_token(INTERFACE);
    }

    static final private boolean jj_3R_318() {
        if (jj_scan_token(IDENTIFIER)) {
            return true;
        }
        if (jj_scan_token(ASSIGN)) {
            return true;
        }
        if (jj_3R_137()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_336()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_274() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_318()) {
            jj_scanpos = xsp;
            return jj_3R_319();
        }
        return false;
    }

    static final private boolean jj_3R_84() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_scan_token(50)) {
            jj_scanpos = xsp;
            if (jj_scan_token(67)) {
                jj_scanpos = xsp;
                if (jj_scan_token(49)) {
                    jj_scanpos = xsp;
                    if (jj_scan_token(48)) {
                        jj_scanpos = xsp;
                        if (jj_scan_token(53)) {
                            jj_scanpos = xsp;
                            return jj_3R_142();
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3_4() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_84()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return jj_scan_token(ENUM);
    }

    static final private boolean jj_3R_83() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_scan_token(13)) {
            jj_scanpos = xsp;
            if (jj_scan_token(50)) {
                jj_scanpos = xsp;
                if (jj_scan_token(67)) {
                    jj_scanpos = xsp;
                    return jj_3R_141();
                }
            }
        }
        return false;
    }

    static final private boolean jj_3R_166() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_scan_token(50)) {
            jj_scanpos = xsp;
            if (jj_scan_token(49)) {
                jj_scanpos = xsp;
                if (jj_scan_token(48)) {
                    jj_scanpos = xsp;
                    if (jj_scan_token(53)) {
                        jj_scanpos = xsp;
                        if (jj_scan_token(13)) {
                            jj_scanpos = xsp;
                            if (jj_scan_token(32)) {
                                jj_scanpos = xsp;
                                if (jj_scan_token(44)) {
                                    jj_scanpos = xsp;
                                    if (jj_scan_token(56)) {
                                        jj_scanpos = xsp;
                                        if (jj_scan_token(67)) {
                                            jj_scanpos = xsp;
                                            return jj_3R_241();
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3R_167() {
        return jj_3R_165();
    }

    static final private boolean jj_3_3() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_83()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return jj_scan_token(INTERFACE);
    }

    static final private boolean jj_3R_113() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_166()) {
                jj_scanpos = xsp;
                break;
            }
        }
        xsp = jj_scanpos;
        if (jj_3R_167()) {
            jj_scanpos = xsp;
        }
        if (jj_3R_129()) {
            return true;
        }
        if (jj_scan_token(IDENTIFIER)) {
            return true;
        }
        return jj_scan_token(LPAREN);
    }

    static final private boolean jj_3R_82() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_scan_token(13)) {
            jj_scanpos = xsp;
            if (jj_scan_token(32)) {
                jj_scanpos = xsp;
                if (jj_scan_token(50)) {
                    jj_scanpos = xsp;
                    if (jj_scan_token(67)) {
                        jj_scanpos = xsp;
                        return jj_3R_140();
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3_51() {
        if (jj_scan_token(LBRACKET)) {
            return true;
        }
        if (jj_3R_132()) {
            return true;
        }
        return jj_scan_token(RBRACKET);
    }

    static final private boolean jj_3_2() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_82()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return jj_scan_token(CLASS);
    }

    static final private boolean jj_3_53() {
        Token xsp;
        if (jj_3_51()) {
            return true;
        }
        while (true) {
            xsp = jj_scanpos;
            if (jj_3_51()) {
                jj_scanpos = xsp;
                break;
            }
        }
        while (true) {
            xsp = jj_scanpos;
            if (jj_3_52()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_417() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3_53()) {
            jj_scanpos = xsp;
            return jj_3R_426();
        }
        return false;
    }

    static final private boolean jj_3R_429() {
        if (jj_scan_token(INSTANCEOF)) {
            return true;
        }
        return jj_3R_94();
    }

    static final private boolean jj_3R_421() {
        if (jj_3R_428()) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_429()) {
            jj_scanpos = xsp;
        }
        return false;
    }

    static final private boolean jj_3R_239() {
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_274()) {
            jj_scanpos = xsp;
        }
        return jj_scan_token(RPAREN);
    }

    static final private boolean jj_3R_144() {
        if (jj_scan_token(AT)) {
            return true;
        }
        if (jj_3R_94()) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_239()) {
            jj_scanpos = xsp;
        }
        return false;
    }

    static final private boolean jj_3R_358() {
        return jj_3R_161();
    }

    static final private boolean jj_3R_357() {
        if (jj_scan_token(THROWS)) {
            return true;
        }
        return jj_3R_188();
    }

    static final private boolean jj_3R_431() {
        return jj_scan_token(NE);
    }

    static final private boolean jj_3R_420() {
        return jj_3R_417();
    }

    static final private boolean jj_3R_430() {
        return jj_scan_token(EQ);
    }

    static final private boolean jj_3R_422() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_430()) {
            jj_scanpos = xsp;
            if (jj_3R_431()) {
                return true;
            }
        }
        return jj_3R_421();
    }

    static final private boolean jj_3_59() {
        return jj_3R_117();
    }

    static final private boolean jj_3R_413() {
        if (jj_3R_421()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_422()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_355() {
        if (jj_scan_token(LT)) {
            return true;
        }
        return jj_3R_240();
    }

    static final private boolean jj_3R_427() {
        return jj_3R_219();
    }

    static final private boolean jj_3R_419() {
        if (jj_3R_119()) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_427()) {
            jj_scanpos = xsp;
        }
        return false;
    }

    static final private boolean jj_3R_398() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_418() {
        return jj_3R_131();
    }

    static final private boolean jj_3R_397() {
        return jj_scan_token(STRICTFP);
    }

    static final private boolean jj_3R_396() {
        return jj_scan_token(SYNCHRONIZED);
    }

    static final private boolean jj_3R_395() {
        return jj_scan_token(NATIVE);
    }

    static final private boolean jj_3R_394() {
        return jj_scan_token(ABSTRACT);
    }

    static final private boolean jj_3R_393() {
        return jj_scan_token(FINAL);
    }

    static final private boolean jj_3R_414() {
        if (jj_scan_token(BIT_AND)) {
            return true;
        }
        return jj_3R_413();
    }

    static final private boolean jj_3R_392() {
        return jj_scan_token(STATIC);
    }

    static final private boolean jj_3R_391() {
        return jj_scan_token(PRIVATE);
    }

    static final private boolean jj_3R_390() {
        return jj_scan_token(PROTECTED);
    }

    static final private boolean jj_3R_187() {
        if (jj_scan_token(NEW)) {
            return true;
        }
        if (jj_3R_120()) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_418()) {
            jj_scanpos = xsp;
        }
        xsp = jj_scanpos;
        if (jj_3R_419()) {
            jj_scanpos = xsp;
            return jj_3R_420();
        }
        return false;
    }

    static final private boolean jj_3R_389() {
        return jj_scan_token(PUBLIC);
    }

    static final private boolean jj_3R_379() {
        if (jj_3R_413()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_414()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_354() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_389()) {
            jj_scanpos = xsp;
            if (jj_3R_390()) {
                jj_scanpos = xsp;
                if (jj_3R_391()) {
                    jj_scanpos = xsp;
                    if (jj_3R_392()) {
                        jj_scanpos = xsp;
                        if (jj_3R_393()) {
                            jj_scanpos = xsp;
                            if (jj_3R_394()) {
                                jj_scanpos = xsp;
                                if (jj_3R_395()) {
                                    jj_scanpos = xsp;
                                    if (jj_3R_396()) {
                                        jj_scanpos = xsp;
                                        if (jj_3R_397()) {
                                            jj_scanpos = xsp;
                                            return jj_3R_398();
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3R_334() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_354()) {
                jj_scanpos = xsp;
                break;
            }
        }
        xsp = jj_scanpos;
        if (jj_3R_355()) {
            jj_scanpos = xsp;
        }
        if (jj_3R_129()) {
            return true;
        }
        if (jj_3R_356()) {
            return true;
        }
        xsp = jj_scanpos;
        if (jj_3R_357()) {
            jj_scanpos = xsp;
        }
        xsp = jj_scanpos;
        if (jj_3R_358()) {
            jj_scanpos = xsp;
            return jj_scan_token(85);
        }
        return false;
    }

    static final private boolean jj_3_50() {
        if (jj_scan_token(NEW)) {
            return true;
        }
        if (jj_3R_126()) {
            return true;
        }
        return jj_3R_417();
    }

    static final private boolean jj_3R_130() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3_50()) {
            jj_scanpos = xsp;
            return jj_3R_187();
        }
        return false;
    }

    static final private boolean jj_3R_449() {
        if (jj_scan_token(FINALLY)) {
            return true;
        }
        return jj_3R_161();
    }

    static final private boolean jj_3_49() {
        if (jj_scan_token(COMMA)) {
            return true;
        }
        return jj_3R_132();
    }

    static final private boolean jj_3R_380() {
        if (jj_scan_token(XOR)) {
            return true;
        }
        return jj_3R_379();
    }

    static final private boolean jj_3R_138() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_81() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_138()) {
                jj_scanpos = xsp;
                break;
            }
        }
        if (jj_scan_token(PACKAGE)) {
            return true;
        }
        if (jj_3R_139()) {
            return true;
        }
        return jj_scan_token(SEMICOLON);
    }

    static final private boolean jj_3R_341() {
        if (jj_3R_379()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_380()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_250() {
        if (jj_3R_132()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_278()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3_27() {
        if (jj_scan_token(COMMA)) {
            return true;
        }
        return jj_3R_116();
    }

    static final private boolean jj_3R_278() {
        if (jj_scan_token(COMMA)) {
            return true;
        }
        return jj_3R_132();
    }

    static final private boolean jj_3R_448() {
        if (jj_scan_token(CATCH)) {
            return true;
        }
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        if (jj_3R_415()) {
            return true;
        }
        if (jj_scan_token(RPAREN)) {
            return true;
        }
        return jj_3R_161();
    }

    static final private boolean jj_3R_346() {
        if (jj_3R_116()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3_27()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_242() {
        if (jj_scan_token(LBRACE)) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_346()) {
            jj_scanpos = xsp;
        }
        xsp = jj_scanpos;
        if (jj_scan_token(86)) {
            jj_scanpos = xsp;
        }
        return jj_scan_token(RBRACE);
    }

    static final private boolean jj_3R_175() {
        return jj_3R_250();
    }

    static final private boolean jj_3R_411() {
        if (jj_scan_token(TRY)) {
            return true;
        }
        if (jj_3R_161()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_448()) {
                jj_scanpos = xsp;
                break;
            }
        }
        xsp = jj_scanpos;
        if (jj_3R_449()) {
            jj_scanpos = xsp;
        }
        return false;
    }

    static final private boolean jj_3R_119() {
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_175()) {
            jj_scanpos = xsp;
        }
        return jj_scan_token(RPAREN);
    }

    static final private boolean jj_3R_342() {
        if (jj_scan_token(BIT_OR)) {
            return true;
        }
        return jj_3R_341();
    }

    static final private boolean jj_3R_327() {
        if (jj_3R_341()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_342()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3_1() {
        return jj_3R_81();
    }

    static final private boolean jj_3R_171() {
        return jj_3R_132();
    }

    static final private boolean jj_3R_170() {
        return jj_3R_242();
    }

    static final private boolean jj_3R_116() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_170()) {
            jj_scanpos = xsp;
            return jj_3R_171();
        }
        return false;
    }

    static final private boolean jj_3R_339() {
        return jj_scan_token(NULL);
    }

    static final private boolean jj_3R_264() {
        if (jj_scan_token(LBRACKET)) {
            return true;
        }
        return jj_scan_token(RBRACKET);
    }

    static final private boolean jj_3R_410() {
        if (jj_scan_token(SYNCHRONIZED)) {
            return true;
        }
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        if (jj_3R_132()) {
            return true;
        }
        if (jj_scan_token(RPAREN)) {
            return true;
        }
        return jj_3R_161();
    }

    static final private boolean jj_3R_328() {
        if (jj_scan_token(SC_AND)) {
            return true;
        }
        return jj_3R_327();
    }

    static final private boolean jj_3R_376() {
        return jj_scan_token(FALSE);
    }

    static final private boolean jj_3R_280() {
        if (jj_3R_327()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_328()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_375() {
        return jj_scan_token(TRUE);
    }

    static final private boolean jj_3R_206() {
        if (jj_scan_token(IDENTIFIER)) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_264()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_338() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_375()) {
            jj_scanpos = xsp;
            return jj_3R_376();
        }
        return false;
    }

    static final private boolean jj_3R_169() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_168() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_326() {
        return jj_3R_339();
    }

    static final private boolean jj_3R_207() {
        if (jj_scan_token(ASSIGN)) {
            return true;
        }
        return jj_3R_116();
    }

    static final private boolean jj_3R_409() {
        if (jj_scan_token(THROW)) {
            return true;
        }
        if (jj_3R_132()) {
            return true;
        }
        return jj_scan_token(SEMICOLON);
    }

    static final private boolean jj_3R_325() {
        return jj_3R_338();
    }

    static final private boolean jj_3R_149() {
        if (jj_3R_206()) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_207()) {
            jj_scanpos = xsp;
        }
        return false;
    }

    static final private boolean jj_3R_281() {
        if (jj_scan_token(SC_OR)) {
            return true;
        }
        return jj_3R_280();
    }

    static final private boolean jj_3R_324() {
        return jj_scan_token(STRING_LITERAL);
    }

    static final private boolean jj_3R_255() {
        if (jj_3R_280()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_281()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_323() {
        return jj_scan_token(CHARACTER_LITERAL);
    }

    static final private boolean jj_3R_447() {
        return jj_3R_132();
    }

    static final private boolean jj_3R_322() {
        return jj_scan_token(FLOATING_POINT_LITERAL);
    }

    static final private boolean jj_3R_408() {
        if (jj_scan_token(RETURN)) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_447()) {
            jj_scanpos = xsp;
        }
        return jj_scan_token(SEMICOLON);
    }

    static final private boolean jj_3R_150() {
        if (jj_scan_token(COMMA)) {
            return true;
        }
        return jj_3R_149();
    }

    static final private boolean jj_3R_321() {
        return jj_scan_token(INTEGER_LITERAL);
    }

    static final private boolean jj_3R_256() {
        if (jj_scan_token(HOOK)) {
            return true;
        }
        if (jj_3R_132()) {
            return true;
        }
        if (jj_scan_token(COLON)) {
            return true;
        }
        return jj_3R_189();
    }

    static final private boolean jj_3R_277() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_321()) {
            jj_scanpos = xsp;
            if (jj_3R_322()) {
                jj_scanpos = xsp;
                if (jj_3R_323()) {
                    jj_scanpos = xsp;
                    if (jj_3R_324()) {
                        jj_scanpos = xsp;
                        if (jj_3R_325()) {
                            jj_scanpos = xsp;
                            return jj_3R_326();
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3R_189() {
        if (jj_3R_255()) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_256()) {
            jj_scanpos = xsp;
        }
        return false;
    }

    static final private boolean jj_3R_446() {
        return jj_scan_token(IDENTIFIER);
    }

    static final private boolean jj_3R_184() {
        return jj_3R_119();
    }

    static final private boolean jj_3R_293() {
        return jj_scan_token(ORASSIGN);
    }

    static final private boolean jj_3R_292() {
        return jj_scan_token(XORASSIGN);
    }

    static final private boolean jj_3R_205() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_291() {
        return jj_scan_token(ANDASSIGN);
    }

    static final private boolean jj_3R_407() {
        if (jj_scan_token(CONTINUE)) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_446()) {
            jj_scanpos = xsp;
        }
        return jj_scan_token(SEMICOLON);
    }

    static final private boolean jj_3R_204() {
        return jj_scan_token(VOLATILE);
    }

    static final private boolean jj_3R_290() {
        return jj_scan_token(RUNSIGNEDSHIFTASSIGN);
    }

    static final private boolean jj_3R_203() {
        return jj_scan_token(TRANSIENT);
    }

    static final private boolean jj_3R_289() {
        return jj_scan_token(RSIGNEDSHIFTASSIGN);
    }

    static final private boolean jj_3R_202() {
        return jj_scan_token(FINAL);
    }

    static final private boolean jj_3R_288() {
        return jj_scan_token(LSHIFTASSIGN);
    }

    static final private boolean jj_3R_201() {
        return jj_scan_token(STATIC);
    }

    static final private boolean jj_3R_287() {
        return jj_scan_token(MINUSASSIGN);
    }

    static final private boolean jj_3R_200() {
        return jj_scan_token(PRIVATE);
    }

    static final private boolean jj_3R_286() {
        return jj_scan_token(PLUSASSIGN);
    }

    static final private boolean jj_3R_183() {
        if (jj_scan_token(DOT)) {
            return true;
        }
        return jj_scan_token(IDENTIFIER);
    }

    static final private boolean jj_3R_199() {
        return jj_scan_token(PROTECTED);
    }

    static final private boolean jj_3R_285() {
        return jj_scan_token(REMASSIGN);
    }

    static final private boolean jj_3R_198() {
        return jj_scan_token(PUBLIC);
    }

    static final private boolean jj_3R_284() {
        return jj_scan_token(SLASHASSIGN);
    }

    static final private boolean jj_3R_283() {
        return jj_scan_token(STARASSIGN);
    }

    static final private boolean jj_3R_282() {
        return jj_scan_token(ASSIGN);
    }

    static final private boolean jj_3R_148() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_198()) {
            jj_scanpos = xsp;
            if (jj_3R_199()) {
                jj_scanpos = xsp;
                if (jj_3R_200()) {
                    jj_scanpos = xsp;
                    if (jj_3R_201()) {
                        jj_scanpos = xsp;
                        if (jj_3R_202()) {
                            jj_scanpos = xsp;
                            if (jj_3R_203()) {
                                jj_scanpos = xsp;
                                if (jj_3R_204()) {
                                    jj_scanpos = xsp;
                                    return jj_3R_205();
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3R_182() {
        if (jj_scan_token(LBRACKET)) {
            return true;
        }
        if (jj_3R_132()) {
            return true;
        }
        return jj_scan_token(RBRACKET);
    }

    static final private boolean jj_3R_257() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_282()) {
            jj_scanpos = xsp;
            if (jj_3R_283()) {
                jj_scanpos = xsp;
                if (jj_3R_284()) {
                    jj_scanpos = xsp;
                    if (jj_3R_285()) {
                        jj_scanpos = xsp;
                        if (jj_3R_286()) {
                            jj_scanpos = xsp;
                            if (jj_3R_287()) {
                                jj_scanpos = xsp;
                                if (jj_3R_288()) {
                                    jj_scanpos = xsp;
                                    if (jj_3R_289()) {
                                        jj_scanpos = xsp;
                                        if (jj_3R_290()) {
                                            jj_scanpos = xsp;
                                            if (jj_3R_291()) {
                                                jj_scanpos = xsp;
                                                if (jj_3R_292()) {
                                                    jj_scanpos = xsp;
                                                    return jj_3R_293();
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3R_95() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_148()) {
                jj_scanpos = xsp;
                break;
            }
        }
        if (jj_3R_94()) {
            return true;
        }
        if (jj_3R_149()) {
            return true;
        }
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_150()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return jj_scan_token(SEMICOLON);
    }

    static final private boolean jj_3R_445() {
        return jj_scan_token(IDENTIFIER);
    }

    static final private boolean jj_3_48() {
        if (jj_scan_token(DOT)) {
            return true;
        }
        if (jj_3R_131()) {
            return true;
        }
        return jj_scan_token(IDENTIFIER);
    }

    static final private boolean jj_3R_406() {
        if (jj_scan_token(BREAK)) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_445()) {
            jj_scanpos = xsp;
        }
        return jj_scan_token(SEMICOLON);
    }

    static final private boolean jj_3_26() {
        return jj_3R_99();
    }

    static final private boolean jj_3_47() {
        if (jj_scan_token(DOT)) {
            return true;
        }
        return jj_3R_130();
    }

    static final private boolean jj_3_25() {
        return jj_3R_97();
    }

    static final private boolean jj_3R_115() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_scan_token(53)) {
            jj_scanpos = xsp;
            if (jj_scan_token(13)) {
                jj_scanpos = xsp;
                if (jj_scan_token(32)) {
                    jj_scanpos = xsp;
                    if (jj_scan_token(50)) {
                        jj_scanpos = xsp;
                        if (jj_scan_token(49)) {
                            jj_scanpos = xsp;
                            if (jj_scan_token(48)) {
                                jj_scanpos = xsp;
                                if (jj_scan_token(67)) {
                                    jj_scanpos = xsp;
                                    return jj_3R_169();
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3_24() {
        return jj_3R_113();
    }

    static final private boolean jj_3R_190() {
        if (jj_3R_257()) {
            return true;
        }
        return jj_3R_132();
    }

    static final private boolean jj_3R_114() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_scan_token(53)) {
            jj_scanpos = xsp;
            if (jj_scan_token(13)) {
                jj_scanpos = xsp;
                if (jj_scan_token(32)) {
                    jj_scanpos = xsp;
                    if (jj_scan_token(50)) {
                        jj_scanpos = xsp;
                        if (jj_scan_token(49)) {
                            jj_scanpos = xsp;
                            if (jj_scan_token(48)) {
                                jj_scanpos = xsp;
                                if (jj_scan_token(67)) {
                                    jj_scanpos = xsp;
                                    return jj_3R_168();
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3_23() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_115()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return jj_scan_token(INTERFACE);
    }

    static final private boolean jj_3_46() {
        if (jj_scan_token(DOT)) {
            return true;
        }
        return jj_scan_token(SUPER);
    }

    static final private boolean jj_3_22() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_114()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return jj_scan_token(CLASS);
    }

    static final private boolean jj_3R_464() {
        return jj_3R_259();
    }

    static final private boolean jj_3R_311() {
        if (jj_3R_95()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_132() {
        if (jj_3R_189()) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_190()) {
            jj_scanpos = xsp;
        }
        return false;
    }

    static final private boolean jj_3R_310() {
        if (jj_3R_99()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3_45() {
        if (jj_scan_token(DOT)) {
            return true;
        }
        return jj_scan_token(THIS);
    }

    static final private boolean jj_3R_309() {
        if (jj_3R_97()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_308() {
        if (jj_3R_334()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_128() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3_45()) {
            jj_scanpos = xsp;
            lookingAhead = true;
            jj_semLA = isSuperAllowed();
            lookingAhead = false;
            if (!jj_semLA || jj_3_46()) {
                jj_scanpos = xsp;
                if (jj_3_47()) {
                    jj_scanpos = xsp;
                    if (jj_3_48()) {
                        jj_scanpos = xsp;
                        if (jj_3R_182()) {
                            jj_scanpos = xsp;
                            if (jj_3R_183()) {
                                jj_scanpos = xsp;
                                return jj_3R_184();
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3R_259() {
        if (jj_3R_297()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_298()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_307() {
        if (jj_3R_98()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_298() {
        if (jj_scan_token(COMMA)) {
            return true;
        }
        return jj_3R_297();
    }

    static final private boolean jj_3R_306() {
        if (jj_3R_96()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_270() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_306()) {
            jj_scanpos = xsp;
            if (jj_3R_307()) {
                jj_scanpos = xsp;
                if (jj_3R_308()) {
                    jj_scanpos = xsp;
                    if (jj_3R_309()) {
                        jj_scanpos = xsp;
                        if (jj_3R_310()) {
                            jj_scanpos = xsp;
                            return jj_3R_311();
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3_44() {
        if (jj_3R_129()) {
            return true;
        }
        if (jj_scan_token(DOT)) {
            return true;
        }
        return jj_scan_token(CLASS);
    }

    static final private boolean jj_3_58() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_scan_token(32)) {
            jj_scanpos = xsp;
        }
        if (jj_3R_94()) {
            return true;
        }
        return jj_scan_token(IDENTIFIER);
    }

    static final private boolean jj_3R_249() {
        return jj_3R_139();
    }

    static final private boolean jj_3R_231() {
        return jj_3R_270();
    }

    static final private boolean jj_3R_266() {
        if (jj_scan_token(COMMA)) {
            return true;
        }
        return jj_3R_120();
    }

    static final private boolean jj_3R_248() {
        if (jj_3R_129()) {
            return true;
        }
        if (jj_scan_token(DOT)) {
            return true;
        }
        return jj_scan_token(CLASS);
    }

    static final private boolean jj_3R_192() {
        return jj_3R_259();
    }

    static final private boolean jj_3R_191() {
        return jj_3R_258();
    }

    static final private boolean jj_3R_188() {
        if (jj_3R_120()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_266()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_247() {
        return jj_3R_130();
    }

    static final private boolean jj_3R_136() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_191()) {
            jj_scanpos = xsp;
            return jj_3R_192();
        }
        return false;
    }

    static final private boolean jj_3R_230() {
        if (jj_scan_token(EXTENDS)) {
            return true;
        }
        return jj_3R_188();
    }

    static final private boolean jj_3R_279() {
        if (jj_scan_token(COMMA)) {
            return true;
        }
        return jj_3R_176();
    }

    static final private boolean jj_3R_246() {
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        if (jj_3R_132()) {
            return true;
        }
        return jj_scan_token(RPAREN);
    }

    static final private boolean jj_3R_229() {
        return jj_3R_165();
    }

    static final private boolean jj_3R_135() {
        return jj_3R_136();
    }

    static final private boolean jj_3_57() {
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        if (jj_3R_136()) {
            return true;
        }
        return jj_scan_token(COLON);
    }

    static final private boolean jj_3R_455() {
        return jj_3R_136();
    }

    static final private boolean jj_3R_456() {
        return jj_3R_132();
    }

    static final private boolean jj_3_56() {
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_135()) {
            jj_scanpos = xsp;
        }
        return jj_scan_token(SEMICOLON);
    }

    static final private boolean jj_3R_163() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_457() {
        return jj_3R_464();
    }

    static final private boolean jj_3R_378() {
        return jj_scan_token(SUPER);
    }

    static final private boolean jj_3R_162() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_377() {
        return jj_scan_token(EXTENDS);
    }

    static final private boolean jj_3R_112() {
        return jj_3R_165();
    }

    static final private boolean jj_3R_444() {
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        if (jj_3R_136()) {
            return true;
        }
        if (jj_scan_token(COLON)) {
            return true;
        }
        return jj_3R_132();
    }

    static final private boolean jj_3R_340() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_377()) {
            jj_scanpos = xsp;
            if (jj_3R_378()) {
                return true;
            }
        }
        return jj_3R_94();
    }

    static final private boolean jj_3R_157() {
        if (jj_scan_token(INTERFACE)) {
            return true;
        }
        if (jj_scan_token(IDENTIFIER)) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_229()) {
            jj_scanpos = xsp;
        }
        xsp = jj_scanpos;
        if (jj_3R_230()) {
            jj_scanpos = xsp;
        }
        if (jj_scan_token(LBRACE)) {
            return true;
        }
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_231()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return jj_scan_token(RBRACE);
    }

    static final private boolean jj_3R_245() {
        if (jj_scan_token(SUPER)) {
            return true;
        }
        if (jj_scan_token(DOT)) {
            return true;
        }
        return jj_scan_token(IDENTIFIER);
    }

    static final private boolean jj_3R_443() {
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_455()) {
            jj_scanpos = xsp;
        }
        if (jj_scan_token(SEMICOLON)) {
            return true;
        }
        xsp = jj_scanpos;
        if (jj_3R_456()) {
            jj_scanpos = xsp;
        }
        if (jj_scan_token(SEMICOLON)) {
            return true;
        }
        xsp = jj_scanpos;
        if (jj_3R_457()) {
            jj_scanpos = xsp;
        }
        return false;
    }

    static final private boolean jj_3R_244() {
        return jj_scan_token(THIS);
    }

    static final private boolean jj_3R_252() {
        if (jj_scan_token(HOOK)) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_340()) {
            jj_scanpos = xsp;
        }
        return false;
    }

    static final private boolean jj_3R_251() {
        return jj_3R_94();
    }

    static final private boolean jj_3R_243() {
        return jj_3R_277();
    }

    static final private boolean jj_3R_164() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_405() {
        if (jj_scan_token(FOR)) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_443()) {
            jj_scanpos = xsp;
            if (jj_3R_444()) {
                return true;
            }
        }
        if (jj_scan_token(RPAREN)) {
            return true;
        }
        return jj_3R_335();
    }

    static final private boolean jj_3R_176() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_251()) {
            jj_scanpos = xsp;
            return jj_3R_252();
        }
        return false;
    }

    static final private boolean jj_3R_228() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_174() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_243()) {
            jj_scanpos = xsp;
            if (jj_3R_244()) {
                jj_scanpos = xsp;
                if (jj_3R_245()) {
                    jj_scanpos = xsp;
                    if (jj_3R_246()) {
                        jj_scanpos = xsp;
                        if (jj_3R_247()) {
                            jj_scanpos = xsp;
                            if (jj_3R_248()) {
                                jj_scanpos = xsp;
                                return jj_3R_249();
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3R_227() {
        return jj_scan_token(STRICTFP);
    }

    static final private boolean jj_3R_226() {
        return jj_scan_token(PRIVATE);
    }

    static final private boolean jj_3R_121() {
        if (jj_scan_token(LT)) {
            return true;
        }
        if (jj_3R_176()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_279()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return jj_scan_token(GT);
    }

    static final private boolean jj_3R_225() {
        return jj_scan_token(PROTECTED);
    }

    static final private boolean jj_3R_224() {
        return jj_scan_token(PUBLIC);
    }

    static final private boolean jj_3R_223() {
        return jj_scan_token(FINAL);
    }

    static final private boolean jj_3R_222() {
        return jj_scan_token(ABSTRACT);
    }

    static final private boolean jj_3R_221() {
        return jj_scan_token(STATIC);
    }

    static final private boolean jj_3R_156() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_221()) {
            jj_scanpos = xsp;
            if (jj_3R_222()) {
                jj_scanpos = xsp;
                if (jj_3R_223()) {
                    jj_scanpos = xsp;
                    if (jj_3R_224()) {
                        jj_scanpos = xsp;
                        if (jj_3R_225()) {
                            jj_scanpos = xsp;
                            if (jj_3R_226()) {
                                jj_scanpos = xsp;
                                if (jj_3R_227()) {
                                    jj_scanpos = xsp;
                                    return jj_3R_228();
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3R_98() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_156()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return jj_3R_157();
    }

    static final private boolean jj_3R_404() {
        if (jj_scan_token(DO)) {
            return true;
        }
        if (jj_3R_335()) {
            return true;
        }
        if (jj_scan_token(WHILE)) {
            return true;
        }
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        if (jj_3R_132()) {
            return true;
        }
        if (jj_scan_token(RPAREN)) {
            return true;
        }
        return jj_scan_token(SEMICOLON);
    }

    static final private boolean jj_3_35() {
        return jj_3R_121();
    }

    static final private boolean jj_3_34() {
        if (jj_scan_token(DOT)) {
            return true;
        }
        if (jj_scan_token(IDENTIFIER)) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3_35()) {
            jj_scanpos = xsp;
        }
        return false;
    }

    static final private boolean jj_3R_111() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_scan_token(50)) {
            jj_scanpos = xsp;
            if (jj_scan_token(49)) {
                jj_scanpos = xsp;
                if (jj_scan_token(48)) {
                    return true;
                }
            }
        }
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_164()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3_33() {
        return jj_3R_121();
    }

    static final private boolean jj_3R_403() {
        if (jj_scan_token(WHILE)) {
            return true;
        }
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        if (jj_3R_132()) {
            return true;
        }
        if (jj_scan_token(RPAREN)) {
            return true;
        }
        return jj_3R_335();
    }

    static final private boolean jj_3R_120() {
        if (jj_scan_token(IDENTIFIER)) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3_33()) {
            jj_scanpos = xsp;
        }
        while (true) {
            xsp = jj_scanpos;
            if (jj_3_34()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3_21() {
        return jj_3R_99();
    }

    static final private boolean jj_3_20() {
        return jj_3R_97();
    }

    static final private boolean jj_3_19() {
        return jj_3R_113();
    }

    static final private boolean jj_3R_110() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_109() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_scan_token(53)) {
            jj_scanpos = xsp;
            if (jj_scan_token(13)) {
                jj_scanpos = xsp;
                if (jj_scan_token(32)) {
                    jj_scanpos = xsp;
                    if (jj_scan_token(50)) {
                        jj_scanpos = xsp;
                        if (jj_scan_token(49)) {
                            jj_scanpos = xsp;
                            if (jj_scan_token(48)) {
                                jj_scanpos = xsp;
                                if (jj_scan_token(67)) {
                                    jj_scanpos = xsp;
                                    return jj_3R_163();
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3_18() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_110()) {
                jj_scanpos = xsp;
                break;
            }
        }
        xsp = jj_scanpos;
        if (jj_3R_111()) {
            jj_scanpos = xsp;
        }
        xsp = jj_scanpos;
        if (jj_3R_112()) {
            jj_scanpos = xsp;
        }
        if (jj_scan_token(IDENTIFIER)) {
            return true;
        }
        return jj_scan_token(LPAREN);
    }

    static final private boolean jj_3R_108() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_scan_token(53)) {
            jj_scanpos = xsp;
            if (jj_scan_token(13)) {
                jj_scanpos = xsp;
                if (jj_scan_token(32)) {
                    jj_scanpos = xsp;
                    if (jj_scan_token(50)) {
                        jj_scanpos = xsp;
                        if (jj_scan_token(49)) {
                            jj_scanpos = xsp;
                            if (jj_scan_token(48)) {
                                jj_scanpos = xsp;
                                if (jj_scan_token(67)) {
                                    jj_scanpos = xsp;
                                    return jj_3R_162();
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3_17() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_109()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return jj_scan_token(INTERFACE);
    }

    static final private boolean jj_3R_305() {
        if (jj_3R_95()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3_16() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_108()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return jj_scan_token(CLASS);
    }

    static final private boolean jj_3R_304() {
        if (jj_3R_99()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_303() {
        if (jj_3R_97()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_302() {
        if (jj_3R_334()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_301() {
        if (jj_3R_333()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3_32() {
        if (jj_scan_token(DOT)) {
            return true;
        }
        return jj_scan_token(IDENTIFIER);
    }

    static final private boolean jj_3R_442() {
        if (jj_scan_token(ELSE)) {
            return true;
        }
        return jj_3R_335();
    }

    static final private boolean jj_3R_300() {
        if (jj_3R_98()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_299() {
        if (jj_3R_96()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3_15() {
        if (jj_3R_107()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_269() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3_15()) {
            jj_scanpos = xsp;
            if (jj_3R_299()) {
                jj_scanpos = xsp;
                if (jj_3R_300()) {
                    jj_scanpos = xsp;
                    if (jj_3R_301()) {
                        jj_scanpos = xsp;
                        if (jj_3R_302()) {
                            jj_scanpos = xsp;
                            if (jj_3R_303()) {
                                jj_scanpos = xsp;
                                if (jj_3R_304()) {
                                    jj_scanpos = xsp;
                                    return jj_3R_305();
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3R_139() {
        if (jj_scan_token(IDENTIFIER)) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3_32()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_402() {
        if (jj_scan_token(IF)) {
            return true;
        }
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        if (jj_3R_132()) {
            return true;
        }
        if (jj_scan_token(RPAREN)) {
            return true;
        }
        if (jj_3R_335()) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_442()) {
            jj_scanpos = xsp;
        }
        return false;
    }

    static final private boolean jj_3R_215() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_214() {
        return jj_scan_token(STRICTFP);
    }

    static final private boolean jj_3R_213() {
        return jj_scan_token(PRIVATE);
    }

    static final private boolean jj_3R_186() {
        return jj_3R_94();
    }

    static final private boolean jj_3R_212() {
        return jj_scan_token(PROTECTED);
    }

    static final private boolean jj_3R_211() {
        return jj_scan_token(PUBLIC);
    }

    static final private boolean jj_3R_210() {
        return jj_scan_token(FINAL);
    }

    static final private boolean jj_3R_209() {
        return jj_scan_token(ABSTRACT);
    }

    static final private boolean jj_3R_208() {
        return jj_scan_token(STATIC);
    }

    static final private boolean jj_3R_151() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_208()) {
            jj_scanpos = xsp;
            if (jj_3R_209()) {
                jj_scanpos = xsp;
                if (jj_3R_210()) {
                    jj_scanpos = xsp;
                    if (jj_3R_211()) {
                        jj_scanpos = xsp;
                        if (jj_3R_212()) {
                            jj_scanpos = xsp;
                            if (jj_3R_213()) {
                                jj_scanpos = xsp;
                                if (jj_3R_214()) {
                                    jj_scanpos = xsp;
                                    return jj_3R_215();
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3R_185() {
        return jj_scan_token(VOID);
    }

    static final private boolean jj_3R_96() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_151()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return jj_3R_152();
    }

    static final private boolean jj_3R_129() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_185()) {
            jj_scanpos = xsp;
            return jj_3R_186();
        }
        return false;
    }

    static final private boolean jj_3R_450() {
        if (jj_scan_token(COLON)) {
            return true;
        }
        return jj_3R_132();
    }

    static final private boolean jj_3R_412() {
        if (jj_scan_token(ASSERT)) {
            return true;
        }
        if (jj_3R_132()) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_450()) {
            jj_scanpos = xsp;
        }
        return jj_scan_token(SEMICOLON);
    }

    static final private boolean jj_3R_265() {
        return jj_3R_269();
    }

    static final private boolean jj_3R_219() {
        if (jj_scan_token(LBRACE)) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_265()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return jj_scan_token(RBRACE);
    }

    static final private boolean jj_3_43() {
        return jj_3R_128();
    }

    static final private boolean jj_3R_126() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_scan_token(16)) {
            jj_scanpos = xsp;
            if (jj_scan_token(21)) {
                jj_scanpos = xsp;
                if (jj_scan_token(18)) {
                    jj_scanpos = xsp;
                    if (jj_scan_token(52)) {
                        jj_scanpos = xsp;
                        if (jj_scan_token(41)) {
                            jj_scanpos = xsp;
                            if (jj_scan_token(43)) {
                                jj_scanpos = xsp;
                                if (jj_scan_token(34)) {
                                    jj_scanpos = xsp;
                                    return jj_scan_token(27);
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3R_263() {
        if (jj_scan_token(LBRACKET)) {
            return true;
        }
        return jj_scan_token(RBRACKET);
    }

    static final private boolean jj_3R_463() {
        if (jj_scan_token(_DEFAULT)) {
            return true;
        }
        return jj_scan_token(COLON);
    }

    static final private boolean jj_3R_254() {
        return jj_3R_277();
    }

    static final private boolean jj_3R_262() {
        return jj_3R_139();
    }

    static final private boolean jj_3R_261() {
        return jj_3R_126();
    }

    static final private boolean jj_3R_197() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_261()) {
            jj_scanpos = xsp;
            if (jj_3R_262()) {
                return true;
            }
        }
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_263()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_218() {
        if (jj_scan_token(IMPLEMENTS)) {
            return true;
        }
        return jj_3R_188();
    }

    static final private boolean jj_3R_462() {
        if (jj_scan_token(CASE)) {
            return true;
        }
        if (jj_3R_132()) {
            return true;
        }
        return jj_scan_token(COLON);
    }

    static final private boolean jj_3R_147() {
        return jj_3R_197();
    }

    static final private boolean jj_3R_453() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_462()) {
            jj_scanpos = xsp;
            return jj_3R_463();
        }
        return false;
    }

    static final private boolean jj_3_31() {
        return jj_3R_120();
    }

    static final private boolean jj_3R_196() {
        if (jj_scan_token(LBRACKET)) {
            return true;
        }
        return jj_scan_token(RBRACKET);
    }

    static final private boolean jj_3R_118() {
        if (jj_3R_174()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3_43()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_217() {
        if (jj_scan_token(EXTENDS)) {
            return true;
        }
        return jj_3R_120();
    }

    static final private boolean jj_3R_146() {
        if (jj_3R_120()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_196()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_216() {
        return jj_3R_165();
    }

    static final private boolean jj_3R_94() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_146()) {
            jj_scanpos = xsp;
            return jj_3R_147();
        }
        return false;
    }

    static final private boolean jj_3_42() {
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        return jj_3R_126();
    }

    static final private boolean jj_3R_454() {
        return jj_3R_273();
    }

    static final private boolean jj_3R_152() {
        if (jj_scan_token(CLASS)) {
            return true;
        }
        if (jj_scan_token(IDENTIFIER)) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_216()) {
            jj_scanpos = xsp;
        }
        xsp = jj_scanpos;
        if (jj_3R_217()) {
            jj_scanpos = xsp;
        }
        xsp = jj_scanpos;
        if (jj_3R_218()) {
            jj_scanpos = xsp;
        }
        return jj_3R_219();
    }

    static final private boolean jj_3R_483() {
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        if (jj_3R_94()) {
            return true;
        }
        if (jj_scan_token(RPAREN)) {
            return true;
        }
        return jj_3R_474();
    }

    static final private boolean jj_3R_482() {
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        if (jj_3R_94()) {
            return true;
        }
        if (jj_scan_token(RPAREN)) {
            return true;
        }
        return jj_3R_458();
    }

    static final private boolean jj_3R_441() {
        if (jj_3R_453()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_454()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return false;
    }

    static final private boolean jj_3R_480() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_482()) {
            jj_scanpos = xsp;
            return jj_3R_483();
        }
        return false;
    }

    static final private boolean jj_3R_401() {
        if (jj_scan_token(SWITCH)) {
            return true;
        }
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        if (jj_3R_132()) {
            return true;
        }
        if (jj_scan_token(RPAREN)) {
            return true;
        }
        if (jj_scan_token(LBRACE)) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_441()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return jj_scan_token(RBRACE);
    }

    static final private boolean jj_3R_127() {
        if (jj_scan_token(LBRACKET)) {
            return true;
        }
        return jj_scan_token(RBRACKET);
    }

    static final private boolean jj_3R_160() {
        return jj_scan_token(STATIC);
    }

    static final private boolean jj_3R_486() {
        return jj_scan_token(DECR);
    }

    static final private boolean jj_3R_107() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_160()) {
            jj_scanpos = xsp;
        }
        return jj_3R_161();
    }

    static final private boolean jj_3R_253() {
        if (jj_scan_token(LBRACKET)) {
            return true;
        }
        return jj_scan_token(RBRACKET);
    }

    static final private boolean jj_3R_485() {
        return jj_scan_token(INCR);
    }

    static final private boolean jj_3R_484() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_485()) {
            jj_scanpos = xsp;
            return jj_3R_486();
        }
        return false;
    }

    static final private boolean jj_3R_481() {
        if (jj_3R_118()) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_484()) {
            jj_scanpos = xsp;
        }
        return false;
    }

    static final private boolean jj_3_41() {
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        if (jj_3R_120()) {
            return true;
        }
        return jj_scan_token(LBRACKET);
    }

    static final private boolean jj_3R_383() {
        if (jj_3R_257()) {
            return true;
        }
        return jj_3R_132();
    }

    static final private boolean jj_3_40() {
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        if (jj_3R_126()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_127()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return jj_scan_token(RPAREN);
    }

    static final private boolean jj_3R_181() {
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        if (jj_3R_120()) {
            return true;
        }
        if (jj_scan_token(RPAREN)) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_scan_token(91)) {
            jj_scanpos = xsp;
            if (jj_scan_token(90)) {
                jj_scanpos = xsp;
                if (jj_scan_token(79)) {
                    jj_scanpos = xsp;
                    if (jj_scan_token(76)) {
                        jj_scanpos = xsp;
                        if (jj_scan_token(57)) {
                            jj_scanpos = xsp;
                            if (jj_scan_token(54)) {
                                jj_scanpos = xsp;
                                if (jj_scan_token(45)) {
                                    jj_scanpos = xsp;
                                    return jj_3R_254();
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static final private boolean jj_3R_382() {
        return jj_scan_token(DECR);
    }

    static final private boolean jj_3R_180() {
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        if (jj_3R_120()) {
            return true;
        }
        if (jj_scan_token(LBRACKET)) {
            return true;
        }
        return jj_scan_token(RBRACKET);
    }

    static final private boolean jj_3_30() {
        if (jj_scan_token(THIS)) {
            return true;
        }
        if (jj_3R_119()) {
            return true;
        }
        return jj_scan_token(SEMICOLON);
    }

    static final private boolean jj_3_29() {
        if (jj_3R_118()) {
            return true;
        }
        return jj_scan_token(DOT);
    }

    static final private boolean jj_3R_381() {
        return jj_scan_token(INCR);
    }

    static final private boolean jj_3R_345() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_381()) {
            jj_scanpos = xsp;
            if (jj_3R_382()) {
                jj_scanpos = xsp;
                return jj_3R_383();
            }
        }
        return false;
    }

    static final private boolean jj_3R_173() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3_29()) {
            jj_scanpos = xsp;
        }
        if (jj_scan_token(SUPER)) {
            return true;
        }
        if (jj_3R_119()) {
            return true;
        }
        return jj_scan_token(SEMICOLON);
    }

    static final private boolean jj_3R_125() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_179()) {
            jj_scanpos = xsp;
            if (jj_3R_180()) {
                jj_scanpos = xsp;
                return jj_3R_181();
            }
        }
        return false;
    }

    static final private boolean jj_3R_179() {
        if (jj_scan_token(LPAREN)) {
            return true;
        }
        if (jj_3R_126()) {
            return true;
        }
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_253()) {
                jj_scanpos = xsp;
                break;
            }
        }
        return jj_scan_token(RPAREN);
    }

    static final private boolean jj_3R_332() {
        if (jj_3R_118()) {
            return true;
        }
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_345()) {
            jj_scanpos = xsp;
        }
        return false;
    }

    static final private boolean jj_3R_267() {
        return jj_3R_119();
    }

    static final private boolean jj_3R_331() {
        return jj_3R_344();
    }

    static final private boolean jj_3R_330() {
        return jj_3R_343();
    }

    static final private boolean jj_3R_172() {
        if (jj_scan_token(THIS)) {
            return true;
        }
        if (jj_3R_119()) {
            return true;
        }
        return jj_scan_token(SEMICOLON);
    }

    static final private boolean jj_3_39() {
        return jj_3R_125();
    }

    static final private boolean jj_3R_117() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_172()) {
            jj_scanpos = xsp;
            return jj_3R_173();
        }
        return false;
    }

    static final private boolean jj_3R_297() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_330()) {
            jj_scanpos = xsp;
            if (jj_3R_331()) {
                jj_scanpos = xsp;
                return jj_3R_332();
            }
        }
        return false;
    }

    static final private boolean jj_3R_268() {
        return jj_3R_219();
    }

    static final private boolean jj_3R_477() {
        return jj_3R_481();
    }

    static final private boolean jj_3R_159() {
        return jj_3R_144();
    }

    static final private boolean jj_3R_476() {
        return jj_3R_480();
    }

    static final private boolean jj_3R_479() {
        return jj_scan_token(BANG);
    }

    static final private boolean jj_3R_478() {
        return jj_scan_token(TILDE);
    }

    static final private boolean jj_3R_106() {
        Token xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_159()) {
                jj_scanpos = xsp;
                break;
            }
        }
        if (jj_scan_token(IDENTIFIER)) {
            return true;
        }
        xsp = jj_scanpos;
        if (jj_3R_267()) {
            jj_scanpos = xsp;
        }
        xsp = jj_scanpos;
        if (jj_3R_268()) {
            jj_scanpos = xsp;
        }
        return false;
    }

    static final private boolean jj_3R_475() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_478()) {
            jj_scanpos = xsp;
            if (jj_3R_479()) {
                return true;
            }
        }
        return jj_3R_458();
    }

    static final private boolean jj_3R_474() {
        Token xsp;
        xsp = jj_scanpos;
        if (jj_3R_475()) {
            jj_scanpos = xsp;
            if (jj_3R_476()) {
                jj_scanpos = xsp;
                return jj_3R_477();
            }
        }
        return false;
    }

    static final private boolean jj_3R_400() {
        return jj_scan_token(SEMICOLON);
    }

    static final private boolean jj_3_28() {
        return jj_3R_117();
    }

    static final private boolean jj_3R_353() {
        return jj_3R_273();
    }

    private static void jj_la1_0() {
        jj_la1_0 = new int[] { 0x0, 0x2040a000, 0x0, 0x2040a000, 0x8000, 0x0, 0x0, 0x0, 0xa000,
            0x2865a000, 0xa000, 0xa000, 0x2000000, 0x0, 0x8000, 0x0, 0x8000, 0x0, 0x2865a000, 0x0,
            0x8000, 0x0, 0x0, 0xa000, 0xa000, 0x0, 0x40000000, 0x0, 0x2865a000, 0xa000, 0xa000, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x8258000, 0xa000, 0xa000, 0xa000, 0xa000, 0x0,
            0x40000000, 0x2865a000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x8258000, 0x8000, 0x8000, 0x0,
            0x0, 0x0, 0x88250000, 0x88250000, 0x0, 0xa000, 0xa000, 0x0, 0x0, 0x0, 0xa000, 0xa000,
            0x0, 0x0, 0x0, 0x8258000, 0x8000, 0x8000, 0x0, 0x0, 0x8000, 0x0, 0x8000, 0x0, 0x0, 0x0,
            0x8d67c000, 0x88250000, 0x0, 0x0, 0x8250000, 0x8250000, 0x0, 0x8250000, 0x8250000, 0x0,
            0x40000000, 0x40000000, 0x8250000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x88250000, 0x0, 0x0, 0x88250000, 0x0,
            0x80000000, 0x0, 0x0, 0x0, 0x0, 0x80000000, 0x0, 0x0, 0x80000000, 0x80000000,
            0x88250000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x8d274000, 0x8d67c000, 0x8d674000, 0x8000,
            0x8000, 0x0, 0x0, 0x0, 0x0, 0x88250000, 0x2080000, 0x8d67c000, 0x2080000, 0x0,
            0x10000000, 0x88258000, 0x88250000, 0x88250000, 0x88250000, 0x0, 0x0, 0x0, 0x88250000,
            0x100000, 0x0, 0x8d67c000, 0x0, 0x88258000, 0x0, 0x0, 0x88258000, 0x88258000, 0x0,
            0x40000000, 0x0, };
    }

    private static void jj_la1_1() {
        jj_la1_1 = new int[] { 0x80, 0x270401, 0x80, 0x270401, 0x0, 0x200000, 0x0, 0x0, 0x270000,
            0x10370e05, 0x40000, 0x40000, 0x0, 0x0, 0x270000, 0x40, 0x0, 0x0, 0x91371e05, 0x0, 0x0,
            0x0, 0x0, 0x40001, 0x40001, 0x0, 0x0, 0x40, 0x91371e05, 0x270001, 0x270001, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x10370a05, 0x40000, 0x40000, 0x270001, 0x270001, 0x0,
            0x0, 0x91371e05, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x10370a05, 0x10270001, 0x10270001, 0x0,
            0x0, 0x0, 0xa2506a04, 0xa2506a04, 0x0, 0x1271001, 0x1271001, 0x0, 0x8000000, 0x0,
            0x1271001, 0x1271001, 0x0, 0x0, 0x0, 0x100a05, 0x0, 0x0, 0x1, 0x0, 0x0, 0x70000, 0x0,
            0x70000, 0x0, 0x8000000, 0xe7d86a2d, 0xa2506a04, 0x200000, 0x0, 0x100a04, 0x100a04, 0x0,
            0x100a04, 0x80100a04, 0x0, 0x400000, 0x400000, 0x100a04, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x100, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xa2506a04, 0x0,
            0x0, 0xa2506a04, 0x0, 0x22406000, 0x0, 0x0, 0x0, 0x0, 0x22406000, 0x0, 0x0, 0x20004000,
            0x20000000, 0xa2506a04, 0x0, 0x0, 0x0, 0x2000, 0x0, 0x0, 0xe7d86a2c, 0xe7d86a2d,
            0xe7d86a2c, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0xa2506a04, 0x0, 0xe7d86a2d, 0x0, 0x0, 0x0,
            0xa2506a05, 0xa2506a04, 0xa2506a04, 0xa2506a04, 0x0, 0x0, 0x0, 0xa2506a04, 0x0, 0x2,
            0xe7d86a2d, 0x0, 0xa2506a04, 0x0, 0x0, 0xa2506a04, 0xa2506a04, 0x0, 0x0, 0x0, };
    }

    private static void jj_la1_2() {
        jj_la1_2 = new int[] { 0x0, 0x200008, 0x0, 0x200008, 0x0, 0x0, 0x800000, 0x200000, 0x8,
            0x201009, 0x0, 0x0, 0x0, 0x200000, 0x8, 0x0, 0x1000, 0x400000, 0x2021009, 0x200000, 0x0,
            0x8000, 0x20000, 0x8, 0x8, 0x2000000, 0x0, 0x0, 0x2021009, 0x8, 0x8, 0x200000, 0x200000,
            0x200000, 0x200000, 0x200000, 0x200000, 0x200000, 0x200000, 0x1001, 0x8, 0x8, 0x8, 0x8,
            0x2000000, 0x0, 0x2001009, 0x200000, 0x200000, 0x200000, 0x200000, 0x200000, 0x200000,
            0x1001, 0x1, 0x1, 0x400000, 0x1000000, 0x80000, 0xc029d10, 0xc029d10, 0x400000, 0x8,
            0x8, 0x2000000, 0x0, 0x220000, 0x8, 0x8, 0x2000000, 0x80000, 0x400000, 0x1000, 0x0, 0x0,
            0x0, 0x4, 0x0, 0x0, 0x0, 0x0, 0x2000000, 0x0, 0x229d12, 0x9d10, 0x0, 0x80000, 0x1000,
            0x1000, 0x80000, 0x0, 0x1000, 0x400000, 0x0, 0x0, 0x10001000, 0x400000, 0x1000000,
            0x1000000, 0x10000000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x40000000, 0x40000000, 0x0, 0x82000000,
            0x82000000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xc009d10, 0xc000000, 0xc000000, 0x9d10,
            0x80000, 0xc009d10, 0x8000, 0x0, 0x0, 0x8000, 0x8d10, 0x1000, 0x888000, 0xd10, 0x0,
            0xc009d10, 0x2000000, 0x20000, 0x88000, 0x0, 0x80000, 0x80000, 0x229d12, 0x229d12,
            0x229d12, 0x0, 0x0, 0x0, 0x400000, 0x1000000, 0x1000000, 0x9d10, 0x0, 0x229d12, 0x0,
            0x20000000, 0x0, 0x9d10, 0xc009d10, 0x9d10, 0x9d10, 0x400000, 0x1000, 0x1000, 0xc009d10,
            0x0, 0x0, 0x229d12, 0x400000, 0xc029d10, 0x8000, 0x400000, 0xc029d10, 0xc029d10,
            0x400000, 0x0, 0x0, };
    }

    private static void jj_la1_3() {
        jj_la1_3 = new int[] { 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xf0, 0xf0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x30, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x3ff8000,
            0x3ff8000, 0x0, 0x4, 0x8, 0x800, 0x1000, 0x400, 0x2, 0x2, 0x0, 0x10000001, 0x10000001,
            0x4000, 0xc0, 0xc0, 0x2300, 0x2300, 0xc0, 0xf0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x30,
            0x30, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xf0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x30, 0x30,
            0x30, 0x0, 0x0, 0x0, 0x0, 0x3ff8030, 0x3ff8030, 0x30, 0x0, 0x30, 0x0, 0x0, 0x0, 0x30,
            0xf0, 0x30, 0x30, 0x0, 0x0, 0x0, 0xf0, 0x0, 0x0, 0x30, 0x0, 0xf0, 0x0, 0x0, 0xf0, 0xf0,
            0x0, 0x0, 0x400, };
    }

    static public void ReInit(java.io.InputStream stream) {
        ReInit(stream, null);
    }

    static public void ReInit(java.io.InputStream stream, String encoding) {
        try {
            jj_input_stream.ReInit(stream, encoding, 1, 1);
        } catch (java.io.UnsupportedEncodingException e) {
            throw new RuntimeException(e);
        }
        JavaCCParserTokenManager.ReInit(jj_input_stream);
        token = new Token();
        jj_ntk = -1;
        jj_gen = 0;
        for (int i = 0; i < 173; i++) {
            jj_la1[i] = -1;
        }
        for (int i = 0; i < jj_2_rtns.length; i++) {
            jj_2_rtns[i] = new JJCalls();
        }
    }

    static public void ReInit(java.io.Reader stream) {
        jj_input_stream.ReInit(stream, 1, 1);
        JavaCCParserTokenManager.ReInit(jj_input_stream);
        token = new Token();
        jj_ntk = -1;
        jj_gen = 0;
        for (int i = 0; i < 173; i++) {
            jj_la1[i] = -1;
        }
        for (int i = 0; i < jj_2_rtns.length; i++) {
            jj_2_rtns[i] = new JJCalls();
        }
    }

    static final private Token jj_consume_token(int kind) throws ParseException {
        Token oldToken;
        if ((oldToken = token).next != null) {
            token = token.next;
        } else {
            token = token.next = JavaCCParserTokenManager.getNextToken();
        }
        jj_ntk = -1;
        if (token.kind == kind) {
            jj_gen++;
            if (++jj_gc > 100) {
                jj_gc = 0;
                for (JJCalls jj_2_rtn : jj_2_rtns) {
                    JJCalls c = jj_2_rtn;
                    while (c != null) {
                        if (c.gen < jj_gen) {
                            c.first = null;
                        }
                        c = c.next;
                    }
                }
            }
            return token;
        }
        token = oldToken;
        jj_kind = kind;
        throw generateParseException();
    }

    static final private boolean jj_scan_token(int kind) {
        if (jj_scanpos == jj_lastpos) {
            jj_la--;
            if (jj_scanpos.next == null) {
                jj_lastpos = jj_scanpos = jj_scanpos.next = JavaCCParserTokenManager.getNextToken();
            } else {
                jj_lastpos = jj_scanpos = jj_scanpos.next;
            }
        } else {
            jj_scanpos = jj_scanpos.next;
        }
        if (jj_rescan) {
            int i = 0;
            Token tok = token;
            while (tok != null && tok != jj_scanpos) {
                i++;
                tok = tok.next;
            }
            if (tok != null) {
                jj_add_error_token(kind, i);
            }
        }
        if (jj_scanpos.kind != kind) {
            return true;
        }
        if (jj_la == 0 && jj_scanpos == jj_lastpos) {
            throw jj_ls;
        }
        return false;
    }

    static final public Token getNextToken() {
        if (token.next != null) {
            token = token.next;
        } else {
            token = token.next = JavaCCParserTokenManager.getNextToken();
        }
        jj_ntk = -1;
        jj_gen++;
        return token;
    }

    static final public Token getToken(int index) {
        Token t = lookingAhead ? jj_scanpos : token;
        for (int i = 0; i < index; i++) {
            if (t.next != null) {
                t = t.next;
            } else {
                t = t.next = JavaCCParserTokenManager.getNextToken();
            }
        }
        return t;
    }

    static final private int jj_ntk() {
        if ((jj_nt = token.next) == null) {
            return (jj_ntk = (token.next = JavaCCParserTokenManager.getNextToken()).kind);
        } else {
            return (jj_ntk = jj_nt.kind);
        }
    }

    static private void jj_add_error_token(int kind, int pos) {
        if (pos >= 100) {
            return;
        }
        if (pos == jj_endpos + 1) {
            jj_lasttokens[jj_endpos++] = kind;
        } else if (jj_endpos != 0) {
            jj_expentry = new int[jj_endpos];
            for (int i = 0; i < jj_endpos; i++) {
                jj_expentry[i] = jj_lasttokens[i];
            }
            boolean exists = false;
            for (java.util.Enumeration e = jj_expentries.elements(); e.hasMoreElements();) {
                int[] oldentry = (int[]) (e.nextElement());
                if (oldentry.length == jj_expentry.length) {
                    exists = true;
                    for (int i = 0; i < jj_expentry.length; i++) {
                        if (oldentry[i] != jj_expentry[i]) {
                            exists = false;
                            break;
                        }
                    }
                    if (exists) {
                        break;
                    }
                }
            }
            if (!exists) {
                jj_expentries.addElement(jj_expentry);
            }
            if (pos != 0) {
                jj_lasttokens[(jj_endpos = pos) - 1] = kind;
            }
        }
    }

    static public ParseException generateParseException() {
        jj_expentries.removeAllElements();
        boolean[] la1tokens = new boolean[125];
        for (int i = 0; i < 125; i++) {
            la1tokens[i] = false;
        }
        if (jj_kind >= 0) {
            la1tokens[jj_kind] = true;
            jj_kind = -1;
        }
        for (int i = 0; i < 173; i++) {
            if (jj_la1[i] == jj_gen) {
                for (int j = 0; j < 32; j++) {
                    if ((jj_la1_0[i] & (1 << j)) != 0) {
                        la1tokens[j] = true;
                    }
                    if ((jj_la1_1[i] & (1 << j)) != 0) {
                        la1tokens[32 + j] = true;
                    }
                    if ((jj_la1_2[i] & (1 << j)) != 0) {
                        la1tokens[64 + j] = true;
                    }
                    if ((jj_la1_3[i] & (1 << j)) != 0) {
                        la1tokens[96 + j] = true;
                    }
                }
            }
        }
        for (int i = 0; i < 125; i++) {
            if (la1tokens[i]) {
                jj_expentry = new int[1];
                jj_expentry[0] = i;
                jj_expentries.addElement(jj_expentry);
            }
        }
        jj_endpos = 0;
        jj_rescan_token();
        jj_add_error_token(0, 0);
        int[][] exptokseq = new int[jj_expentries.size()][];
        for (int i = 0; i < jj_expentries.size(); i++) {
            exptokseq[i] = (int[]) jj_expentries.elementAt(i);
        }
        return new ParseException(token, exptokseq, tokenImage);
    }

    static final public void enable_tracing() {
    }

    static final public void disable_tracing() {
    }

    static final private void jj_rescan_token() {
        jj_rescan = true;
        for (int i = 0; i < 62; i++) {
            try {
                JJCalls p = jj_2_rtns[i];
                do {
                    if (p.gen > jj_gen) {
                        jj_la = p.arg;
                        jj_lastpos = jj_scanpos = p.first;
                        switch (i) {
                        case 0:
                            jj_3_1();
                            break;
                        case 1:
                            jj_3_2();
                            break;
                        case 2:
                            jj_3_3();
                            break;
                        case 3:
                            jj_3_4();
                            break;
                        case 4:
                            jj_3_5();
                            break;
                        case 5:
                            jj_3_6();
                            break;
                        case 6:
                            jj_3_7();
                            break;
                        case 7:
                            jj_3_8();
                            break;
                        case 8:
                            jj_3_9();
                            break;
                        case 9:
                            jj_3_10();
                            break;
                        case 10:
                            jj_3_11();
                            break;
                        case 11:
                            jj_3_12();
                            break;
                        case 12:
                            jj_3_13();
                            break;
                        case 13:
                            jj_3_14();
                            break;
                        case 14:
                            jj_3_15();
                            break;
                        case 15:
                            jj_3_16();
                            break;
                        case 16:
                            jj_3_17();
                            break;
                        case 17:
                            jj_3_18();
                            break;
                        case 18:
                            jj_3_19();
                            break;
                        case 19:
                            jj_3_20();
                            break;
                        case 20:
                            jj_3_21();
                            break;
                        case 21:
                            jj_3_22();
                            break;
                        case 22:
                            jj_3_23();
                            break;
                        case 23:
                            jj_3_24();
                            break;
                        case 24:
                            jj_3_25();
                            break;
                        case 25:
                            jj_3_26();
                            break;
                        case 26:
                            jj_3_27();
                            break;
                        case 27:
                            jj_3_28();
                            break;
                        case 28:
                            jj_3_29();
                            break;
                        case 29:
                            jj_3_30();
                            break;
                        case 30:
                            jj_3_31();
                            break;
                        case 31:
                            jj_3_32();
                            break;
                        case 32:
                            jj_3_33();
                            break;
                        case 33:
                            jj_3_34();
                            break;
                        case 34:
                            jj_3_35();
                            break;
                        case 35:
                            jj_3_36();
                            break;
                        case 36:
                            jj_3_37();
                            break;
                        case 37:
                            jj_3_38();
                            break;
                        case 38:
                            jj_3_39();
                            break;
                        case 39:
                            jj_3_40();
                            break;
                        case 40:
                            jj_3_41();
                            break;
                        case 41:
                            jj_3_42();
                            break;
                        case 42:
                            jj_3_43();
                            break;
                        case 43:
                            jj_3_44();
                            break;
                        case 44:
                            jj_3_45();
                            break;
                        case 45:
                            jj_3_46();
                            break;
                        case 46:
                            jj_3_47();
                            break;
                        case 47:
                            jj_3_48();
                            break;
                        case 48:
                            jj_3_49();
                            break;
                        case 49:
                            jj_3_50();
                            break;
                        case 50:
                            jj_3_51();
                            break;
                        case 51:
                            jj_3_52();
                            break;
                        case 52:
                            jj_3_53();
                            break;
                        case 53:
                            jj_3_54();
                            break;
                        case 54:
                            jj_3_55();
                            break;
                        case 55:
                            jj_3_56();
                            break;
                        case 56:
                            jj_3_57();
                            break;
                        case 57:
                            jj_3_58();
                            break;
                        case 58:
                            jj_3_59();
                            break;
                        case 59:
                            jj_3_60();
                            break;
                        case 60:
                            jj_3_61();
                            break;
                        case 61:
                            jj_3_62();
                            break;
                        }
                    }
                    p = p.next;
                } while (p != null);
            } catch (LookaheadSuccess ls) {
            }
        }
        jj_rescan = false;
    }

    static final private void jj_save(int index, int xla) {
        JJCalls p = jj_2_rtns[index];
        while (p.gen > jj_gen) {
            if (p.next == null) {
                p = p.next = new JJCalls();
                break;
            }
            p = p.next;
        }
        p.gen = jj_gen + xla - jj_la;
        p.first = token;
        p.arg = xla;
    }

    public void ReInit(JavaCCParserTokenManager tm) {
        token_source = tm;
        token = new Token();
        jj_ntk = -1;
        jj_gen = 0;
        for (int i = 0; i < 173; i++) {
            jj_la1[i] = -1;
        }
        for (int i = 0; i < jj_2_rtns.length; i++) {
            jj_2_rtns[i] = new JJCalls();
        }
    }

    /**
     * inner class that is only used to return results from primary suffix syntax rule
     *
     * @author RN
     */
    static class PrimarySuffixReturnValue {

        // the following constants represent the various sub rules

        /**
         * indicates that the result is currently undefined
         */
        static final int UNDEFINED = -1;
        /**
         * production was
         *
         * <pre>
         * "." "this"
         * </pre>
         */
        static final int THIS = 0;
        /**
         * production was
         *
         * <pre>
         * "." AllocationExpression
         * </pre>
         */
        static final int ALLOCATION_EXPR = 1;
        /**
         * production was
         *
         * <pre>
         * "[" Expression "]"
         * </pre>
         */
        static final int INDEX_EXPR = 2;
        /**
         * production was
         *
         * <pre>
         * "." <IDENTIFIER>
         * </pre>
         */
        static final int IDENTIFIER = 3;
        /**
         * production was
         *
         * <pre>
         * Arguments
         * </pre>
         */
        static final int ARGUMENTS = 4;
        /**
         * production was
         *
         * <pre>
         * super
         * </pre>
         */
        static final int SUPER = 5;

        /**
         * indicates the type of the result
         */
        int type = UNDEFINED;

        /**
         * valid iff <tt>type</tt> is <tt>ALLOCATION_EXPR</tt> or <tt>INDEX_EXPR</tt>
         */
        Expression expr = null;

        /**
         * valid iff <tt>type</tt> is <tt>IDENTIFIER</tt>
         */
        Identifier id = null;

        /**
         * valid iff <tt>type</tt> is <tt>ARGUMENTS</tt>
         */
        ASTList<Expression> args = null;

        /**
         * valid iff <tt>type</tt> is <tt>IDENTIFIER</tt> and it is an explicit generic method
         * invocation
         */
        ASTList<TypeArgumentDeclaration> typeArgs = null;
    }

    /**
     * inner class that is only used to return results from primary prefix syntax rule
     *
     * @author RN
     */
    static class PrimaryPrefixReturnValue {

        // the following constants represent the various sub rules

        /**
         * indicates that the result is currently undefined
         */
        static final int UNDEFINED = -1;
        /**
         * production was
         *
         * <pre>
         * Literal
         * </pre>
         */
        static final int LITERAL = 0;
        /**
         * production was
         *
         * <pre>
         * "this"
         * </pre>
         */
        static final int THIS = 1;
        /**
         * production was
         *
         * <pre>
         * "super" "." <IDENTIFIER>
         * </pre>
         */
        static final int SUPER_MEMBER = 2;
        /**
         * production was
         *
         * <pre>
         * "(" Expression ")"
         * </pre>
         */
        static final int PARENTHESIZED_EXPR = 3;
        /**
         * production was
         *
         * <pre>
         * AllocationExpression
         * </pre>
         */
        static final int ALLOCATION_EXPR = 4;
        /**
         * production was
         *
         * <pre>
         * ResultType "." "class"
         * </pre>
         */
        static final int CLASS_REF = 5;
        /**
         * production was
         *
         * <pre>
         * Name
         * </pre>
         */
        static final int QUALIFIED_NAME = 6;

        /**
         * indicates the type of the result
         */
        int type = UNDEFINED;

        /**
         * valid iff <tt>type</tt> is <tt>LITERAL</tt>
         */
        Literal literal = null;

        /**
         * valid iff <tt>type</tt> is <tt>PARENTHESED_EXPR</tt> or <tt>ALLOCATION_EXPR</tt>
         */
        Expression expr = null;

        /**
         * valid iff <tt>type</tt> is <tt>CLASS_REF</tt>
         */
        TypeReference typeref = null;

        /**
         * valid iff <tt>type</tt> is <tt>QUALIFIED_NAME</tt> or <tt>SUPER_MEMBER</tt>
         */
        UncollatedReferenceQualifier name = null;
    }

    static private final class LookaheadSuccess extends java.lang.Error {
    }

    static final class JJCalls {
        int gen;
        Token first;
        int arg;
        JJCalls next;
    }

}
