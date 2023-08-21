/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import java.io.IOException;
import java.io.Reader;
import java.util.List;

import de.uka.ilkd.key.java.recoderext.adt.MethodSignature;
import de.uka.ilkd.key.parser.proofjava.ParseException;
import de.uka.ilkd.key.parser.proofjava.ProofJavaParser;

import recoder.ParserException;
import recoder.ServiceConfiguration;
import recoder.convenience.TreeWalker;
import recoder.io.ProjectSettings;
import recoder.io.PropertyNames;
import recoder.java.*;
import recoder.java.SourceElement.Position;
import recoder.java.declaration.ConstructorDeclaration;
import recoder.java.declaration.FieldDeclaration;
import recoder.java.declaration.MemberDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.ParameterDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.reference.MethodReference;
import recoder.java.reference.TypeReference;
import recoder.java.reference.VariableReference;
import recoder.java.statement.Branch;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.util.StringUtils;

public class ProofJavaProgramFactory extends JavaProgramFactory {

    /**
     * Protected constructor - use {@link #getInstance} instead.
     */
    protected ProofJavaProgramFactory() {}

    /**
     * The singleton instance of the program factory.
     */
    private static final ProofJavaProgramFactory theFactory = new ProofJavaProgramFactory();

    /**
     * Returns the single instance of this class.
     */
    public static JavaProgramFactory getInstance() {
        return theFactory;
    }

    @Override
    public void initialize(ServiceConfiguration cfg) {

        super.initialize(cfg);
        ProjectSettings settings = cfg.getProjectSettings();
        /*
         * // that is the original recoder code:
         * ProofJavaParser.setAwareOfAssert(StringUtils.parseBooleanProperty(settings.getProperties(
         * ).getProperty( PropertyNames.JDK1_4))); ProofJavaParser.setJava5(ALLOW_JAVA5);
         */
        ProofJavaParser.setJava5(StringUtils
                .parseBooleanProperty(settings.getProperties().getProperty(PropertyNames.JAVA_5)));
        ProofJavaParser.setAwareOfAssert(true);

    }


    /**
     * For internal reuse and synchronization.
     */
    private static final ProofJavaParser parser = new ProofJavaParser(System.in);

    private static final Position ZERO_POSITION = new Position(0, 0);

    // attaches a single comment to a ProgramElement
    private static void attachComment(Comment c, ProgramElement pe) {
        ProgramElement dest = pe;
        // never reached, proably buggy code...
        if (!c.isPrefixed()) {
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

    // appends all comments with pos < endPos to the end of the last a block
    private static int appendComments(ProgramElement last, List<Comment> comments, int commentIndex,
            Position endPos) {
        int commentCount = comments.size();

        while (commentIndex < commentCount) {
            Comment current = comments.get(commentIndex);
            Position cpos = current.getStartPosition();

            if (endPos != null && cpos.compareTo(endPos) > 0) {
                return commentIndex;
            }

            if (!current.getText().contains("@")) {
                // "pure" comment without @ (we only need JML annotations)
                // place it somewhere, doesn't matter
                current.setPrefixed(true);
                attachComment(current, last);
                commentIndex += 1;
                continue;
            }

            ProgramElement pe = last;
            while (pe.getEndPosition().compareTo(cpos) < 0) {
                if (pe.getASTParent() == null) {
                    return commentIndex;
                }
                pe = pe.getASTParent();
            }
            if (!(pe instanceof StatementBlock)) {
                // -- conservative with old behavior of postWork --
                // Rest assured, KeY does probably some magic later
                return commentIndex;
            }
            StatementBlock block = (StatementBlock) pe;
            while (commentIndex < commentCount && pe.getEndPosition().compareTo(cpos) > 0) {
                if (current.getText().contains("@")) {
                    // append new empty statement to statement block
                    Statement newEmpty = pe.getFactory().createEmptyStatement();
                    ASTList<Statement> body = block.getBody();
                    body.add(newEmpty);
                    block.setBody(body);

                    // attach comment to empty statement
                    ASTList<Comment> cml = new ASTArrayList<>();
                    newEmpty.setComments(cml);
                    current.setPrefixed(true);
                    cml.add(current);
                } else {
                    // again, skip "pure" comments
                    current.setPrefixed(true);
                    attachComment(current, last);
                }
                commentIndex += 1;
                if (commentIndex < commentCount) {
                    current = comments.get(commentIndex);
                    cpos = current.getStartPosition();
                }
            }
        }
        return commentIndex;
    }

    private static Position getPrevBlockEnd(ProgramElement pePrev, ProgramElement peNext) {
        Position startPos = peNext.getFirstElement().getStartPosition();
        ProgramElement pe = pePrev;
        Position endPos = ZERO_POSITION;
        while (pe != null) {
            if (pe.getEndPosition().compareTo(startPos) > 0) {
                return endPos;
            }
            endPos = pe.getEndPosition();
            pe = pe.getASTParent();
        }
        return endPos;
    }

    private static void makeParentRolesValid(ProgramElement programElem) {
        TreeWalker tw = new TreeWalker(programElem);
        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            if (pe instanceof NonTerminalProgramElement) {
                ((NonTerminalProgramElement) pe).makeParentRoleValid();
            }
        }
    }

    /**
     * Perform post work on the created element. Creates parent links and assigns comments.
     */
    private static void postWork(ProgramElement programElem) {
        makeParentRolesValid(programElem);

        List<Comment> comments = ProofJavaParser.getComments();
        int commentIndex = 0;
        int commentCount = comments.size();
        if (commentCount == 0) {
            return;
        }
        Comment current = comments.get(commentIndex);
        Position cpos = current.getFirstElement().getStartPosition();

        ProgramElement pePrev = programElem;
        ProgramElement peNext = programElem;
        TreeWalker tw = new TreeWalker(programElem);
        while (tw.next()) {
            peNext = tw.getProgramElement();

            if (peNext.getFirstElement() == null) {
                // Apparently, these are nodes with no source and no position... skip them
                continue;
            }

            Position startPos = peNext.getFirstElement().getStartPosition();
            if (startPos.compareTo(cpos) < 0) {
                pePrev = peNext;
                continue;
            }
            Position endPos = getPrevBlockEnd(pePrev, peNext);

            commentIndex = appendComments(pePrev, comments, commentIndex, endPos);
            if (commentIndex == commentCount) {
                return;
            }
            current = comments.get(commentIndex);
            cpos = current.getFirstElement().getStartPosition();
            while ((commentIndex < commentCount) && startPos.compareTo(cpos) > 0) {
                // Attach comments to the next node
                current.setPrefixed(true);
                attachComment(current, peNext);
                commentIndex += 1;
                if (commentIndex == commentCount) {
                    return;
                }
                current = comments.get(commentIndex);
                cpos = current.getFirstElement().getStartPosition();
            }
            pePrev = peNext;
        }
        // Append remaining comments to the previous block
        commentIndex = appendComments(pePrev, comments, commentIndex, null);

        if (commentIndex < commentCount) {
            // -- conservative with old behovior of this method ---
            // Attach all still remaining comments to the compilation unit
            ProgramElement pe = peNext;
            while (pe.getASTParent() != null) {
                pe = pe.getASTParent();
            }
            ASTList<Comment> cml = pe.getComments();
            if (cml == null) {
                pe.setComments(cml = new ASTArrayList<>());
            }
            do {
                current = comments.get(commentIndex);
                current.setPrefixed(false);
                cml.add(current);
                commentIndex += 1;
            } while (commentIndex < commentCount);
        }
    }

    /**
     * Parse a {@link CompilationUnit} from the given reader.
     */
    @Override
    public CompilationUnit parseCompilationUnit(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                CompilationUnit res = ProofJavaParser.CompilationUnit();
                postWork(res);
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }
        }
    }

    /**
     * Parse a {@link TypeDeclaration} from the given reader.
     */
    @Override
    public TypeDeclaration parseTypeDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                TypeDeclaration res = ProofJavaParser.TypeDeclaration();
                postWork(res);
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }

        }
    }

    /**
     * Parse a {@link FieldDeclaration} from the given reader.
     */
    @Override
    public FieldDeclaration parseFieldDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                FieldDeclaration res = ProofJavaParser.FieldDeclaration();
                postWork(res);
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }

        }
    }

    /**
     * Parse a {@link MethodDeclaration} from the given reader.
     */
    @Override
    public MethodDeclaration parseMethodDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                MethodDeclaration res = ProofJavaParser.MethodDeclaration();
                postWork(res);
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }

        }
    }

    /**
     * Parse a {@link MemberDeclaration} from the given reader.
     */
    @Override
    public MemberDeclaration parseMemberDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                MemberDeclaration res = ProofJavaParser.ClassBodyDeclaration();
                postWork(res);
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }

        }
    }

    /**
     * Parse a {@link ParameterDeclaration} from the given reader.
     */
    @Override
    public ParameterDeclaration parseParameterDeclaration(Reader in)
            throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                ParameterDeclaration res = ProofJavaParser.FormalParameter();
                postWork(res);
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }

        }
    }

    /**
     * Parse a {@link ConstructorDeclaration} from the given reader.
     */
    @Override
    public ConstructorDeclaration parseConstructorDeclaration(Reader in)
            throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                ConstructorDeclaration res = ProofJavaParser.ConstructorDeclaration();
                postWork(res);
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }

        }
    }

    /**
     * Parse a {@link TypeReference} from the given reader.
     */
    @Override
    public TypeReference parseTypeReference(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                TypeReference res = ProofJavaParser.ResultType();
                postWork(res);
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }

        }
    }

    /**
     * Parse an {@link Expression} from the given reader.
     */
    @Override
    public Expression parseExpression(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                Expression res = ProofJavaParser.Expression();
                postWork(res);
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }

        }
    }

    /**
     * Parse some {@link Statement}s from the given reader.
     */
    @Override
    public ASTList<Statement> parseStatements(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                ASTList<Statement> res = ProofJavaParser.GeneralizedStatements();
                for (Statement re : res) {
                    postWork(re);
                }
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }

        }
    }

    /**
     * Parse a {@link StatementBlock} from the given string.
     */
    @Override
    public StatementBlock parseStatementBlock(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            try {
                ProofJavaParser.initialize(in);
                StatementBlock res = ProofJavaParser.StartBlock();
                postWork(res);
                return res;
            } catch (ParseException e) {
                throw (ParserException) (new ParserException(e.getMessage())).initCause(e);
            }

        }
    }

    /**
     * Create a {@link PassiveExpression}.
     */
    public PassiveExpression createPassiveExpression(Expression e) {
        return new PassiveExpression(e);
    }

    /**
     * Create a {@link PassiveExpression}.
     */
    public PassiveExpression createPassiveExpression() {
        return new PassiveExpression();
    }

    /**
     * Create a {@link MethodSignature}.
     */
    public MethodSignature createMethodSignature(Identifier methodName,
            ASTList<TypeReference> paramTypes) {
        return new MethodSignature(methodName, paramTypes);
    }

    /**
     * Create a {@link MethodCallStatement}.
     */
    public MethodCallStatement createMethodCallStatement(Expression resVar, ExecutionContext ec,
            StatementBlock block) {
        return new MethodCallStatement(resVar, ec, block);
    }

    public LoopScopeBlock createLoopScopeBlock() {
        return new LoopScopeBlock();
    }

    public MergePointStatement createMergePointStatement() {
        return new MergePointStatement();
    }

    public MergePointStatement createMergePointStatement(Expression expr) {
        return new MergePointStatement(expr);
    }

    /**
     * Create a {@link MethodBodyStatement}.
     */
    public MethodBodyStatement createMethodBodyStatement(TypeReference bodySource,
            Expression resVar, MethodReference methRef) {
        return new MethodBodyStatement(bodySource, resVar, methRef);
    }

    /**
     * Create a {@link CatchAllStatement}.
     */
    public Statement createCatchAllStatement(VariableReference param, StatementBlock body) {
        return new CatchAllStatement(param, body);
    }

    /**
     * Create a comment.
     *
     * @param text comment text
     */
    @Override
    public Comment createComment(String text) {
        return new Comment(text);
    }

    /**
     * Create a comment.
     *
     * @param text comment text
     */
    @Override
    public Comment createComment(String text, boolean prefixed) {
        return new Comment(text, prefixed);
    }

    /**
     * Create an {@link ImplicitIdentifier}.
     */
    public ImplicitIdentifier createImplicitIdentifier(String text) {
        return new ImplicitIdentifier(text);
    }


    @Override
    public Identifier createIdentifier(String text) {
        return new ExtendedIdentifier(text);
    }

    public ObjectTypeIdentifier createObjectTypeIdentifier(String text) {
        return new ObjectTypeIdentifier(text);
    }

    public Exec createExec() {
        Exec res = new Exec();
        return res;
    }

    public Exec createExec(StatementBlock body) {
        Exec res = new Exec(body);
        return res;
    }

    public Exec createExec(StatementBlock body, ASTList<Branch> branches) {
        Exec res = new Exec(body, branches);
        return res;
    }

    public Ccatch createCcatch() {
        Ccatch res = new Ccatch();
        return res;
    }

    public Ccatch createCcatch(ParameterDeclaration e, StatementBlock body) {
        Ccatch res = new Ccatch(e, body);
        return res;
    }

    public CcatchReturnParameterDeclaration createCcatchReturnParameterDeclaration() {
        return new CcatchReturnParameterDeclaration();
    }

    public CcatchBreakParameterDeclaration createCcatchBreakParameterDeclaration() {
        return new CcatchBreakParameterDeclaration();
    }

    public CcatchBreakLabelParameterDeclaration createCcatchBreakLabelParameterDeclaration(
            Identifier label) {
        return new CcatchBreakLabelParameterDeclaration(label);
    }

    public CcatchBreakWildcardParameterDeclaration createCcatchBreakWildcardParameterDeclaration() {
        return new CcatchBreakWildcardParameterDeclaration();
    }

    public CcatchContinueParameterDeclaration createCcatchContinueParameterDeclaration() {
        return new CcatchContinueParameterDeclaration();
    }

    public CcatchContinueLabelParameterDeclaration createCcatchContinueLabelParameterDeclaration(
            Identifier label) {
        return new CcatchContinueLabelParameterDeclaration(label);
    }

    public CcatchContinueWildcardParameterDeclaration createCcatchContinueWildcardParameterDeclaration() {
        return new CcatchContinueWildcardParameterDeclaration();
    }

    public CcatchNonstandardParameterDeclaration createCcatchReturnValParameterDeclaration(
            ParameterDeclaration e) {
        return new CcatchReturnValParameterDeclaration(e);
    }
}
