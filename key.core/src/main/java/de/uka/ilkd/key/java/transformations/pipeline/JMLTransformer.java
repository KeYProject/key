// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.transformations.pipeline;

import java.net.URI;
import java.util.Arrays;
import java.util.EnumSet;
import java.util.LinkedList;
import java.util.List;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLAssertStatement.Kind;
import de.uka.ilkd.key.speclang.njml.JmlIO;
import de.uka.ilkd.key.speclang.njml.PreParser;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.StringUtil;

import com.github.javaparser.Position;
import com.github.javaparser.Range;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.key.KeyMergePointStatement;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.EmptyStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.visitor.VoidVisitorWithDefaults;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.Interval;

import static java.lang.String.format;

/**
 * RecodeR transformation that parses JML comments, and attaches code-like
 * specifications (ghost fields, set statements, model methods) directly to the
 * RecodeR AST. Note that internally, this class is highly similar to the class
 * speclang.jml.SpecExtractor; if you change one of these classes, you probably
 * need to change the other as well.
 */
public final class JMLTransformer extends JavaTransformer {
    public static final EnumSet<JMLModifier> JAVA_MODS =
        EnumSet.of(JMLModifier.ABSTRACT, JMLModifier.FINAL, JMLModifier.PRIVATE,
            JMLModifier.PROTECTED,
            JMLModifier.PUBLIC, JMLModifier.STATIC);


    /**
     * JML markers left and right.
     */
    private static final String JML = "/*@";
    private static final String JMR = "@*/";
    private static ImmutableList<PositionedString> warnings = ImmutableSLList.nil();

    /**
     * Creates a transformation that adds JML specific elements, for example
     * ghost fields and model method declarations.
     *
     * @param services the CrossReferenceServiceConfiguration to access model
     *        information
     */
    public JMLTransformer(TransformationPipelineServices services) {
        super(services);
        warnings = ImmutableSLList.nil();
    }

    // -------------------------------------------------------------------------
    // private helper methods
    // -------------------------------------------------------------------------

    public static String getFullText(ParserRuleContext context) {
        if (context.start == null || context.stop == null
                || context.start.getStartIndex() < 0 || context.stop.getStopIndex() < 0)
            return context.getText(); // Fallback
        return context.start.getInputStream()
                .getText(Interval.of(context.start.getStartIndex(), context.stop.getStopIndex()));
    }

    public static ImmutableList<PositionedString> getWarningsOfLastInstance() {
        return warnings;
    }

    /**
     * Concatenates the passed comments in a position-preserving way. (see also
     * JMLSpecExtractor::concatenate(), which does the same thing for KeY ASTs)
     */
    private String concatenate(Comment[] comments) {
        if (comments.length == 0) {
            return "";
        }
        StringBuilder sb = new StringBuilder();

        for (Comment comment : comments) {
            Position relativePos = comment.getRange().get().begin;
            sb.append("\n".repeat(Math.max(0, relativePos.line)));
            sb.append(" ".repeat(Math.max(0, relativePos.column)));
            if (comment instanceof BlockComment) {
                sb.append("/*").append(comment.getContent()).append("*/");
            } else {
                sb.append("//").append(comment.getContent());
            }
        }
        return sb.toString();
    }

    /**
     * Prepends the Java (i.e., non-JML) modifiers from the passed list to the
     * passed PositionedString. Inserts whitespace in place of the JML modifiers
     * (in order to preserve position information).
     */
    private PositionedString convertToString(ImmutableList<JMLModifier> mods,
            ParserRuleContext ctx) {
        StringBuilder sb = new StringBuilder();
        for (var mod : mods) {
            if (JAVA_MODS.contains(mod)) {
                sb.append(mod);
            } else {
                sb.append(StringUtil.repeat(" ", mod.name().length()));
            }
            sb.append(" ");
        }
        sb.append(getFullText(ctx));
        int column = ctx.start.getCharPositionInLine() - sb.toString().length();
        if (column < 0) {
            column = 0;
        }
        var pos = de.uka.ilkd.key.java.Position.newOneBased(ctx.start.getLine(), column);
        var location = new Location(
            MiscTools.getURIFromTokenSource(ctx.start.getTokenSource().getSourceName()), pos);
        return new PositionedString(sb.toString(), location);
    }

    /**
     * Puts the JML modifiers from the passed list into a string enclosed in JML
     * markers.
     */
    private String getJMLModString(ImmutableList<JMLModifier> mods) {
        StringBuilder sb = new StringBuilder(JML);
        for (var mod : mods) {
            if (!JAVA_MODS.contains(mod)) {
                sb.append(mod.name()).append(" ");
            }
        }
        sb.append(JMR);
        return sb.toString();
    }

    /**
     * Recursively adds the passed position to the starting positions of the
     * passed program element and its children.
     */
    private void updatePositionInformation(Node pe, de.uka.ilkd.key.java.Position pos) {
        if (pe.getRange().isPresent()) {
            final var range = pe.getRange().get();
            Position oldStartPosition = range.begin;
            int line = Math.max(0, pos.line() + oldStartPosition.line - 1);
            int column = Math.max(0, pos.column() + oldStartPosition.column - 1);
            Position newPos = oldStartPosition.withColumn(column).withLine(line);
            pe.setRange(range.withBegin(newPos));

            // recurse to children
            for (Node childNode : pe.getChildNodes()) {
                updatePositionInformation(childNode, pos);
            }
        }
    }

    /**
     * Returns the children of the passed program element.
     */
    private Node[] getChildren(Node pe) {
        return pe.getChildNodes().toArray(new Node[0]);
    }

    private Comment[] getCommentsAndSetParent(@Nonnull Node pe) {
        if (pe.getComment().isEmpty()) {
            return new Comment[0];
        }
        Comment var = pe.getComment().get();
        return new Comment[] { var };
    }

    private void transformFieldDecl(TextualJMLFieldDecl decl, Comment[] originalComments)
            throws SLTranslationException {
        assert originalComments.length > 0;

        // prepend Java modifiers
        PositionedString declWithMods = convertToString(decl.getMods(), decl.getDecl());

        // ghost or model?
        boolean isGhost = false;
        boolean isModel = false;
        if (decl.getMods().contains(JMLModifier.GHOST)) {
            isGhost = true;
        }
        if (decl.getMods().contains(JMLModifier.MODEL)) {
            isModel = true;
            if (isGhost) {
                throw new SLTranslationException(
                    "JML field declaration cannot be both ghost and model!", declWithMods.location);
            }
        }
        if (!(isGhost || isModel)) {
            String s = declWithMods.text;
            s = s.substring(0, s.indexOf(' '));
            throw new SLTranslationException(
                format("Could not translate JML specification. You have either tried to use an" +
                    " unsupported keyword (%s) or a JML field declaration without a ghost or model modifier.",
                    s),
                declWithMods.location);
        }

        // determine parent, child index
        Node astParent = originalComments[0].getParentNode().flatMap(Node::getParentNode).get();
        int childIndex =
            astParent.getChildNodes().indexOf(originalComments[0].getParentNode().get());

        // parse declaration, attach to AST
        FieldDeclaration fieldDecl;
        try {
            if (astParent instanceof TypeDeclaration) {
                var result = services.getParser()
                        .parseBodyDeclaration(
                            fillWithWhitespaces(declWithMods.location.getPosition(),
                                declWithMods.text));
                // TODO weigl add parseFieldDeclaration(declWithMods.text); ?

                if (result.isSuccessful()) {
                    fieldDecl = (FieldDeclaration) result.getResult().get();
                    if (decl.getMods().contains(JMLModifier.INSTANCE)) {
                        fieldDecl.getModifiers()
                                .removeIf(it -> it.getKeyword() == Modifier.Keyword.STATIC);
                    }
                    // updatePositionInformation(fieldDecl, declWithMods.pos);
                    // set comments: the original list of comments with the declaration, and the JML
                    // modifiers
                    NodeList<Comment> newComments = new NodeList<>(Arrays.asList(originalComments));
                    Comment jmlComment = new BlockComment(getJMLModString(decl.getMods()));
                    jmlComment.setParentNode(fieldDecl);
                    newComments.add(jmlComment);
                    fieldDecl.setAssociatedSpecificationComments(newComments);
                    ((TypeDeclaration<?>) astParent).addMember(fieldDecl);
                    /*
                     * javadoc for attach() may say, this value is *not* used as a child index but
                     * as an index
                     * into astParent.getMembers(), which only contains some of the children, not
                     * all. 0 is topmost
                     * position, which should be a safe choice in any case.
                     */

                    // add ghost or model modifier
                    NodeList<Modifier> mods = fieldDecl.getModifiers();
                    if (mods == null) {
                        mods = new NodeList<>();
                    }
                    mods.add(
                        new Modifier(isGhost ? Modifier.Keyword.GHOST : Modifier.Keyword.MODEL));
                    fieldDecl.setModifiers(mods);

                } else {
                    throw new SLTranslationException("Could not parse " + declWithMods.text,
                        declWithMods.location);
                }
            } else {
                assert astParent instanceof BlockStmt;
                if (isModel) {
                    throw new SLTranslationException(
                        "JML model fields cannot be declared within a method!",
                        declWithMods.location);
                }

                var block = services.getParser().parseBlock(
                    fillWithWhitespaces(declWithMods.location.getPosition(),
                        "{" + declWithMods.text + "}"));
                if (!block.isSuccessful()) {
                    throw new SLTranslationException("", declWithMods.location);
                }
                List<Statement> declStatement = block.getResult().get().getStatements();
                assert declStatement.size() == 1;
                var vdecl = declStatement.get(0);
                // updatePositionInformation(fieldDecl, declWithMods.pos);
                ((BlockStmt) astParent).addStatement(childIndex, vdecl);
                // attach((LocalVariableDeclaration) fieldDecl, (BlockStmt) astParent, childIndex);
                // Unlike above, here the value is really a child index, and here the
                // position really matters.
            }
        } catch (Throwable e) {
            throw new SLTranslationException(
                e.getMessage() + " (" + e.getClass().getName() + ")",
                declWithMods.location, e);
        }
    }

    private String fillWithWhitespaces(de.uka.ilkd.key.java.Position pos, String s) {
        return "\n".repeat(Math.max(0, pos.line())) +
                " ".repeat(Math.max(0, pos.column())) + s;
    }

    private void transformMethodDecl(TextualJMLMethodDecl decl, Comment[] originalComments)
            throws SLTranslationException {
        assert originalComments.length > 0;

        // prepend Java modifiers
        PositionedString declWithMods =
            new PositionedString(decl.getParsableDeclaration());

        // only handle model methods
        if (!decl.getMods().contains(JMLModifier.MODEL)) {
            throw new SLTranslationException("JML method declaration has to be model!",
                declWithMods.location);
        }

        // determine parent
        TypeDeclaration<?> astParent =
            (TypeDeclaration<?>) originalComments[0].getParentNode().get();

        // parse declaration, attach to AST
        MethodDeclaration methodDecl;
        var md = services.getParser()
                .parseMethodDeclaration(declWithMods.text);
        if (md.getResult().isPresent()) {
            methodDecl = md.getResult().get();
            updatePositionInformation(methodDecl, declWithMods.location.getPosition());
            astParent.addMember(methodDecl);
            // about the 0 see the comment in transformFieldDecl() above
        } else {
            throw new SLTranslationException(
                "could not parse", declWithMods.location);
        }

        // add model modifier
        methodDecl.setModifiers(Modifier.Keyword.MODEL);
        if (decl.getMods().contains(JMLModifier.TWO_STATE)) {
            methodDecl.addModifier(Modifier.Keyword.TWO_STATE);
        }
        if (decl.getMods().contains(JMLModifier.NO_STATE)) {
            methodDecl.addModifier(Modifier.Keyword.NO_STATE);
        }

        // set comments: the original list of comments with the declaration,
        // and the JML modifiers
        NodeList<Comment> newComments = new NodeList<>(originalComments);
        Comment jmlComment = new LineComment(getJMLModString(decl.getMods()));
        jmlComment.setParentNode(methodDecl);
        newComments.add(jmlComment);
        methodDecl.setAssociatedSpecificationComments(newComments);
    }

    private void transformAssertStatement(TextualJMLAssertStatement stat,
            Comment[] originalComments) throws SLTranslationException {
        if (originalComments.length <= 0)
            throw new IllegalArgumentException();

        // determine parent, child index
        BlockStmt astParent = (BlockStmt) originalComments[0]
                .getParentNode().get().getParentNode().get();
        int childIndex =
            astParent.getChildNodes().indexOf(originalComments[0].getParentNode().get());

        ParserRuleContext ctx = stat.getContext().first;

        // Convert to block with block contract, attach to AST.
        var location = Location.fromToken(ctx.start);

        try {
            String comment = format(
                """
                        /*@ normal_behavior
                          @ %s %s
                          @ assignable \\strictly_nothing;
                          @*/
                        """,
                stat.getKind() == Kind.ASSERT ? "ensures" : "ensures_free", stat.getClauseText());

            BlockStmt block = new BlockStmt();
            block.setAssociatedSpecificationComments(new NodeList<>(new BlockComment(comment)));
            updatePositionInformation(block, location.getPosition());
            astParent.addStatement(childIndex, block);
        } catch (Throwable e) {
            throw new SLTranslationException(
                format("%s (%s)", e.getMessage(), e.getClass().getName()), location, e);
        }
    }

    private void transformSetStatement(TextualJMLSetStatement stat,
            Comment[] originalComments) throws SLTranslationException {
        assert originalComments.length > 0;

        // determine parent, child index
        BlockStmt astParent =
            (BlockStmt) originalComments[0].getParentNode().get().getParentNode().get();
        int childIndex =
            astParent.getChildNodes().indexOf(originalComments[0].getParentNode().get());

        // parse statement, attach to AST
        var location = Location.fromToken(stat.getAssignment().start);
        try {
            String assignment = getFullText(stat.getAssignment()).substring(3);
            var result = services.getParser().parseBlock("{" + assignment + "}");
            var stmtList = result.getResult().get().getStatements();
            assert stmtList.size() == 1;
            var assignStmt = stmtList.get(0);
            shiftPosition(assignStmt, location.getPosition());
            // updatePositionInformation(assignStmt, pos);
            astParent.addStatement(childIndex, assignStmt);
        } catch (Throwable e) {
            throw new SLTranslationException(e.getMessage() + " (" + e.getClass().getName() + ")",
                location, e);
        }
    }

    private void shiftPosition(Node node, de.uka.ilkd.key.java.Position pos) {
        shiftPosition(node, pos.line(), pos.column());
    }

    private void shiftPosition(Node node, int line, int column) {
        final var tokenRange = node.getTokenRange();
        if (tokenRange.isPresent()) {
            var iter = tokenRange.get().iterator();
            iter.forEachRemaining(it -> {
                if (it.getRange().isPresent()) {
                    var range = it.getRange().get();
                    it.setRange(
                        Range.range(range.begin.line + line,
                            range.begin.column + column,
                            range.end.line + line,
                            range.end.column + column));
                }
            });
        }
    }

    private void transformMergePointDecl(TextualJMLMergePointDecl stat,
            Comment[] originalComments) throws SLTranslationException {
        assert originalComments.length > 0;

        // determine parent, child index
        BlockStmt astParent =
            (BlockStmt) originalComments[0].getParentNode().get().getParentNode().get();
        int childIndex =
            astParent.getChildNodes().indexOf(originalComments[0].getParentNode().get());

        // create MPS, attach to AST
        try {
            KeyMergePointStatement mps = new KeyMergePointStatement(new BooleanLiteralExpr(true));
            mps.setAssociatedSpecificationComments(new NodeList<>(Arrays.asList(originalComments)));

            Position startPosition =
                astParent.getChildNodes().get(childIndex).getRange().get().begin;
            shiftPosition(mps, startPosition.line, startPosition.column);
            astParent.addStatement(childIndex, mps);
        } catch (Throwable e) {
            throw new SLTranslationException(
                format("%s (%s)", e.getMessage(), e.getClass().getName()),
                stat.getLocation(), e);
        }
    }

    private void transformClassLevelComments(TypeDeclaration<?> td, URI fileName)
            throws SLTranslationException {
        // iterate over all pre-existing children
        Node[] children = getChildren(td);
        for (int i = 0; i <= children.length; i++) {
            // collect comments
            // (last position are comments of type declaration itself)
            Comment[] comments = null;
            if (i < children.length) {
                comments = getCommentsAndSetParent(children[i]);
            } else if (td.getAssociatedSpecificationComments().isPresent()) {
                assert i > 0; // otherwise there wouldn't even be implicit
                // fields
                NodeList<Comment> var = td.getAssociatedSpecificationComments().get();
                comments = var.toArray(new Comment[0]);
                for (Comment c : comments) {
                    c.setParentNode(children[i - 1]);
                }
            }
            if (comments == null || comments.length == 0) {
                continue;
            }

            // concatenate comments of child, determine position
            String concatenatedComment = concatenate(comments);
            Position recoderPos = comments[0].getRange().get().begin;
            de.uka.ilkd.key.java.Position pos = de.uka.ilkd.key.java.Position.newOneBased(
                recoderPos.line, recoderPos.column);

            // call preparser
            JmlIO io = new JmlIO();
            PreParser pp = new PreParser();
            ImmutableList<TextualJMLConstruct> constructs =
                pp.parseClassLevel(concatenatedComment, fileName, pos);
            warnings = warnings.append(io.getWarnings());

            // handle model and ghost declarations in textual constructs
            // (and set assignments which RecodeR evilly left hanging *behind*
            // the method to which they belong)
            for (TextualJMLConstruct c : constructs) {
                if (c instanceof TextualJMLFieldDecl) {
                    transformFieldDecl((TextualJMLFieldDecl) c, comments);
                } else if (c instanceof TextualJMLMethodDecl) {
                    transformMethodDecl((TextualJMLMethodDecl) c, comments);
                } else if (c instanceof TextualJMLSetStatement) {
                    if (i == 0 || !(children[i - 1] instanceof MethodDeclaration)) {
                        throw new SLTranslationException(
                            "A set assignment only allowed inside of a method body.",
                            new Location(fileName, pos));
                    }
                    Statement emptyStmt = new EmptyStmt();
                    Comment emptyStmtComment = new BlockComment();
                    emptyStmtComment.setParentNode(emptyStmt);
                    BlockStmt methodBody = ((MethodDeclaration) children[i - 1]).getBody().get();
                    methodBody.addStatement(emptyStmt);
                    transformSetStatement((TextualJMLSetStatement) c,
                        new Comment[] { emptyStmtComment });
                }
            }
        }
    }

    private void transformMethodLevelCommentsHelper(Node pe, URI fileName)
            throws SLTranslationException {
        // recurse to all pre-existing children
        Node[] children = getChildren(pe);
        for (Node aChildren : children) {
            transformMethodLevelCommentsHelper(aChildren, fileName);
        }

        if (pe instanceof MethodDeclaration)
            return;

        // get comments
        Comment[] comments = getCommentsAndSetParent(pe);
        if (comments.length == 0) {
            return;
        }

        // concatenate comments, determine position
        String concatenatedComment = concatenate(comments);
        Position recoderPos = comments[0].getRange().get().begin;
        de.uka.ilkd.key.java.Position pos = de.uka.ilkd.key.java.Position.newOneBased(
            recoderPos.line, recoderPos.column);

        // call preparser
        var io = new PreParser();
        ImmutableList<TextualJMLConstruct> constructs =
            io.parseMethodLevel(concatenatedComment, fileName, pos);
        warnings = warnings.append(io.getWarnings());

        // handle ghost declarations and set assignments in textual constructs
        for (TextualJMLConstruct c : constructs) {
            if (c instanceof TextualJMLFieldDecl) {
                transformFieldDecl((TextualJMLFieldDecl) c, comments);
            } else if (c instanceof TextualJMLSetStatement) {
                transformSetStatement((TextualJMLSetStatement) c, comments);
            } else if (c instanceof TextualJMLMergePointDecl) {
                transformMergePointDecl((TextualJMLMergePointDecl) c, comments);
            } else if (c instanceof TextualJMLAssertStatement) {
                transformAssertStatement((TextualJMLAssertStatement) c, comments);
            }
        }
    }


    public void analyze() {
        for (var unit : cache.getUnits()) {
            // move comments of type declarations to previous type declaration
            // (because RecodeR attaches comments appearing at the end of a type
            // declaration to the next one; for example, in a unit with the
            // text
            // class A {
            // //@ invariant true;
            // }
            // class B {}
            // the invariant will appear as a comment of B. We move it to A
            // here.)
            for (int j = 1; j < unit.getTypes().size(); j++) {
                TypeDeclaration<?> td1 = unit.getType(j - 1);
                TypeDeclaration<?> td2 = unit.getType(j);
                td1.setAssociatedSpecificationComments(
                    td2.getAssociatedSpecificationComments().get());
            }

            // copy comments of compilation unit to last type declaration
            // (because RecodeR attaches comments appearing at the end of the
            // last type declaration to the unit; for example, in a unit with
            // the text
            // class A {}
            // class B {
            // //@ invariant true;
            // }
            // the invariant will appear as a comment of the unit. We move it to B here.)
            if (unit.getTypes().size() > 0) {
                TypeDeclaration<?> td = unit.getType(unit.getTypes().size() - 1);
                NodeList<Comment> tdComments = new NodeList<>();
                if (unit.getComments() != null) {
                    tdComments.addAll(TransformationPipelineServices.cloneList(
                        unit.getAssociatedSpecificationComments().get()));
                }
                td.setAssociatedSpecificationComments(tdComments);
            }

            // iterate over all type declarations of the compilation unit
            var typeDeclarations = getAllTypes(unit);
            for (TypeDeclaration<?> td : typeDeclarations) {
                // collect pre-existing operations
                List<? extends ConstructorDeclaration> constructorList = td.getConstructors();
                List<MethodDeclaration> methodList = td.getMethods();
            }
        }
    }

    private List<TypeDeclaration<?>> getAllTypes(CompilationUnit unit) {
        var seq = new LinkedList<TypeDeclaration<?>>();
        class TypesCollector extends VoidVisitorWithDefaults<Void> {
            @Override
            public void defaultAction(Node n, Void arg) {
                if (n instanceof TypeDeclaration) {
                    seq.add((TypeDeclaration<?>) n);
                }
            }
        }
        unit.accept(new TypesCollector(), null);
        return seq;
    }


    public void apply(TypeDeclaration<?> td) {
        // abort if JML is disabled
        if (!ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().isUseJML()) {
            return;
        }

        try {
            // collect pre-existing operations
            List<? extends ConstructorDeclaration> constructorList = td.getConstructors();
            List<MethodDeclaration> methodList = td.getMethods();

            // fix mu: units carry an artificial file name. use getOriginalDataLocation
            // instead
            // DataLocation dl = unit.getOriginalDataLocation();
            /*
             * If the DataLocation is not set, we set an invalid URL string.
             * This may cause a MalformedURLException later if a parsing error occurs,
             * but at least show the error message of the parser.
             */
            URI resource = td.findCompilationUnit()
                    .flatMap(CompilationUnit::getStorage)
                    .map(it -> it.getPath().toUri())
                    .orElse(null);

            transformClassLevelComments(td, resource);

            // iterate over all pre-existing constructors
            for (var aConstructorList : constructorList) {
                transformMethodLevelCommentsHelper(aConstructorList.getBody(), resource);
            }

            // iterate over all pre-existing methods
            for (var aMethodList : methodList) {
                // might be ImplicitEnumMethod
                if (aMethodList.getBody().isPresent()) {
                    transformMethodLevelCommentsHelper(aMethodList.getBody().get(),
                        resource);
                }
            }
        } catch (SLTranslationException e) {
            // Wrap the exception into a runtime exception because recoder does
            // not allow otherwise. It will be unwrapped later ...
            throw new RuntimeException(e);
        }
    }
}
