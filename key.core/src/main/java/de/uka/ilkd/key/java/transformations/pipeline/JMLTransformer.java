/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
import java.util.*;

import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.speclang.njml.PreParser;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.StringUtil;

import com.github.javaparser.Position;
import com.github.javaparser.Range;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.EmptyStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.visitor.VoidVisitorWithDefaults;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.Interval;
import org.jspecify.annotations.NonNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


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

    public static final DataKey<TextualJMLConstruct> KEY_CONSTRUCT = new DataKey<>() {
    };

    private static ImmutableList<PositionedString> warnings = ImmutableSLList.nil();
    private static final Logger LOGGER = LoggerFactory.getLogger(JMLTransformer.class);

    /**
     * Creates a transformation that adds JML specific elements, for example
     * ghost fields and model method declarations.
     *
     * @param services
     *        the CrossReferenceServiceConfiguration to access model
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
    private String concatenate(Iterable<Comment> comments) {
        StringBuilder sb = new StringBuilder();
        var iter = comments.iterator();
        if (!iter.hasNext()) {
            return sb.toString();
        }
        var first = iter.next();
        if (first instanceof BlockComment) {
            sb.append("/*").append(first.getContent()).append("*/");
        } else {
            sb.append("//").append(first.getContent());
        }
        var last = first.getRange().get().end;
        while (iter.hasNext()) {
            var comment = iter.next();
            int line;
            int column;
            var pos = comment.getRange().get().begin;
            if (last.line == pos.line) {
                line = 0;
                column = pos.column - last.column;
            } else {
                line = pos.line - last.line;
                column = pos.column;
            }
            StringUtil.appendRepeated(sb, '\n', Math.max(0, line));
            StringUtil.appendRepeated(sb, ' ', Math.max(0, column));
            if (comment instanceof BlockComment) {
                sb.append("/*").append(comment.getContent()).append("*/");
            } else {
                sb.append("//").append(comment.getContent());
            }
        }
        iter.forEachRemaining(comment -> {

        });
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
        // TODO this is garbage, see Throwable::cause, protected is not contained in ctx
        int column = ctx.start.getCharPositionInLine() - sb.toString().length();
        if (column <= 0) {
            column = 1;
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
    private BlockComment getJMLModComment(ImmutableList<JMLModifier> mods) {
        StringBuilder sb = new StringBuilder("@");
        for (var mod : mods) {
            if (!JAVA_MODS.contains(mod)) {
                sb.append(mod.toString()).append(" ");
            }
        }
        sb.append("@");
        return new BlockComment(sb.toString());
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
    private List<Node> getChildren(Node pe) {
        return pe.getChildNodes();
    }

    private static void insertAtSourceNodeOffsetInParent(Statement node, List<Comment> comments) {
        assert !comments.isEmpty();

        // determine parent, child index
        BlockStmt astParent =
            (BlockStmt) comments.get(0).getParentNode().orElseThrow().getParentNode().orElseThrow();
        int childIndex =
            astParent.getChildNodes().indexOf(comments.get(0).getParentNode().get());
        astParent.addStatement(childIndex, node);
    }

    private static Modifier.@NonNull Keyword getModifier(TextualJMLFieldDecl decl)
            throws SLTranslationException {
        // ghost or model?
        boolean isGhost = decl.getModifiers().contains(JMLModifier.GHOST);
        boolean isModel = decl.getModifiers().contains(JMLModifier.MODEL);
        if (isGhost == isModel) {
            throw new SLTranslationException(
                "JML field declaration must be either ghost or model!", decl.getLocation());
        }
        return isGhost ? Modifier.Keyword.GHOST : Modifier.Keyword.MODEL;
    }

    @NonNull
    private FieldDeclaration transformClassFieldDecl(TextualJMLFieldDecl decl,
            List<Comment> originalComments)
            throws SLTranslationException {
        assert !originalComments.isEmpty();

        // prepend Java modifiers
        PositionedString declWithMods = convertToString(decl.getModifiers(), decl.getDecl());

        // parse declaration, attach to AST
        var result = services.getParser()
                .parseBodyDeclaration(
                    fillWithWhitespaces(declWithMods.location.getPosition(),
                        declWithMods.text));
        // TODO weigl add parseFieldDeclaration(declWithMods.text); ?

        if (!result.isSuccessful()) {
            throw new SLTranslationException("Could not parse " + declWithMods.text,
                declWithMods.location);
        }

        var fieldDecl = (FieldDeclaration) result.getResult().get();
        if (decl.getModifiers().contains(JMLModifier.INSTANCE)
                && decl.getModifiers().contains(JMLModifier.STATIC)) {
            throw new SLTranslationException(
                "JML field can't be static and instance at once " + declWithMods.text);
        }
        // updatePositionInformation(fieldDecl, declWithMods.pos);
        // set comments: the original list of comments with the declaration, and the JML
        // modifiers
        NodeList<Comment> newComments = new NodeList<>(originalComments);
        Comment jmlComment = getJMLModComment(decl.getModifiers());
        jmlComment.setParentNode(fieldDecl);
        newComments.add(jmlComment);
        fieldDecl.setAssociatedSpecificationComments(newComments);
        /*
         * javadoc for attach() may say, this value is *not* used as a child index but
         * as an index
         * into astParent.getMembers(), which only contains some of the children, not
         * all. 0 is topmost
         * position, which should be a safe choice in any case.
         */

        var mod = getModifier(decl);

        // add ghost or model modifier
        fieldDecl.addModifier(mod);

        return fieldDecl;
    }

    @NonNull
    private Statement transformVariableDecl(TextualJMLFieldDecl decl)
            throws SLTranslationException {
        // prepend Java modifiers
        PositionedString declWithMods = convertToString(decl.getModifiers(), decl.getDecl());
        var mod = getModifier(decl);

        // parse declaration, attach to AST

        if (mod == Modifier.Keyword.MODEL) {
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
        // updatePositionInformation(fieldDecl, declWithMods.pos);
        // Unlike above, here the value is really a child index, and here the
        // position really matters.
        return declStatement.get(0);
    }

    private String fillWithWhitespaces(de.uka.ilkd.key.java.Position pos, String s) {
        var line = Math.max(0, pos.line() - 1);
        var column = Math.max(0, pos.column() - 1);
        return "\n".repeat(line) +
                " ".repeat(column) +
                s;
    }

    @NonNull
    private MethodDeclaration transformMethodDecl(TextualJMLMethodDecl decl,
            List<Comment> originalComments)
            throws SLTranslationException {
        assert !originalComments.isEmpty();

        // prepend Java modifiers
        PositionedString declWithMods =
            new PositionedString(decl.getParsableDeclaration());

        // only handle model methods
        if (!decl.getModifiers().contains(JMLModifier.MODEL)) {
            throw new SLTranslationException("JML method declaration has to be model!",
                declWithMods.location);
        }

        // parse declaration, attach to AST
        MethodDeclaration methodDecl;
        var md = services.getParser()
                .parseMethodDeclaration(declWithMods.text);
        if (md.getResult().isEmpty()) {
            throw new SLTranslationException(
                "could not parse", declWithMods.location);
        }
        methodDecl = md.getResult().get();
        updatePositionInformation(methodDecl, declWithMods.location.getPosition());
        // about the 0 see the comment in transformFieldDecl() above

        // add model modifier
        methodDecl.addModifier(Modifier.Keyword.MODEL);
        if (decl.getModifiers().contains(JMLModifier.TWO_STATE)) {
            methodDecl.addModifier(Modifier.Keyword.TWO_STATE);
        }
        if (decl.getModifiers().contains(JMLModifier.NO_STATE)) {
            methodDecl.addModifier(Modifier.Keyword.NO_STATE);
        }

        // set comments: the original list of comments with the declaration,
        // and the JML modifiers
        NodeList<Comment> newComments = new NodeList<>(originalComments);
        Comment jmlComment = getJMLModComment(decl.getModifiers());
        jmlComment.setParentNode(methodDecl);
        newComments.add(jmlComment);
        methodDecl.setAssociatedSpecificationComments(newComments);
        return methodDecl;
    }

    private Statement storeInStatement(TextualJMLConstruct construct) {
        var stmt = new EmptyStmt();
        var pos = construct.getLocation().getPosition();
        var rangePos = new Position(pos.line(), pos.column());
        stmt.setRange(Range.range(rangePos, rangePos));
        stmt.setData(KEY_CONSTRUCT, construct);
        return stmt;
    }

    private Statement transformAssertStatement(TextualJMLAssertStatement stat) {
        return storeInStatement(stat);
    }

    private Statement transformSetStatement(TextualJMLSetStatement stat) {
        // parse statement, attach to AST
        var location = Location.fromToken(stat.getAssignment().start);
        String assignment = getFullText(stat.getAssignment()).substring(3);
        var result = services.getParser().parseBlock("{" + assignment + "}");
        // TODO javaparser error handling!
        var stmtList = result.getResult().orElseThrow().getStatements();
        assert stmtList.size() == 1;
        var assignStmt = stmtList.get(0);
        shiftPosition(assignStmt, location.getPosition());
        // updatePositionInformation(assignStmt, pos);
        return assignStmt;
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

    private Statement transformMergePointDecl(TextualJMLMergePointDecl stat) {
        return storeInStatement(stat);
    }

    private static <T> Optional<T> extractData(Node node, DataKey<T> key) {
        try {
            var result = node.getData(key);
            node.removeData(key);
            return Optional.of(result);
        } catch (IllegalStateException ignored) {
            return Optional.empty();
        }
    }

    private void transformClassLevelComments(TypeDeclaration<?> td, Node child, URI fileName)
            throws SLTranslationException {
        List<Comment> comments = extractData(child, JMLCommentTransformer.BEFORE_COMMENTS)
                .orElse(new ArrayList<>());
        if (!comments.isEmpty()) {
            child.setAssociatedSpecificationComments(new NodeList<>(comments));
        }
        comments.addAll(extractData(child, JMLCommentTransformer.AFTER_COMMENTS)
                .orElse(Collections.emptyList()));
        if (comments.isEmpty()) {
            return;
        }
        // concatenate comments of child, determine position
        String concatenatedComment = concatenate(comments);
        Position astPos = comments.get(0).getRange().get().begin;
        de.uka.ilkd.key.java.Position pos = de.uka.ilkd.key.java.Position.fromJPPosition(astPos);

        // call preparser
        PreParser pp = new PreParser(
            ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings().getUseOriginLabels());
        ImmutableList<TextualJMLConstruct> constructs =
            pp.parseClassLevel(concatenatedComment, fileName, pos);
        warnings = warnings.append(pp.getWarnings());

        // handle model and ghost declarations in textual constructs
        for (TextualJMLConstruct c : constructs) {
            if (c instanceof TextualJMLFieldDecl) {
                td.addMember(transformClassFieldDecl((TextualJMLFieldDecl) c, comments));
            } else if (c instanceof TextualJMLMethodDecl) {
                td.addMember(transformMethodDecl((TextualJMLMethodDecl) c, comments));
            }
        }
    }

    private static Optional<BlockStmt> findInnermostBlock(Node node) {
        while (true) {
            node = node.getParentNode().get();
            if (node instanceof BlockStmt) {
                return Optional.of((BlockStmt) node);
            }
            if (node.getParentNode().isEmpty()) {
                return Optional.empty();
            }
        }
    }

    private int transformMethodLevelCommentsAt(Node pe, List<Comment> comments, URI fileName,
            int offset) throws SLTranslationException {
        // concatenate comments, determine position
        Position astPos = comments.get(0).getRange().get().begin;
        de.uka.ilkd.key.java.Position pos = de.uka.ilkd.key.java.Position.fromJPPosition(
            astPos);

        // call preparser
        var io = new PreParser(
            ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings().getUseOriginLabels());
        String concat = concatenate(comments);
        ImmutableList<TextualJMLConstruct> constructs =
            io.parseMethodLevel(concat, fileName, pos);
        warnings = warnings.append(io.getWarnings());

        // handle ghost declarations and set assignments in textual constructs
        for (TextualJMLConstruct c : constructs) {
            Statement statement;
            if (c instanceof TextualJMLFieldDecl) {
                statement = transformVariableDecl((TextualJMLFieldDecl) c);
            } else if (c instanceof TextualJMLSetStatement) {
                statement = transformSetStatement((TextualJMLSetStatement) c);
            } else if (c instanceof TextualJMLMergePointDecl) {
                statement = transformMergePointDecl((TextualJMLMergePointDecl) c);
            } else if (c instanceof TextualJMLAssertStatement) {
                statement = transformAssertStatement((TextualJMLAssertStatement) c);
            } else {
                LOGGER.trace("{}: Jml element unhandled: {}", c.getLocation(), c.getClass());
                continue;
            }
            var target = findInnermostBlock(pe).orElseThrow();
            target.addStatement(offset, statement);
            offset += 1;
        }
        return offset;
    }

    private void transformMethodLevelCommentsHelper(Node pe, URI fileName)
            throws SLTranslationException {
        // recurse to all pre-existing children
        var children = pe.getChildNodes().toArray(new Node[0]);
        for (Node aChildren : children) {
            transformMethodLevelCommentsHelper(aChildren, fileName);
        }

        // get comments
        var before = extractData(pe, JMLCommentTransformer.BEFORE_COMMENTS);
        before.ifPresent(c -> pe.setAssociatedSpecificationComments(new NodeList<>(c)));

        if (pe instanceof MethodDeclaration || pe.getParentNode().isEmpty()) {
            assert !pe.containsData(JMLCommentTransformer.AFTER_COMMENTS);
            return;
        }

        var parent = findInnermostBlock(pe);
        boolean hasStatement = pe instanceof Statement;
        int parentOffset;
        if (parent.isPresent()) {
            var stmts = parent.get().getStatements();
            // If pe is a statement we insert before the statement,
            // else insert at the end (this happens only for orphan comments that are always at the
            // end)
            parentOffset = hasStatement ? stmts.indexOf(pe) : stmts.size();
        } else {
            parentOffset = -1;
        }

        if (before.isPresent()) {
            parentOffset = transformMethodLevelCommentsAt(pe, before.get(), fileName, parentOffset);
        }
        var after = extractData(pe, JMLCommentTransformer.AFTER_COMMENTS);
        if (after.isPresent()) {
            transformMethodLevelCommentsAt(pe, after.get(), fileName,
                parentOffset + (hasStatement ? 1 : 0));
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
                if (unit.getAssociatedSpecificationComments().isPresent()) {
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

    @Override
    public void apply(CompilationUnit cu) {
        // abort if JML is disabled
        if (!ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().isUseJML()) {
            return;
        }

        try {
            URI resource = cu.getStorage()
                    .map(it -> it.getPath().toUri())
                    .orElse(null);

            for (var td : cu.getTypes()) {
                for (Node child : td.getChildNodes().toArray(new Node[0])) {
                    transformClassLevelComments(td, child, resource);
                }

                // iterate over all pre-existing constructors
                for (var constructor : td.getConstructors()) {
                    transformMethodLevelCommentsHelper(constructor.getBody(), resource);
                }

                // iterate over all pre-existing methods
                for (var method : td.getMethods()) {
                    // might be ImplicitEnumMethod
                    if (method.getBody().isPresent()) {
                        transformMethodLevelCommentsHelper(method.getBody().get(),
                            resource);
                    }
                }
            }
        } catch (SLTranslationException e) {
            // Wrap the exception into a runtime exception because recoder does
            // not allow otherwise. It will be unwrapped later ...
            throw new RuntimeException(e);
        }
    }
}
