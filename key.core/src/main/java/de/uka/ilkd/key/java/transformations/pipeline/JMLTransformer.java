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

import com.github.javaparser.*;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.key.JmlDoc;
import com.github.javaparser.ast.key.JmlDocModifier;
import com.github.javaparser.ast.key.JmlDocsBodyDeclaration;
import com.github.javaparser.ast.key.JmlDocsStatements;
import com.github.javaparser.ast.nodeTypes.NodeWithBody;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.nodeTypes.NodeWithOptionalBlockStmt;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.EmptyStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.VoidVisitorWithDefaults;
import com.google.common.base.Strings;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.speclang.njml.PreParser;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.MiscTools;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.Interval;
import org.jspecify.annotations.NonNull;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.StringUtil;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.net.URI;
import java.util.*;
import java.util.regex.Pattern;


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
     * @param services the CrossReferenceServiceConfiguration to access model
     *                 information
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
        Iterator<Comment> iter = comments.iterator();
        if (!iter.hasNext()) {
            return sb.toString();
        }
        Comment first = iter.next();
        if (first instanceof BlockComment || first instanceof JavadocComment) {
            sb.append("/*").append(first.getContent()).append("*/");
        } else {
            sb.append("//").append(first.getContent());
        }
        Position last = first.getRange().get().end;
        while (iter.hasNext()) {
            Comment comment = iter.next();
            int line;
            int column;
            Position pos = comment.getRange().get().begin;
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
        for (JMLModifier mod : mods) {
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
        de.uka.ilkd.key.java.Position pos = de.uka.ilkd.key.java.Position.newOneBased(ctx.start.getLine(), column);
        Location location = new Location(
                MiscTools.getURIFromTokenSource(ctx.start.getTokenSource().getSourceName()), pos);
        return new PositionedString(sb.toString(), location);
    }

    /**
     * Puts the JML modifiers from the passed list into a string enclosed in JML
     * markers.
     */
    private BlockComment getJMLModComment(ImmutableList<JMLModifier> mods) {
        StringBuilder sb = new StringBuilder("@");
        for (JMLModifier mod : mods) {
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
            final Range range = pe.getRange().get();
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
        return isGhost ? Modifier.DefaultKeyword.JML_GHOST : Modifier.DefaultKeyword.JML_MODEL;
    }

    @NonNull
    private FieldDeclaration transformClassFieldDecl(TextualJMLFieldDecl decl) throws SLTranslationException {
        NodeList<Modifier> modifiers = new NodeList<>();
        for (JMLModifier m : decl.getModifiers()) {
            Modifier mod = new Modifier(m.getParserKeyword());
            modifiers.add(mod);
        }


        final var dims = decl.getDecl().typespec().dims();

        int arrayDims = (dims!=null?dims.LBRACKET().size():0) + decl.getDecl().LBRACKET().size();
        Type type = StaticJavaParser.parseType(decl.getDecl().typespec().type().getText() + Strings.repeat("[]", arrayDims));
        String name = decl.getDecl().IDENT().getText();

        //TODO Copy position from textual jml field decl
        FieldDeclaration fieldDecl = new FieldDeclaration(
                modifiers, new VariableDeclarator(type, name)
        );

        if (decl.getModifiers().contains(JMLModifier.INSTANCE)
                && decl.getModifiers().contains(JMLModifier.STATIC)) {
            throw new SLTranslationException(
                    "JML field can't be static and instance at once " + decl.getDecl().getText());
        }
        return fieldDecl;
    }

    @NonNull
    private Statement transformVariableDecl(TextualJMLFieldDecl decl)
            throws SLTranslationException {
        // prepend Java modifiers
        PositionedString declWithMods = convertToString(decl.getModifiers(), decl.getDecl());
        Modifier.Keyword mod = getModifier(decl);

        // parse declaration, attach to AST

        if (mod == Modifier.DefaultKeyword.JML_MODEL) {
            throw new SLTranslationException(
                    "JML model fields cannot be declared within a method!",
                    declWithMods.location);
        }

        ParseResult<BlockStmt> block = services.getParser().parseBlock(
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
        int line = Math.max(0, pos.line() - 1);
        int column = Math.max(0, pos.column() - 1);
        return "\n".repeat(line) +
                " ".repeat(column) +
                s;
    }

    @NonNull
    private MethodDeclaration transformMethodDecl(TextualJMLMethodDecl decl)
            throws SLTranslationException {
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
        ParseResult<MethodDeclaration> md = services.getParser().parseMethodDeclaration(declWithMods.text);
        if (md.getResult().isEmpty()) {
            throw new SLTranslationException(
                    "could not parse", declWithMods.location);
        }
        methodDecl = md.getResult().get();
        updatePositionInformation(methodDecl, declWithMods.location.getPosition());
        // about the 0 see the comment in transformFieldDecl() above

        // add model modifier
        methodDecl.addModifier(Modifier.DefaultKeyword.JML_MODEL);
        if (decl.getModifiers().contains(JMLModifier.TWO_STATE)) {
            methodDecl.addModifier(Modifier.DefaultKeyword.JML_TWO_STATE);
        }
        if (decl.getModifiers().contains(JMLModifier.NO_STATE)) {
            methodDecl.addModifier(Modifier.DefaultKeyword.JML_NO_STATE);
        }
        return methodDecl;
    }

    private Statement storeInStatement(TextualJMLConstruct construct) {
        EmptyStmt stmt = new EmptyStmt();
        de.uka.ilkd.key.java.Position pos = construct.getLocation().getPosition();
        Position rangePos = new Position(pos.line(), pos.column());
        stmt.setRange(Range.range(rangePos, rangePos));
        stmt.setData(KEY_CONSTRUCT, construct);
        return stmt;
    }

    private Statement transformAssertStatement(TextualJMLAssertStatement stat) {
        return storeInStatement(stat);
    }

    private Statement transformSetStatement(TextualJMLSetStatement stat) {
        // parse statement, attach to AST
        Location location = Location.fromToken(stat.getAssignment().start);
        String assignment = getFullText(stat.getAssignment()).substring(3);
        ParseResult<BlockStmt> result = services.getParser().parseBlock("{" + assignment + "}");
        // TODO javaparser error handling!
        NodeList<Statement> stmtList = result.getResult().orElseThrow().getStatements();
        assert stmtList.size() == 1;
        Statement assignStmt = stmtList.get(0);
        shiftPosition(assignStmt, location.getPosition());
        // updatePositionInformation(assignStmt, pos);
        return assignStmt;
    }

    private void shiftPosition(Node node, de.uka.ilkd.key.java.Position pos) {
        shiftPosition(node, pos.line(), pos.column());
    }

    private void shiftPosition(Node node, int line, int column) {
        final Optional<TokenRange> tokenRange = node.getTokenRange();
        if (tokenRange.isPresent()) {
            Iterator<JavaToken> iter = tokenRange.get().iterator();
            iter.forEachRemaining(it -> {
                if (it.getRange().isPresent()) {
                    Range range = it.getRange().get();
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
            T result = node.getData(key);
            node.removeData(key);
            return Optional.of(result);
        } catch (IllegalStateException ignored) {
            return Optional.empty();
        }
    }

    private final JmlDocSanitizer sanitizer = new JmlDocSanitizer(Set.of("key"));


    public static final DataKey<List<TextualJMLSpecCase>> KEY_SPEC_CASE = new DataKey<>() {
    };
    public static final DataKey<List<TextualJMLConstruct>> KEY_CLASS_SPEC = new DataKey<>() {
    };

    private void transformClassLevelComments(TypeDeclaration<?> td) throws SLTranslationException {
        URI fileName = td.findCompilationUnit().get().getStorage().get().getPath().toUri();

        ArrayList<BodyDeclaration<?>> members = new ArrayList<>(td.getMembers());
        ArrayList<TextualJMLSpecCase> specCases = new ArrayList<>();

        for (int i = 0; i < members.size(); i++) {
            BodyDeclaration<?> member = members.get(i);
            if (member instanceof JmlDocsBodyDeclaration bd) {
                String concatenatedComment = sanitizer.asString(bd.jmlDocs());
                Position astPos = bd.getRange().get().begin;
                de.uka.ilkd.key.java.Position pos = de.uka.ilkd.key.java.Position.fromJPPosition(astPos);

                // The preparser split along the grammar rules in KeYParser.g4, and gives you a list of JML entities.
                PreParser pp = new PreParser(
                        ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings().getUseOriginLabels());
                ImmutableList<TextualJMLConstruct> constructs = pp.parseClassLevel(concatenatedComment, fileName, pos);
                warnings = warnings.append(pp.getWarnings());

                // handle model and ghost declarations in textual constructs
                for (TextualJMLConstruct c : constructs) {
                    if (c instanceof TextualJMLFieldDecl fd) {
                        td.addMember(transformClassFieldDecl(fd));
                    } else if (c instanceof TextualJMLMethodDecl md) {
                        final var decl = transformMethodDecl(md);
                        for (var specCase : specCases) {
                            addSpec(decl, specCase);
                        }
                        td.addMember(decl);
                        specCases.clear();
                    } else if (c instanceof TextualJMLClassAxiom
                            || c instanceof TextualJMLRepresents
                            || c instanceof TextualJMLClassInv
                            || c instanceof TextualJMLInitially
                            || c instanceof TextualJMLDepends) {
                        addClassSpec(td, c);
                    } else if (c instanceof TextualJMLSpecCase specCase) {
                        specCases.add(specCase);
                    } else {
                        System.out.println("blubb " + c.getClass());
                    }
                }
            }

            if (member instanceof CallableDeclaration<?> c) {
                for (var specCase : specCases) {
                    addSpec(c, specCase);
                }
                specCases.clear();
            }
        }

    }

    private void addClassSpec(TypeDeclaration<?> td, TextualJMLConstruct c) {
        if (!td.containsData(KEY_CLASS_SPEC)) {
            td.setData(KEY_CLASS_SPEC, new ArrayList<>(4));
        }
        List<TextualJMLConstruct> specList = td.getData(KEY_CLASS_SPEC);
        specList.add(c);
    }

    private void addSpec(Node nextMember, TextualJMLSpecCase specCase) {
        if (!nextMember.containsData(KEY_SPEC_CASE)) {
            nextMember.setData(KEY_SPEC_CASE, new ArrayList<>(4));
        }
        List<TextualJMLSpecCase> specList = nextMember.getData(KEY_SPEC_CASE);
        specList.add(specCase);
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

    private void transformMethodLevelCommentsAt(BlockStmt blockStmt) throws SLTranslationException {
        PreParser io = new PreParser(ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings().getUseOriginLabels());
        var stmts = new ArrayList<>(blockStmt.getStatements());

        for (int i = 0; i < stmts.size(); i++) {
            var stmt = stmts.get(i);
            if (stmt instanceof BlockStmt bs) {
                transformMethodLevelCommentsAt(bs);
            }

            if (stmt instanceof JmlDocsStatements doc) {
                Position astPos = doc.getRange().get().begin;
                de.uka.ilkd.key.java.Position pos = de.uka.ilkd.key.java.Position.fromJPPosition(astPos);
                String concat = sanitizer.asString(doc.getJmlDocs());
                ImmutableList<TextualJMLConstruct> constructs = io.parseMethodLevel(concat, null, pos);
                warnings = warnings.append(io.getWarnings());


                int j = 0;
                // handle ghost declarations and set assignments in textual constructs
                outer: for (TextualJMLConstruct c : constructs) {
                    j++;
                    Statement statement;
                    switch (c) {
                        case TextualJMLFieldDecl field -> statement = transformVariableDecl(field);
                        case TextualJMLSetStatement set -> statement = transformSetStatement(set);
                        case TextualJMLMergePointDecl mergePointDecl -> statement = transformMergePointDecl(mergePointDecl);
                        case TextualJMLAssertStatement assertStatement -> statement = transformAssertStatement(assertStatement);
                        case TextualJMLSpecCase spec -> {
                            for (int k = i; k < stmts.size(); k++) {
                                var search = stmts.get(k);
                                if (search instanceof BlockStmt bs || search instanceof NodeWithBody<?> /*aka loops*/) {
                                    addSpec(search, spec);
                                    continue outer;
                                }
                            }
                            // Nothing found error
                            throw new IllegalStateException("Could not find a suitable statement for the loop/block/invariant");
                        }
                        default -> {
                            LOGGER.error("{}: Jml element unhandled: {}", c.getLocation(), c.getClass());
                            continue;
                        }
                    }
                    //TODO Block, loop specifications contracts
                    blockStmt.getStatements().add(i + j, statement);
                }
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
                if (unit.getAssociatedSpecificationComments().isPresent()) {
                    tdComments.addAll(TransformationPipelineServices.cloneList(
                            unit.getAssociatedSpecificationComments().get()));
                }
                td.setAssociatedSpecificationComments(tdComments);
            }

            // iterate over all type declarations of the compilation unit
            List<TypeDeclaration<?>> typeDeclarations = getAllTypes(unit);
            for (TypeDeclaration<?> td : typeDeclarations) {
                // collect pre-existing operations
                List<? extends ConstructorDeclaration> constructorList = td.getConstructors();
                List<MethodDeclaration> methodList = td.getMethods();
            }
        }
    }

    private List<TypeDeclaration<?>> getAllTypes(CompilationUnit unit) {
        LinkedList<TypeDeclaration<?>> seq = new LinkedList<TypeDeclaration<?>>();
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

            for (TypeDeclaration<?> td : cu.getTypes()) {
                transformClassLevelComments(td);

                for (BodyDeclaration<?> member : td.members()) {
                    if (member instanceof NodeWithOptionalBlockStmt<?> call && call.getBody().isPresent()) {
                        transformMethodLevelCommentsAt(call.getBody().get());
                    }

                    if (member instanceof NodeWithModifiers<?> hasMods) {
                        transformModifiers(hasMods);
                    }
                }
            }
        } catch (SLTranslationException e) {
            // Wrap the exception into a runtime exception because recoder does
            // not allow otherwise. It will be unwrapped later ...
            throw new RuntimeException(e);
        }
    }

    private void transformModifiers(NodeWithModifiers<?> hasMods) {
        PreParser pp = new PreParser(
                ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings().getUseOriginLabels());
        warnings = warnings.append(pp.getWarnings());

        for (Modifier mod : hasMods.getModifiers()) {
            var kw = mod.getKeyword();
            if (kw instanceof JmlDocModifier jdm) {
                var modifiers = sanitizer.asString(jdm.getJmlDocs());
                var jmlMods = pp.parseModifiers(modifiers);
                for (var jmlMod : jmlMods) {
                    hasMods.addModifier(jmlMod.getParserKeyword());
                }
            }
        }
    }
}

record JmlDocSanitizer(Set<String> enabledKeys) {

    public String asString(NodeList<JmlDoc> jmlDocs) {
        return asString(jmlDocs, true);
    }

    public String asStringJT(Collection<JavaToken> jmlDocs, boolean emulateGlobalPosition) {
        if (jmlDocs.isEmpty()) return "";
        StringConstructor s = new StringConstructor();
        for (JavaToken tok : jmlDocs) {
            if (emulateGlobalPosition) {
                final Optional<Range> range = tok.getRange();
                if (range.isPresent()) {
                    Position cur = range.get().begin;
                    s.expandTo(cur.line, cur.column);
                }
            } else {
                s.append("\n");
            }
            s.append(tok.getText());
        }
        return toSanitizedString(s.getBuffer());
    }

    public String asString(Collection<Token> jmlDocs, boolean emulateGlobalPosition) {
        if (jmlDocs.isEmpty()) return "";
        StringConstructor s = new StringConstructor();
        for (Token tok : jmlDocs) {
            if (emulateGlobalPosition) {
                s.expandTo(tok.beginLine, tok.beginColumn);
            } else {
                s.append("\n");
            }
            s.append(tok.image);
        }
        return toSanitizedString(s.getBuffer());
    }

    public String asString(NodeList<JmlDoc> jmlDocs, boolean emulateGlobalPosition) {
        return asStringJT(jmlDocs.stream().map(JmlDoc::getContent).toList(), emulateGlobalPosition);
    }

    public String toSanitizedString(StringBuilder s) {
        cleanComments(s);
        cleanAtSigns(s);
        return s.toString();
    }

    private static void cleanAtSigns(StringBuilder s) {
        for (int pos = 0; pos < s.length(); pos++) {
            char cur = s.charAt(pos);
            if (cur == '\n') {
                ++pos;
                for (; pos < s.length(); pos++) {
                    if (!Character.isWhitespace(s.charAt(pos))) break;
                }
                for (; pos < s.length(); pos++) {
                    if ('@' == s.charAt(pos)) {
                        s.setCharAt(pos, ' ');
                    }
                }
            }
        }
    }

    private void cleanComments(StringBuilder s) {
        int cur = 0;
        for (; cur < s.length() - 1; ++cur) {
            if (isJavaCommentStart(s, cur)) {
                if (isJmlComment(s, cur)) {
                    cur = activateJmlComment(s, cur);
                } else {
                    cur = cleanComment(s, cur);
                }
            }
        }
    }

    private int cleanComment(StringBuilder s, int pos) {
        char second = s.charAt(pos + 1);
        int end;
        if (second == '*') {
            end = s.indexOf("*/", pos + 2) + 2;
        } else {
            end = s.indexOf("\n", pos + 2);
        }
        if (end == -1) {
            // Comment is aborted by EOF rather than */ or \n
            end = s.length();
        }
        for (int i = pos; i < end; i++) {
            s.setCharAt(i, ' ');
        }
        return end;
    }

    private int activateJmlComment(StringBuilder s, int pos) {
        boolean blockComment = s.charAt(pos) == '/' && s.charAt(pos + 1) == '*';
        if (blockComment) {
            int endPos = s.indexOf("*/", pos);
            if (endPos >= 0) {
                s.setCharAt(endPos, ' ');
                s.setCharAt(endPos + 1, ' ');
            }
        }
        for (int i = pos; i < s.length(); i++) {
            char point = s.charAt(i);
            s.setCharAt(i, ' ');
            if (point == '@') {
                return i;
            }
        }
        return s.length();
    }

    private boolean isJmlComment(StringBuilder s, int pos) {
        int posAt = s.indexOf("@", pos + 2);
        if (posAt < 0) return false;
        for (int i = pos + 2; i < posAt; i++) {
            int point = s.charAt(i);
            if (!(Character.isJavaIdentifierPart(point) || point == '-' || point == '+')) {
                return false;
            }
        }
        // unconditional JML comment
        if (pos + 2 == posAt) return true;
        String[] keys = splitTags(s.substring(pos + 2, posAt));
        return isActiveJmlSpec(keys);
    }

    private static final Pattern tag = Pattern.compile("(?=[+-])");

    private static String[] splitTags(String substring) {
        return tag.split(substring);
    }

    private boolean isJavaCommentStart(StringBuilder s, int pos) {
        return s.charAt(pos) == '/' && (s.charAt(pos + 1) == '*' || s.charAt(pos + 1) == '/');
    }

    public static boolean isActiveJmlSpec(Collection<String> activeKeys, String[] keys) {
        if (keys.length == 0) {
            // a JML annotation with no keys is always included,
            return true;
        }
        // a JML annotation with at least one positive-key is only included
        boolean plusKeyFound = false;
        // if at least one of these positive keys is enabled
        boolean enabledPlusKeyFound = false;
        // a JML annotation with an enabled negative-key is ignored (even if there are enabled positive-keys).
        boolean enabledNegativeKeyFound = false;
        for (String marker : keys) {
            if (marker.isEmpty()) continue;
            plusKeyFound = plusKeyFound || isPositive(marker);
            enabledPlusKeyFound = enabledPlusKeyFound || isPositive(marker) && isEnabled(activeKeys, marker);
            enabledNegativeKeyFound = enabledNegativeKeyFound || isNegative(marker) && isEnabled(activeKeys, marker);
            if ("-".equals(marker) || "+".equals(marker)) {
                return false;
            }
        }
        return (!plusKeyFound || enabledPlusKeyFound) && !enabledNegativeKeyFound;
    }

    public boolean isActiveJmlSpec(String[] keys) {
        return isActiveJmlSpec(enabledKeys, keys);
    }

    private static boolean isNegative(String marker) {
        return marker.charAt(0) == '-';
    }

    private static boolean isEnabled(Collection<String> enabledKeys, String marker) {
        // remove [+-] prefix
        return enabledKeys.contains(marker.substring(1).toLowerCase());
    }

    private static boolean isPositive(String marker) {
        return marker.charAt(0) == '+';
    }
}

class StringConstructor {

    private final StringBuilder sb = new StringBuilder(1024);

    // JavaCC starts with 1/1
    private int curLine = 1;

    private int curColumn = 1;

    public StringConstructor append(String value) {
        sb.ensureCapacity(sb.length() + value.length() + 1);
        for (char c : value.toCharArray()) {
            sb.append(c);
            if (c == '\n') {
                curColumn = 1;
                curLine++;
            } else {
                curColumn++;
            }
        }
        return this;
    }

    public StringConstructor expandTo(int line, int column) {
        if (curLine > line || (curLine == line && curColumn > column)) {
            throw new IllegalArgumentException();
        }
        for (; curLine < line; curLine++) {
            sb.append("\n");
            curColumn = 1;
        }
        for (; curColumn < column; curColumn++) {
            sb.append(" ");
        }
        return this;
    }

    @Override
    public String toString() {
        return sb.toString();
    }

    public StringBuilder getBuffer() {
        return sb;
    }
}