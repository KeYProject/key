/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import java.net.URI;
import java.util.*;
import java.util.regex.Pattern;

import com.github.javaparser.ast.nodeTypes.NodeWithParameters;
import de.uka.ilkd.key.java.ConvertException;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.speclang.njml.PreParser;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.parsing.BuildingException;

import org.key_project.util.collection.ImmutableList;

import com.github.javaparser.*;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.Modifier.DefaultKeyword;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.key.*;
import com.github.javaparser.ast.nodeTypes.NodeWithBody;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.nodeTypes.NodeWithOptionalBlockStmt;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.Type;
import com.google.common.base.Strings;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static de.uka.ilkd.key.java.transformations.MarkerStatementHelper.*;

/// JMLTransformer translates the JML annotation comments into parse trees that are attached
/// to the Java AST nodes.
/// This class handles JML annotations at three different levels:
///
/// * Type level / Compilation Unit
///
/// Currently, the support is limited for JML modifiers on classes
///
/// * Class level / Body Declarations
///
/// On this level, type-internal declaration can appear like class invariants,
/// model methods and ghost fields. But also modifiers are captured
///
/// * Method level / Statements
///
/// Support for ghost statements.
///
/// After execution this {@link JavaTransformer}, contracts are attached to
/// {@link MethodDeclaration}, or {@link BlockStmt}, {@link FieldDeclaration} and
/// {@link MethodDeclaration} were introduced for ghost and model declarations,
/// JML statements (assume, assert, ...) are inserted into the bodies using
/// {@link KeYMarkerStatement}.
///
/// You can access attached JML information using the {@link DataKey} in
/// [JMLTransformer#KEY_SPEC_CASE],
/// [JMLTransformer#KEY_SPEC_CASE], and [JMLTransformer#KEY_SPEC_CASE].
///
/// JMLModifier are reduced to *normal* modifier of {@link DefaultKeyword}.
///
/// @author weigl
/// @author drodt
/// @author lanzinger
/// @author bubel
/// @author pfeifer
/// @author ulbrich
@SuppressWarnings("OptionalGetWithoutIsPresent")
public final class JMLTransformer extends JavaTransformer {
    public static final EnumSet<JMLModifier> JAVA_MODS =
        EnumSet.of(JMLModifier.ABSTRACT, JMLModifier.FINAL, JMLModifier.PRIVATE,
            JMLModifier.PROTECTED, JMLModifier.PUBLIC, JMLModifier.STATIC);

    private static final Logger LOGGER = LoggerFactory.getLogger(JMLTransformer.class);

    private final JmlDocSanitizer sanitizer = new JmlDocSanitizer(
            ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().getJmlEnabledKeys());

    /// KEY for contracts
    public static final DataKey<List<TextualJMLConstruct>> KEY_SPEC_CASE = new DataKey<>() {
    };
    /// KEY for class level specification
    public static final DataKey<List<TextualJMLConstruct>> KEY_CLASS_SPEC = new DataKey<>() {
    };

    /// KEY for loop specifications
    public static final DataKey<List<TextualJMLLoopSpec>> KEY_LOOP_SPEC = new DataKey<>() {
    };


    /**
     * Creates a transformation that adds JML specific elements, for example
     * ghost fields and model method declarations.
     *
     * @param services the CrossReferenceServiceConfiguration to access model
     *        information
     */
    public JMLTransformer(TransformationPipelineServices services) {
        super(services);
    }

    /**
     * Transform the given ghost or model field declaration into a "real" field declaration, and
     * attach modifiers.
     *
     * @param decl the given textual model/ghost field declaration
     * @return the newly created FieldDeclaration
     * @throws SLTranslationException
     */
    private @NonNull FieldDeclaration transformClassFieldDecl(TextualJMLFieldDecl decl)
            throws SLTranslationException {
        NodeList<Modifier> modifiers = new NodeList<>();
        for (JMLModifier m : decl.getModifiers()) {
            Modifier mod = new Modifier(m.getParserKeyword());
            modifiers.add(mod);
        }

        final var dims = decl.getDecl().typespec().dims();

        // for cases like `int[] a[]`, which are allowed in Java (a is 2d here)
        int arrayDims =
            (dims != null ? dims.LBRACKET().size() : 0) + decl.getDecl().LBRACKET().size();
        Type type = StaticJavaParser.parseType(
            decl.getDecl().typespec().type().getText() + Strings.repeat("[]", arrayDims));
        String name = decl.getDecl().IDENT().getText();

        // TODO Copy position from textual jml field decl
        FieldDeclaration fieldDecl = new FieldDeclaration(
            modifiers, new VariableDeclarator(type, name));

        if (decl.getModifiers().contains(JMLModifier.INSTANCE)
                && decl.getModifiers().contains(JMLModifier.STATIC)) {
            throw new SLTranslationException(
                "JML field can't be static and instance at once " + decl.getDecl().getText());
        }
        return fieldDecl;
    }

    /**
     * Transform the given local ghost/model variable declaration into a "real" statement.
     *
     * @param decl the given ghost/model declaration (TextualJMLFieldDecl is also used to represent
     *        local variable declarations!)
     * @return the newly created statement
     */
    private @NonNull Statement transformVariableDecl(TextualJMLFieldDecl decl) {
        NodeList<Modifier> modifiers = new NodeList<>();
        for (JMLModifier m : decl.getModifiers()) {
            if (m.equals(JMLModifier.MODEL)) {
                throw new BuildingException(decl.getDecl(),
                    "Model modifier on variable declaration detected, only model fields are allowed");
            }

            Modifier mod = new Modifier(m.getParserKeyword());
            modifiers.add(mod);
        }

        final var dims = decl.getDecl().typespec().dims();

        // for cases like `int[] a[]`, which are allowed in Java (a is 2d here)
        int arrayDims =
            (dims != null ? dims.LBRACKET().size() : 0) + decl.getDecl().LBRACKET().size();
        Type type = StaticJavaParser.parseType(
            decl.getDecl().typespec().type().getText() + Strings.repeat("[]", arrayDims));
        String name = decl.getDecl().IDENT().getText();

        // TODO Copy position from textual jml field decl
        var expr = new VariableDeclarationExpr(type, name);
        expr.setModifiers(modifiers);
        if (decl.getDecl().initialiser() != null) {
            var init = decl.getDecl().initialiser().expression().getText();
            expr.getVariables().getFirst().setInitializer(StaticJavaParser.parseExpression(init));
        }
        return new ExpressionStmt(expr);
    }

    /**
     * Transform the given model method declaration into a "real" method declaration.
     *
     * @param decl the give textual model method declaration
     * @param jmlModifiers
     * @return the new method declaration
     * @throws SLTranslationException
     */
    private @NonNull MethodDeclaration transformMethodDecl(TextualJMLMethodDecl decl,
            @Nullable TextualJMLModifierList jmlModifiers)
            throws SLTranslationException {
        // prepend Java modifiers
        PositionedString declWithMods =
            new PositionedString(decl.getParsableDeclaration());

        ImmutableList<JMLModifier> mods =
            jmlModifiers != null ? jmlModifiers.getModifiers() : ImmutableList.of();
        ImmutableList<JMLModifier> modifiers = mods.prepend(decl.getModifiers());

        // only handle model methods
        if (!modifiers.contains(JMLModifier.MODEL)) {
            throw new SLTranslationException("JML method declaration has to be model!",
                declWithMods.location);
        }

        // parse declaration, attach to AST
        MethodDeclaration methodDecl;
        ParseResult<MethodDeclaration> md =
            services.getParser().parseMethodDeclaration(declWithMods.text);
        if (md.getResult().isEmpty()) {
            throw new SLTranslationException(
                "could not parse", declWithMods.location);
        }
        methodDecl = md.getResult().get();

        // add model modifier
        for (var modifier : modifiers) {
            methodDecl.addModifier(modifier.getParserKeyword());
        }
        addSpec(methodDecl, decl);
        return methodDecl;
    }


    private Statement transformAssertStatement(TextualJMLAssertStatement stat) {
        KeyAst.Expression ctx = stat.getContext();
        de.uka.ilkd.key.java.Position pos = ctx.getStartLocation().getPosition();
        int kind = switch (stat.getKind()) {
            case ASSERT -> KIND_ASSERT;
            case ASSUME -> KIND_ASSUME;
        };
        KeYMarkerStatement stmt = new KeYMarkerStatement(kind);
        // TODO simulate/ copy token range.
        stmt.setData(KEY_EXPR, ctx);
        return stmt;
    }

    private Statement transformSetStatement(TextualJMLSetStatement stat) {
        KeyAst.SetStatementContext ctx = new KeyAst.SetStatementContext(stat.getAssignment());
        // de.uka.ilkd.key.java.Position pos = ctx.getStartLocation().getPosition();
        KeYMarkerStatement stmt = new KeYMarkerStatement(KIND_SET);
        // TODO simulate/ copy token range.
        stmt.setData(KEY_ASSIGN, ctx);
        return stmt;
    }

    private KeYMarkerStatement transformMergePointDecl(TextualJMLMergePointDecl stat) {
        KeYMarkerStatement mps = new KeYMarkerStatement(KIND_MERGE_POINT);
        mps.setData(KEY_MERGE_POINT, stat);
        return mps;
    }

    /**
     * Transform all class level JML comments (such as class invariants, represents clauses,
     * method contract, model method declarations, ...) with the {@link PreParser} and attach them
     * to either the type declaration itself (model methods, class invariants, ...) or their
     * (directly) subsequent callable declaration (method contracts).
     *
     * @param td the given type declaration (typically a class declaration)
     * @throws SLTranslationException
     */
    private void transformClassLevelComments(TypeDeclaration<?> td) throws SLTranslationException {
        URI fileName = td.findCompilationUnit().flatMap(CompilationUnit::getStorage)
                .map(it -> it.getPath().toUri())
                .orElse(null);

        ArrayList<BodyDeclaration<?>> members = new ArrayList<>(td.getMembers());
        ArrayList<TextualJMLSpecCase> specCases = new ArrayList<>();
        TextualJMLModifierList jmlModifiers = null;

        for (BodyDeclaration<?> member : members) {
            // JMLDocsBodyDeclaration: JML comments inside a class/interface/... body
            if (member instanceof JmlDocsBodyDeclaration bd) {
                String concatenatedComment = sanitizer.asString(bd.jmlDocs());

                // The preparser split along the grammar rules in KeYParser.g4, and gives you a list
                // of JML entities.
                PreParser pp = getPreParser();
                // We might have multiple textual constructs now, because the single comment could
                // contain multiple JML entities (e.g. method contract and ghost field declaration)

                de.uka.ilkd.key.java.Position pos =
                    de.uka.ilkd.key.java.Position.fromOneZeroBased(1, 0);
                ImmutableList<TextualJMLConstruct> constructs =
                    pp.parseClassLevel(concatenatedComment, fileName, pos);
                services.addWarnings(pp.getWarnings());

                // handle model and ghost declarations in textual constructs
                for (TextualJMLConstruct c : constructs) {
                    if (c instanceof TextualJMLFieldDecl fd) {
                        // ghost/model field decl.: transform into "real" field decl.
                        td.addMember(transformClassFieldDecl(fd));
                    } else if (c instanceof TextualJMLMethodDecl md) {
                        // model method decl.:
                        final MethodDeclaration decl = transformMethodDecl(md, jmlModifiers);
                        jmlModifiers = null; // these are used now
                        // attach all specification cases accumulated so far
                        for (TextualJMLSpecCase specCase : specCases) {
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
                        // accumulate spec cases (these are model method contracts) to attach them
                        // in a later loop iteration to the model method declaration
                        specCases.add(specCase);
                    } else if (c instanceof TextualJMLModifierList newModifiers) {
                        if (jmlModifiers != null) {
                            throw new SLTranslationException("There seems to be more than one set of dangling modifiers",
                                    c.getLocation());
                        }
                        jmlModifiers = newModifiers;
                    } else {
                        String errorMessage = switch (c) {
                            case TextualJMLSetStatement a ->
                                    "A set assignment only allowed inside of a method body";
                            case TextualJMLMergePointDecl a ->
                                    "Merge points are only allowed inside of a method body";
                            case TextualJMLLoopSpec a ->
                                    "Loop specifications are only allowed inside of a method body or initializers";
                            case TextualJMLAssertStatement a ->
                                    "Assert statements are only allowed inside of a method body or initializers";
                            default -> "Unknown subclass of TextualJMLSpecCase: " + c.getClass();
                        };
                        throw new ConvertException(errorMessage, c.getLocation());
                    }
                }
            } else if (jmlModifiers != null) {
                // Attach any dangling modifiers from the preceding JML comment to the current node.
                if (member instanceof NodeWithModifiers<?> hasMods) {
                    for (var jmlMod : jmlModifiers.getModifiers()) {
                        hasMods.addModifier(jmlMod.getParserKeyword());
                    }
                } else {
                    throw new SLTranslationException(
                        "Modifiers before node that cannot have modifiers: " + member.getClass(),
                        jmlModifiers.getLocation());
                }
                jmlModifiers = null;
            }

            // add specifications to (Java) method and constructor declarations
            if (member instanceof CallableDeclaration<?> c) {
                for (var specCase : specCases) {
                    addSpec(c, specCase);
                }
                specCases.clear();
            }

            // on methods, constructor, ... also process the parameters.
            if(member instanceof NodeWithParameters<?> nwp) {
                NodeList<Parameter> params = nwp.getParameters();
                for (var param : params) {
                    transformModifiers(param);
                }
            }
        }


        for (BodyDeclaration<?> member : td.members()) {
            // attach anything that should be inside a method
            if (member instanceof NodeWithOptionalBlockStmt<?> call
                    && call.getBody().isPresent()) {
                transformMethodLevelCommentsAt(call.getBody().get(), fileName);
            }

            // modifiers (such as pure, spec_public, model, ghost, ...)
            if (member instanceof NodeWithModifiers<?> hasMods) {
                transformModifiers(hasMods);
            }

            if (member instanceof TypeDeclaration<?> inner) {
                transformClassLevelComments(inner);
            }
        }
    }

    private static @NonNull PreParser getPreParser() {
        return new PreParser();
    }

    private void addClassSpec(TypeDeclaration<?> td, TextualJMLConstruct c) {
        if (!td.containsData(KEY_CLASS_SPEC)) {
            td.setData(KEY_CLASS_SPEC, new ArrayList<>(4));
        }
        List<TextualJMLConstruct> specList = td.getData(KEY_CLASS_SPEC);
        specList.add(c);
    }

    private void addSpec(Node nextMember, TextualJMLConstruct specCase) {
        if (!nextMember.containsData(KEY_SPEC_CASE)) {
            nextMember.setData(KEY_SPEC_CASE, new ArrayList<>(4));
        }
        List<TextualJMLConstruct> specList = nextMember.getData(KEY_SPEC_CASE);
        specList.add(specCase);
    }

    private void addLoopSpec(Node nextMember, TextualJMLLoopSpec spec) {
        if (!nextMember.containsData(KEY_LOOP_SPEC)) {
            nextMember.setData(KEY_LOOP_SPEC, new ArrayList<>(4));
        }
        List<TextualJMLLoopSpec> specList = nextMember.getData(KEY_LOOP_SPEC);
        specList.add(spec);
    }

    private void transformMethodLevelCommentsAt(BlockStmt blockStmt, URI fileName)
            throws SLTranslationException {
        PreParser io = getPreParser();
        var stmts = new ArrayList<>(blockStmt.getStatements());
        var newStmts = new ArrayList<Statement>(blockStmt.getStatements().size() * 2);

        final de.uka.ilkd.key.java.Position pos =
            de.uka.ilkd.key.java.Position.fromOneZeroBased(1, 0);

        for (int i = 0; i < stmts.size(); i++) {
            var stmt = stmts.get(i);
            newStmts.add(stmt);

            while(stmt instanceof LabeledStmt labeledStmt) {
                var inner = labeledStmt.getStatement();

                if(inner instanceof JmlDocsStatements) {
                    throw new SLTranslationException(("Here is something wrong. Your label '%s' is glued to a " +
                            "JML annotation instead of a Java statement. Please consider the use of braces")
                            .formatted(labeledStmt.getLabel()),
                            Location.fromNode(inner));
                }
                // go into the labled statement
                stmt =  inner;
                // and treat it like a regular statement. Especially, that means
                // the processing go into labled blocks `l:{}`, labled ifs `l:if(){}` or labled loops.
                // It can not be a JML annotation statement by the exception above;
            }


            if (stmt instanceof BlockStmt bs) {
                transformMethodLevelCommentsAt(bs, fileName);
            } else if (stmt instanceof IfStmt is) {
                if (is.thenStmt().isBlockStmt()) {
                    transformMethodLevelCommentsAt(is.thenStmt().asBlockStmt(), fileName);
                }
                if (is.elseStmt() != null && is.elseStmt().isBlockStmt()) {
                    transformMethodLevelCommentsAt(is.elseStmt().asBlockStmt(), fileName);
                }
            } else if (stmt instanceof NodeWithBody<?> b && b.getBody().isBlockStmt()) {
                transformMethodLevelCommentsAt(b.getBody().asBlockStmt(), fileName);
            } else if (stmt instanceof JmlDocsStatements doc) {
                String concat = sanitizer.asString(doc.getJmlDocs());
                ImmutableList<TextualJMLConstruct> constructs =
                    io.parseMethodLevel(concat, fileName, pos);
                services.addWarnings(io.getWarnings());

                // handle ghost declarations and set assignments in textual constructs
                for (TextualJMLConstruct c : constructs) {
                    Statement statement;
                    switch (c) {
                        // local ghost variable declaration!
                        case TextualJMLFieldDecl field -> statement = transformVariableDecl(field);
                        case TextualJMLSetStatement set -> statement = transformSetStatement(set);
                        case TextualJMLMergePointDecl mergePointDecl ->
                            statement = transformMergePointDecl(mergePointDecl);
                        case TextualJMLAssertStatement assertStatement ->
                            statement = transformAssertStatement(assertStatement);
                        case TextualJMLSpecCase spec -> {
                            var specifiedStmt = stmts.get(i + 1);
                            if (specifiedStmt instanceof BlockStmt
                                    || specifiedStmt instanceof NodeWithBody<?> /* aka loops */
                                    || specifiedStmt instanceof LabeledStmt) {
                                addSpec(specifiedStmt, spec);
                                continue;
                            } else {
                                throw new IllegalStateException(
                                    "Could not find a suitable statement for the specification in body of "
                                        + blockStmt.getRange().get().begin + " for contracts "
                                        + spec);
                            }
                        }
                        case TextualJMLLoopSpec spec -> {
                            var specifiedStmt = stmts.get(i + 1);
                            // go into labled statements
                            while(specifiedStmt instanceof LabeledStmt labeledStmt) {
                                specifiedStmt = labeledStmt.getStatement();
                            }
                            if (specifiedStmt instanceof BlockStmt
                                    || specifiedStmt instanceof NodeWithBody<?> /* aka loops */
                                    || specifiedStmt instanceof LabeledStmt) {
                                addLoopSpec(specifiedStmt, spec);
                                continue;
                            } else {
                                throw new IllegalStateException(
                                    "Could not find a suitable statement for the specification in body of "
                                        + blockStmt.getRange().get().begin + " for contracts "
                                        + spec);
                            }
                        }
                        default -> {
                            LOGGER.error("{}: Jml element unhandled: {}", c.getLocation(),
                                c.getClass());
                            continue;
                        }
                    }

                    if (statement != null) {
                        newStmts.add(statement);
                    }
                }
            }

        }

        blockStmt.getStatements().clear();
        blockStmt.getStatements().addAll(newStmts);
    }

    @Override
    public void apply(@NonNull CompilationUnit cu) {
        // abort if JML is disabled
        if (!ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().isUseJML()) {
            return;
        }

        try {
            URI resource = cu.getStorage()
                    .map(it -> it.getPath().toUri())
                    .orElse(null);

            // iterate through all classes/interfaces/... in this compilation unit
            final var types = new ArrayList<>(cu.getTypes());
            ImmutableList<JMLModifier> modifiers = null;
            for (TypeDeclaration<?> td : types) {
                if (td instanceof JmlDocsTypeDeclaration jdtd) {
                    // Currently, we only support modifier at type declaration level.
                    // Other things would be ghost classes or model imports.
                    var input = sanitizer.asString(jdtd.jmlDocs());
                    PreParser pp = getPreParser();
                    modifiers = pp.parseModifiers(input);
                } else {
                    if (modifiers != null && !modifiers.isEmpty()) {
                        for (var jmlMod : modifiers) {
                            td.addModifier(jmlMod.getParserKeyword());
                        }
                        modifiers = null;
                    }
                    transformModifiers(td);
                    /*
                     * attach anything that should be directly inside classes (e.g. method
                     * contracts,
                     * model methods, class invariants, ghost field declarations, ...).
                     */
                    transformClassLevelComments(td);
                }
            }
        } catch (SLTranslationException e) {
            // Wrap the exception into a runtime exception because recoder does
            // not allow otherwise. It will be unwrapped later ...
            throw new RuntimeException(e);
        }
    }

    /**
     * Parse modifiers inside JML comments and attach them to the node as proper modifiers
     * (modifiers are registered in JavaParser fork already).
     *
     * @param hasMods the node the modifiers should be attached to
     */
    private void transformModifiers(NodeWithModifiers<?> hasMods) {
        PreParser pp = getPreParser();
        services.addWarnings(pp.getWarnings());

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
        if (jmlDocs.isEmpty())
            return "";
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
        if (jmlDocs.isEmpty())
            return "";
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
                    if (!Character.isWhitespace(s.charAt(pos)))
                        break;
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
        if (posAt < 0)
            return false;
        for (int i = pos + 2; i < posAt; i++) {
            int point = s.charAt(i);
            if (!(Character.isJavaIdentifierPart(point) || point == '-' || point == '+')) {
                return false;
            }
        }
        // unconditional JML comment
        if (pos + 2 == posAt)
            return true;
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
        // a JML annotation with an enabled negative-key is ignored (even if there are enabled
        // positive-keys).
        boolean enabledNegativeKeyFound = false;
        for (String marker : keys) {
            if (marker.isEmpty())
                continue;
            plusKeyFound = plusKeyFound || isPositive(marker);
            enabledPlusKeyFound =
                enabledPlusKeyFound || isPositive(marker) && isEnabled(activeKeys, marker);
            enabledNegativeKeyFound =
                enabledNegativeKeyFound || isNegative(marker) && isEnabled(activeKeys, marker);
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
