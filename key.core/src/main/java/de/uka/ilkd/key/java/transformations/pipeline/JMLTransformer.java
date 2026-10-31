/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.transformations.pipeline;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.speclang.jml.pretranslation.JMLModifier;
import de.uka.ilkd.key.speclang.njml.JmlFacade;
import de.uka.ilkd.key.speclang.njml.JmlParser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.DataKey;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.CallableDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.jml.body.JmlClassLevelDeclaration;
import com.github.javaparser.ast.jml.body.JmlFieldDeclaration;
import com.github.javaparser.ast.jml.body.JmlMethodDeclaration;
import com.github.javaparser.ast.jml.doc.JmlDoc;
import com.github.javaparser.ast.jml.doc.JmlDocStmt;
import com.github.javaparser.ast.jml.stmt.JmlExpressionStmt;
import com.github.javaparser.ast.jml.stmt.JmlExpressionStmt.JmlStmtKind;
import com.github.javaparser.ast.jml.stmt.JmlGhostStmt;
import com.github.javaparser.ast.key.KeyLoopScopeBlockStmt;
import com.github.javaparser.ast.key.KeyMergePointStmt;
import com.github.javaparser.ast.nodeTypes.NodeWithBody;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.LabeledStmt;
import com.github.javaparser.ast.stmt.Statement;
import org.antlr.v4.runtime.ParserRuleContext;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static de.uka.ilkd.key.java.transformations.MarkerStatementHelper.KEY_ASSERT;
import static de.uka.ilkd.key.java.transformations.MarkerStatementHelper.KEY_ASSIGN;
import static de.uka.ilkd.key.java.transformations.MarkerStatementHelper.KEY_JML_FALLBACK;
import static de.uka.ilkd.key.java.transformations.MarkerStatementHelper.KEY_MERGE_POINT;

/// JMLTransformer translates the JML annotation comments into the JML AST that is attached to
/// the Java AST nodes.
///
/// The actual JML parsing is done by JMLtk (see `JmlProcessor`): class-level contracts and
/// declarations, method-level statements (assert/assume/set, ghost variables) and loop
/// specifications are attached to the corresponding Java AST nodes directly. This transformer
/// only needs to
///
/// * re-process the bodies of (model) methods for method level JML statements,
/// * self-mark JML statements (`JmlExpressionStmt`, `KeyMergePointStmt`, `JmlGhostStmt`)
/// so that the [de.uka.ilkd.key.java.loader.JP2KeYConverter] can recognize them.
///
/// The JMLtk wrapper declarations (`JmlMethodDeclaration`, `JmlFieldDeclaration`) and the class
/// level specifications (`JmlClassExprDeclaration`, `JmlRepresentsDeclaration`,
/// `JmlClassAccessibleDeclaration`) stay in the JMLtk type: the
/// [de.uka.ilkd.key.java.loader.JP2KeYConverter] converts the contained Java declarations and
/// the [de.uka.ilkd.key.speclang.jml.JMLSpecExtractor] reads the specifications directly from
/// the JMLtk AST via `KeYJPMapping`.
///
/// The removal of the raw `JmlDoc*` nodes is left to [JmlDocRemoval].
///
/// @author weigl
/// @author drodt
/// @author lanzinger
/// @author bubel
/// @author pfeifer
/// @author ulbrich
public final class JMLTransformer extends JavaTransformerAbstract {

    private static final Logger LOGGER = LoggerFactory.getLogger(JMLTransformer.class);

    /**
     * Java modifiers that can appear in a textual JML model method declaration.
     */
    public static final EnumSet<JMLModifier> JAVA_MODS =
        EnumSet.of(JMLModifier.ABSTRACT, JMLModifier.FINAL, JMLModifier.PRIVATE,
            JMLModifier.PROTECTED, JMLModifier.PUBLIC, JMLModifier.STATIC);

    /**
     * Data key for the {@link JmlMethodDeclaration}/{@link JmlFieldDeclaration} wrapper that the
     * pipeline unwraps from a (model) method or (ghost/model) field. The wrapper remains the
     * carrier of the parsed JML specification (contract, method definition); it is remembered
     * on the contained declaration so that the converter can register the reverse mapping and
     * the {@code JMLSpecExtractor} can read the specification back via {@code KeYJPMapping}.
     */
    public static final DataKey<JmlClassLevelDeclaration<?>> KEY_JML_WRAPPER = new DataKey<>() {
    };

    /**
     * Class level "field-like" JML clauses that JMLtk represents as {@link JmlFieldDeclaration}
     * whose inner {@code FieldDeclaration} carries the keyword as a bogus type. The datagroup
     * family is not supported by KeY; unwrapping it would silently install a spurious field, so
     * these are rejected loudly. {@code repr} is the historical shorthand of
     * {@code represents}-style declarations and likewise must not become a field.
     */
    private static final Set<String> DATAGROUP_FAMILY = Set.of(
        "datagroup", "in_group", "maps_into", "monitors_for",
        "readable_if", "writable_if", "mapped_by", "repr");

    /**
     * Legacy, deprecated class level clauses that are accepted as drops ("deprecated crap").
     * They are removed without leaving a spurious field behind and without a guard.
     */
    private static final Set<String> LEGACY_DROPPED_TAGS = Set.of(
        "captures", "duration", "working_space");

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

    @Override
    public void apply(@NonNull CompilationUnit cu) {
        // abort if JML is disabled
        if (!ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().isUseJML()) {
            return;
        }

        try {
            for (TypeDeclaration<?> td : new ArrayList<>(cu.getTypes())) {
                transformType(td);
            }
        } catch (RuntimeException e) {
            // Wrap the exception into a runtime exception because recoder does
            // not allow otherwise. It will be unwrapped later ...
            throw e;
        }
    }

    /**
     * Transform all class level JML constructs of the given type declaration. JMLtk already
     * attached the parsed JML to the Java AST: contracts sit on {@code NodeWithContracts} nodes,
     * model/ghost methods and fields are wrapped in {@code JmlMethodDeclaration}/
     * {@code JmlFieldDeclaration} wrappers, and class level specifications are
     * {@code JmlClassExprDeclaration}/{@code JmlRepresentsDeclaration}/
     * {@code JmlClassAccessibleDeclaration} members of the type.
     * <p>
     * The wrapper declarations are unwrapped into their contained real declarations so that the
     * Java symbol solver sees the (model) methods and (ghost/model) fields again — Javaparser's
     * resolution ignores nodes that are not direct {@code MethodDeclaration}/
     * {@code FieldDeclaration} members. The wrapper is remembered on the contained declaration
     * via {@link #KEY_JML_WRAPPER}; the
     * {@link de.uka.ilkd.key.java.loader.JP2KeYConverter} registers it as the reverse mapping
     * target of the resulting KeY declaration and the
     * {@link de.uka.ilkd.key.speclang.jml.JMLSpecExtractor} reads the specifications from it via
     * {@code KeYJPMapping}. Class level specifications stay on the JMLtk type.
     *
     * @param td the given type declaration (typically a class declaration)
     */
    private void transformType(TypeDeclaration<?> td) {
        for (BodyDeclaration<?> member : new ArrayList<>(td.getMembers())) {
            switch (member) {
                // The JMLtk wrapper for a (model) method declaration: contains the "real"
                // method declaration plus the contract (wrapper.getContract()). Unwrap it and
                // remember the wrapper, which remains the carrier of the specification.
                case JmlMethodDeclaration methodDecl -> {
                    var method = methodDecl.getMethodDeclaration();
                    method.setData(KEY_JML_WRAPPER, methodDecl);
                    transformCallableBody(method);
                    replaceMember(td, methodDecl, method);
                }
                // Ghost/model field declarations: unwrap and remember the wrapper.
                //
                // JMLtk also models the class level "field-like" clauses (datagroup family and
                // the legacy captures/duration/working_space) as JmlFieldDeclaration with the
                // keyword as a bogus type. None of them is a field; unwrapping would turn them
                // into spurious Java fields. The datagroup family is rejected loudly, the
                // legacy clauses are accepted drops.
                case JmlFieldDeclaration fieldDecl -> {
                    String tag = fieldDecl.getDecl().getVariables().isEmpty() ? ""
                            : fieldDecl.getDecl().getVariables().get(0).getType().asString();
                    if (DATAGROUP_FAMILY.contains(tag)) {
                        throw new IllegalArgumentException(
                            "JML '" + tag + "' clauses (datagroup family) are not supported by "
                                + "KeY and must not silently become spurious fields; remove or "
                                + "migrate the clause"
                                + fieldDecl.getRange().map(r -> " at line " + r.begin.line)
                                        .orElse(""));
                    }
                    if (LEGACY_DROPPED_TAGS.contains(tag)) {
                        // Accepted drops: deprecated legacy clauses without a KeY counterpart.
                        LOGGER.debug("Dropping legacy JML '{}' clause{}", tag,
                            fieldDecl.getRange().map(r -> " at line " + r.begin.line)
                                    .orElse(""));
                        fieldDecl.remove();
                    } else {
                        var decl = fieldDecl.getDecl();
                        decl.setData(KEY_JML_WRAPPER, fieldDecl);
                        replaceMember(td, fieldDecl, decl);
                    }
                }
                // Class level specifications: invariants, initially clauses, axioms,
                // represents clauses and accessible-clauses. They stay on the JMLtk type and
                // are read by the JMLSpecExtractor. Since the JmlMethodDeclaration and
                // JmlFieldDeclaration arms above come first, this catches exactly
                // JmlClassExprDeclaration, JmlRepresentsDeclaration and
                // JmlClassAccessibleDeclaration.
                case JmlClassLevelDeclaration<?> ignored -> {
                }
                // Regular Java declarations with attached JML contracts
                case CallableDeclaration<?> callable -> transformCallableBody(callable);
                case TypeDeclaration<?> inner -> transformType(inner);
                case InitializerDeclaration init -> transformMethodLevelCommentsAt(init.getBody());
                default -> {
                    // Fields, enums, records: JML is handled by JmlProcessor already
                }
            }
        }
    }

    /**
     * Replaces the given wrapper member by the contained declaration within {@code td}.
     */
    private static void replaceMember(TypeDeclaration<?> td, BodyDeclaration<?> oldMember,
            BodyDeclaration<?> newMember) {
        if (!td.replace(oldMember, newMember)) {
            LOGGER.error("Could not replace JML declaration wrapper {} in {}",
                oldMember.getClass().getSimpleName(), td.getNameAsString());
        }
    }

    private void transformCallableBody(CallableDeclaration<?> callable) {
        if (callable instanceof MethodDeclaration method) {
            method.getBody().ifPresent(this::transformMethodLevelCommentsAt);
        } else if (callable instanceof ConstructorDeclaration constructor) {
            constructor.getBody().ifPresent(this::transformMethodLevelCommentsAt);
        }
    }

    /**
     * Processes the statements of the given block. JMLtk already attached method level JML
     * constructs: contracts (loop invariants and loop contracts) were attached to the following
     * statement, assert/assume/set statements and ghost variables were inserted as statements.
     * Here we only self-mark these nodes so that the
     * {@link de.uka.ilkd.key.java.loader.JP2KeYConverter} can translate them.
     *
     * @param block the given block
     */
    private void transformMethodLevelCommentsAt(BlockStmt block) {
        for (Statement stmt : new ArrayList<>(block.getStatements())) {
            // JMLtk attaches contracts to the innermost statement after a JML comment,
            // ignoring labels.
            var inner = unwrapLabels(stmt);
            if (inner instanceof BlockStmt bs) {
                transformMethodLevelCommentsAt(bs);
            } else if (inner instanceof IfStmt ifStmt) {
                transformIf(ifStmt);
            } else if (inner instanceof NodeWithBody<?> nodeWithBody) {
                if (nodeWithBody.getBody().isBlockStmt()) {
                    transformMethodLevelCommentsAt(nodeWithBody.getBody().asBlockStmt());
                }
            } else if (inner instanceof JmlGhostStmt ghost) {
                // Ghost local variable: unwrap the statement and mark the declared
                // variables as ghost.
                Statement ghostStatement = ghost.getStatement();
                ghostStatement.findAll(VariableDeclarationExpr.class)
                        .forEach(var -> var.addModifier(Modifier.DefaultKeyword.JML_GHOST));
                ghost.replace(ghostStatement);
            } else if (inner instanceof JmlExpressionStmt expr) {
                markExpressionStatement(expr);
            } else if (inner instanceof KeyMergePointStmt mergePoint) {
                mergePoint.setData(KEY_MERGE_POINT, mergePoint);
            } else if (inner instanceof JmlDocStmt docStmt) {
                transformFallbackJmlDocStmt(block, stmt, docStmt);
            }
        }
    }

    /**
     * Re-parses a leftover raw JML comment block ({@link JmlDocStmt}) that JMLtk could not turn
     * into typed JML AST nodes with KeY's own JML grammar and marks the successfully parsed
     * statement elements for the {@link de.uka.ilkd.key.java.loader.JP2KeYConverter} via
     * {@link MarkerStatementHelper#KEY_JML_FALLBACK}.
     * <p>
     * JMLtk groups adjacent JML comments into one {@code JmlDocStmt} and converts them
     * all-or-nothing: if every statement of the group could be parsed, the converted statements
     * are emitted as following siblings whose source range lies inside the group's range and the
     * {@code JmlDocStmt} is pure duplication; if any statement fails, nothing is converted and
     * the group's comments all remain in the {@code JmlDocStmt}. Groups of the first kind are
     * left untouched (and removed by {@link JmlDocRemoval}). Groups of the second kind are
     * re-parsed here: their comments are re-lexed against KeY's own grammar (adjacent lines like
     * {@code //@ merge_point} + {@code //@ merge_proc "X";} form a single statement) and the
     * group is split into one {@code JmlDocStmt} per supported statement element, each marked
     * with its parse tree. Elements JMLtk would have converted anyway ({@code set},
     * {@code assert}/{@code assume} without a proof script) are kept since JMLtk did not convert
     * them in a failing group. Statements JMLtk and KeY's grammar both cannot handle stay
     * unmarked and are dropped by {@link JmlDocRemoval}, as before.
     *
     * @param block the block containing the leftover comment
     * @param stmt the leftover statement itself (possibly wrapped in labels)
     * @param docStmt the leftover raw comment block
     */
    private static void transformFallbackJmlDocStmt(BlockStmt block, Statement stmt,
            JmlDocStmt docStmt) {
        NodeList<Statement> stmts = block.getStatements();
        int idx = stmts.indexOf(stmt);
        if (idx < 0) {
            return;
        }
        // Skip leftover duplication of a group JMLtk already converted: a converted JML
        // statement that follows the leftover and lies within its source range.
        var range = docStmt.getRange().orElse(null);
        if (range != null) {
            for (int i = idx + 1; i < stmts.size(); i++) {
                Statement s = stmts.get(i);
                if (isConvertedJmlStatement(s)
                        && s.getRange().map(range::overlapsWith).orElse(false)) {
                    return;
                }
            }
        }
        // Re-parse the raw comments with KeY's own JML grammar.
        List<ParserRuleContext> elements =
            parseFallbackElements(docStmt);
        if (elements.isEmpty()) {
            return;
        }
        // Split the leftover into one JmlDocStmt per parsed element so that the converter sees
        // exactly one statement per element, at the position of the original comment group.
        List<JmlDocStmt> replacements = new ArrayList<>(elements.size());
        for (var element : elements) {
            var single = new JmlDocStmt(new NodeList<>(new JmlDoc(element.getText())));
            docStmt.getRange().ifPresent(single::setRange);
            single.setData(KEY_JML_FALLBACK, element);
            replacements.add(single);
        }
        stmts.set(idx, replacements.get(0));
        for (int i = 1; i < replacements.size(); i++) {
            stmts.add(idx + i, replacements.get(i));
        }
    }

    /**
     * Re-parses the comments of the given leftover with KeY's JML grammar. The comments are
     * concatenated (adjacent {@code //@} lines form single statements, e.g. {@code merge_point}
     * + {@code merge_proc "X";}) and parsed as a whole; if that fails, every comment is parsed
     * individually and unparseable comments are dropped. Returns the supported statement
     * elements in source order.
     */
    private static List<ParserRuleContext> parseFallbackElements(
            JmlDocStmt docStmt) {
        StringBuilder joined = new StringBuilder();
        for (JmlDoc doc : docStmt.getJmlComments()) {
            String text = normalizeJmlDocContent(doc);
            if (!text.isBlank()) {
                joined.append(text).append('\n');
            }
        }
        if (joined.isEmpty()) {
            return List.of();
        }
        List<ParserRuleContext> elements =
            parseMethodlevelElements(joined.toString());
        if (!elements.isEmpty()) {
            return elements;
        }
        List<ParserRuleContext> result = new ArrayList<>();
        for (JmlDoc doc : docStmt.getJmlComments()) {
            String content = normalizeJmlDocContent(doc);
            if (!content.isBlank()) {
                result.addAll(parseMethodlevelElements(content));
            }
        }
        return result;
    }

    /**
     * Parses the given JML content as a method level comment with KeY's grammar and returns the
     * supported statement contexts in source order. Unsupported elements (e.g.
     * {@code loop_invariant} clauses) are skipped: they have no KeY statement counterpart here
     * and are dropped, as they were before this fallback existed.
     */
    private static List<ParserRuleContext> parseMethodlevelElements(String content) {
        try {
            var parser = JmlFacade.createParser(JmlFacade.createLexer(content));
            var ctx = parser.methodlevel_comment();
            parser.getErrorReporter().throwException();
            List<ParserRuleContext> elements = new ArrayList<>();
            for (var element : ctx.methodlevel_element()) {
                var sub = supportedFallbackElementOrNull(element);
                if (sub != null) {
                    elements.add(sub);
                }
            }
            return elements;
        } catch (RuntimeException e) {
            return List.of();
        }
    }

    /**
     * Returns the specific statement context of the given method level element if the fallback
     * can translate it into a KeY statement, {@code null} otherwise. The supported kinds are
     * exactly the constructs JMLtk leaves unparsed: KeY extension statements ({@code merge_point}
     * family) and statements with proof scripts or obtain clauses.
     */
    private static @Nullable ParserRuleContext supportedFallbackElementOrNull(
            JmlParser.Methodlevel_elementContext element) {
        var merge = element.merge_point_statement();
        if (merge != null) {
            return merge;
        }
        var set = element.set_statement();
        if (set != null) {
            return set;
        }
        var asrt = element.assert_statement();
        if (asrt != null) {
            return asrt;
        }
        var assume = element.assume_statement();
        if (assume != null) {
            return assume;
        }
        return null;
    }

    /**
     * Returns whether the given statement was produced by JMLtk's typed JML parsing (as opposed
     * to a plain Java statement or another leftover {@link JmlDocStmt}).
     */
    private static boolean isConvertedJmlStatement(Statement s) {
        if (s instanceof JmlDocStmt) {
            return false;
        }
        String pkg = s.getClass().getPackageName();
        return pkg.startsWith("com.github.javaparser.ast.jml.stmt")
                || s instanceof KeyMergePointStmt
                || s instanceof KeyLoopScopeBlockStmt;
    }

    /**
     * Strips the JML comment markers from the given raw comment content so that the remaining
     * text can be fed to KeY's JML grammar: a {@code /*@ ... *&#47;} block or {@code //@} lines.
     */
    private static String normalizeJmlDocContent(JmlDoc doc) {
        String content = doc.getContent().strip();
        if (content.startsWith("/*")) {
            int at = content.indexOf('@');
            if (at >= 0) {
                content = content.substring(at + 1);
            }
            if (content.endsWith("*/")) {
                content = content.substring(0, content.length() - 2);
            }
        }
        StringBuilder sb = new StringBuilder();
        for (String line : content.split("\n")) {
            String l = line.strip();
            if (l.startsWith("//")) {
                int at = l.indexOf('@');
                if (at >= 0) {
                    l = l.substring(at + 1).stripLeading();
                }
            } else if (l.startsWith("*") && !l.startsWith("*/")) {
                l = l.substring(1).stripLeading();
            }
            if (!l.isBlank()) {
                sb.append(l).append('\n');
            }
        }
        return sb.toString();
    }

    private void transformIf(IfStmt ifStmt) {
        if (ifStmt.getThenStmt().isBlockStmt()) {
            transformMethodLevelCommentsAt(ifStmt.getThenStmt().asBlockStmt());
        }
        Statement elseStmt = ifStmt.getElseStmt().orElse(null);
        if (elseStmt != null) {
            if (elseStmt.isBlockStmt()) {
                transformMethodLevelCommentsAt(elseStmt.asBlockStmt());
            } else if (elseStmt.isIfStmt()) {
                transformIf(elseStmt.asIfStmt());
            }
        }
    }

    private static Statement unwrapLabels(Statement stmt) {
        while (stmt instanceof LabeledStmt labeledStmt) {
            stmt = labeledStmt.getStatement();
        }
        return stmt;
    }

    /**
     * Self-marks the given JML statement: `set` statements as assignments, everything else
     * (assert, assume) as assertions.
     */
    private static void markExpressionStatement(JmlExpressionStmt expr) {
        if (expr.getKind() == JmlStmtKind.SET) {
            expr.setData(KEY_ASSIGN, expr);
        } else {
            expr.setData(KEY_ASSERT, expr);
        }
    }
}
