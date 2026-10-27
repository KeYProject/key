/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.transformations.pipeline;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.Set;

import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.speclang.jml.pretranslation.JMLModifier;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.DataKey;
import com.github.javaparser.ast.Modifier;
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
import com.github.javaparser.ast.jml.stmt.JmlExpressionStmt;
import com.github.javaparser.ast.jml.stmt.JmlExpressionStmt.JmlStmtKind;
import com.github.javaparser.ast.jml.stmt.JmlGhostStmt;
import com.github.javaparser.ast.key.KeyMergePointStmt;
import com.github.javaparser.ast.nodeTypes.NodeWithBody;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.LabeledStmt;
import com.github.javaparser.ast.stmt.Statement;
import org.jspecify.annotations.NonNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static de.uka.ilkd.key.java.transformations.MarkerStatementHelper.KEY_ASSERT;
import static de.uka.ilkd.key.java.transformations.MarkerStatementHelper.KEY_ASSIGN;
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
            }
        }
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
