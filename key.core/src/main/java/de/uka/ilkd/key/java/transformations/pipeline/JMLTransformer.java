/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.transformations.pipeline;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;

import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.speclang.jml.JmlSpec;
import de.uka.ilkd.key.speclang.jml.pretranslation.JMLModifier;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.DataKey;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.CallableDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.jml.NodeWithContracts;
import com.github.javaparser.ast.jml.body.JmlClassLevelDeclaration;
import com.github.javaparser.ast.jml.body.JmlFieldDeclaration;
import com.github.javaparser.ast.jml.body.JmlMethodDeclaration;
import com.github.javaparser.ast.jml.clauses.JmlContract;
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
import org.jspecify.annotations.Nullable;
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
/// * expose the attached JML as [JmlSpec] wrapped nodes via the data keys
/// [JMLTransformer#KEY_SPEC_CASE] (method/block/loop contracts) and
/// [JMLTransformer#KEY_CLASS_SPEC] (class level specifications such as invariants,
/// initially clauses, model field and model method declarations),
/// * replace the JMLtk wrapper declarations (`JmlMethodDeclaration`, `JmlFieldDeclaration`)
/// by the contained real declarations,
/// * self-mark JML statements (`JmlExpressionStmt`, `KeyMergePointStmt`, `JmlGhostStmt`)
/// so that the [de.uka.ilkd.key.java.loader.JP2KeYConverter] can recognize them.
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

    /// KEY for contracts
    public static final DataKey<List<JmlSpec>> KEY_SPEC_CASE = new DataKey<>() {
    };
    /// KEY for class level specification
    public static final DataKey<List<JmlSpec>> KEY_CLASS_SPEC = new DataKey<>() {
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
     * attached the parsed JML to the Java AST; here we only relocate it into the KeY
     * {@link DataKey}s and unwrap the JML wrapper declarations.
     *
     * @param td the given type declaration (typically a class declaration)
     */
    private void transformType(TypeDeclaration<?> td) {
        for (BodyDeclaration<?> member : new ArrayList<>(td.getMembers())) {
            switch (member) {
                // The JMLtk wrapper for a (model) method declaration: contain the "real" method
                // declaration plus a method definition. The contracts were already attached to
                // the inner method declaration.
                case JmlMethodDeclaration methodDecl -> {
                    var method = methodDecl.getMethodDeclaration();
                    // the model method definition itself is a specification
                    TransformationPipelineServices.addSpec(method, new JmlSpec(methodDecl));
                    moveContracts(method);
                    replaceMember(td, methodDecl, method);
                    transformCallableBody(method);
                }
                // Ghost/model field declarations
                case JmlFieldDeclaration fieldDecl -> {
                    replaceMember(td, fieldDecl, fieldDecl.getDecl());
                }
                // Class level specifications: invariants, initially clauses, axioms,
                // represents clauses and accessible-clauses. After the JmlMethodDeclaration and
                // JmlFieldDeclaration arms above, this catches exactly JmlClassExprDeclaration,
                // JmlRepresentsDeclaration and JmlClassAccessibleDeclaration.
                case JmlClassLevelDeclaration<?> classSpec -> {
                    TransformationPipelineServices.addClassSpec(td, new JmlSpec(member));
                    member.remove();
                }
                // Regular Java declarations with attached JML contracts
                case CallableDeclaration<?> callable -> {
                    moveContracts(callable);
                    transformCallableBody(callable);
                }
                case TypeDeclaration<?> inner -> transformType(inner);
                case InitializerDeclaration init -> transformMethodLevelCommentsAt(init.getBody());
                default -> {
                    // Fields, enums, records: JML is handled by JmlProcessor already
                }
            }
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
     * Replaces the given wrapper member by the contained declaration within {@code td}.
     */
    private static void replaceMember(TypeDeclaration<?> td, BodyDeclaration<?> oldMember,
            BodyDeclaration<?> newMember) {
        if (!td.replace(oldMember, newMember)) {
            LOGGER.error("Could not replace JML declaration wrapper {} in {}",
                oldMember.getClass().getSimpleName(), td.getNameAsString());
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
        moveContracts(block);
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
            } else if (inner instanceof NodeWithContracts<?> nodeWithContracts) {
                moveContracts(nodeWithContracts);
            }
        }
    }

    private void transformIf(IfStmt ifStmt) {
        if (ifStmt.getThenStmt().isBlockStmt()) {
            transformMethodLevelCommentsAt(ifStmt.getThenStmt().asBlockStmt());
        }
        @Nullable
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

    /**
     * Moves the contracts attached to a {@link NodeWithContracts} (methods, blocks, loops) into
     * the {@link #KEY_SPEC_CASE} data key so that the converter can attach them to the KeY AST.
     */
    private static void moveContracts(NodeWithContracts<?> node) {
        if (!node.getContracts().isEmpty()) {
            for (JmlContract contract : new ArrayList<>(node.getContracts())) {
                TransformationPipelineServices.addSpec((Node) node, new JmlSpec(contract));
            }
            node.setContracts(new NodeList<>());
        }
    }
}
