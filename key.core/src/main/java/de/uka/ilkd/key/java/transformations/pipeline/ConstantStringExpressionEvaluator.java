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

import java.util.Objects;

import de.uka.ilkd.key.java.transformations.ConstantExpressionEvaluator;
import de.uka.ilkd.key.java.transformations.EvaluationException;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.comments.MarkdownComment;
import com.github.javaparser.ast.comments.TraditionalJavadocComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.key.*;
import com.github.javaparser.ast.key.sv.*;
import com.github.javaparser.ast.modules.ModuleDeclaration;
import com.github.javaparser.ast.modules.ModuleExportsDirective;
import com.github.javaparser.ast.modules.ModuleOpensDirective;
import com.github.javaparser.ast.modules.ModuleProvidesDirective;
import com.github.javaparser.ast.modules.ModuleRequiresDirective;
import com.github.javaparser.ast.modules.ModuleUsesDirective;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

public class ConstantStringExpressionEvaluator extends JavaTransformer {

    public ConstantStringExpressionEvaluator(TransformationPipelineServices services) {
        super(services);
    }


    private void evaluateConstantStringExpressions(Node td) {
        td.accept(new ConstantStringEvaluator(), null);
    }

    @Override
    public void apply(TypeDeclaration<?> td) {
        evaluateConstantStringExpressions(td);
    }

    private class ConstantStringEvaluator extends VoidVisitorAdapter<Object> {
        public ConstantStringEvaluator() {
            super();
        }

        @Override
        public void visit(AnnotationDeclaration n, Object arg) {
            super.visit(n, arg);
        }

        @Override
        public void visit(AnnotationMemberDeclaration n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ArrayAccessExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ArrayCreationExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ArrayInitializerExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(AssertStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(AssignExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(BinaryExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(BlockComment n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(BlockStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(BooleanLiteralExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(BreakStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(CastExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(CatchClause n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(CharLiteralExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ClassExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ClassOrInterfaceDeclaration n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ClassOrInterfaceType n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(CompilationUnit n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ConditionalExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ConstructorDeclaration n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ContinueStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(DoStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(DoubleLiteralExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(EmptyStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(EnclosedExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(EnumConstantDeclaration n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(EnumDeclaration n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ExplicitConstructorInvocationStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ExpressionStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(FieldAccessExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(FieldDeclaration n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ForEachStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ForStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(IfStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(InitializerDeclaration n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(InstanceOfExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(IntegerLiteralExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(TraditionalJavadocComment n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(LabeledStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(LineComment n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(LongLiteralExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(MarkerAnnotationExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(MemberValuePair n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(MethodCallExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(MethodDeclaration n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(NameExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(NormalAnnotationExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(NullLiteralExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ObjectCreationExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(PackageDeclaration n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(Parameter n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(PrimitiveType n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(Name n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(SimpleName n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ArrayType n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ArrayCreationLevel n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(IntersectionType n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(UnionType n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ReturnStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(SingleMemberAnnotationExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(StringLiteralExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(SuperExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(SwitchEntry n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(SwitchStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(SynchronizedStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ThisExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ThrowStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(TryStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(LocalClassDeclarationStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(LocalRecordDeclarationStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(TypeParameter n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(UnaryExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(UnknownType n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(VariableDeclarationExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(VariableDeclarator n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(VoidType n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(WhileStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(WildcardType n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(LambdaExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(MethodReferenceExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(TypeExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(NodeList n, Object arg) {
            super.visit(n, arg);
            for (Object nodeObj : n) {
                if (nodeObj instanceof Node node) {
                    defaultAction(node, arg);
                }
            }
        }

        @Override
        public void visit(ImportDeclaration n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ModuleDeclaration n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ModuleRequiresDirective n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ModuleExportsDirective n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ModuleProvidesDirective n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ModuleUsesDirective n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ModuleOpensDirective n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(UnparsableStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(ReceiverParameter n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(VarType n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(Modifier n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(SwitchExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(TextBlockLiteralExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(YieldStmt n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(TypePatternExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(RecordDeclaration n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(CompactConstructorDeclaration n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyCcatchBreak n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyCcatchContinue n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyCcatchParameter n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyCcatchReturn n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyCatchAllStatement n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyEscapeExpression n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyExecStatement n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyExecutionContext n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyLoopScopeBlock n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyMergePointStatement n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyMethodBodyStatement n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyMethodCallStatement n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyMethodSignature n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyRangeExpression n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyTransactionStatement n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyContextStatementBlock n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyExecCtxtSV n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyExpressionSV n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyJumpLabelSV n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyMetaConstructExpression n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyMetaConstruct n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyMetaConstructType n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyMethodSignatureSV n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyPassiveExpression n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyProgramVariableSV n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyStatementSV n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyTypeSV n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyCcatchSV n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeyExecutionContextSV n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(RecordPatternExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(MatchAllPatternExpr n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(MarkdownComment n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(JmlDoc n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(JmlDocsBodyDeclaration n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(JmlDocsTypeDeclaration n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(JmlDocsStatements n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        @Override
        public void visit(KeYMarkerStatement n, Object arg) {
            super.visit(n, arg);
            defaultAction(n, arg);
        }

        public void defaultAction(Node n, Object arg) {
            if (n instanceof StringLiteralExpr || n instanceof BinaryExpr) {
                final Expression e = (Expression) n;
                ConstantExpressionEvaluator cee = services.getConstantEvaluator();
                try {
                    var expType = e.calculateResolvedType();
                    if (!e.isNullLiteralExpr() && expType != null
                            && expType.isReferenceType()
                            && Objects.equals(expType.asReferenceType().getQualifiedName(),
                                "java.lang.String")) {
                        try {
                            var expression = cee.evaluate(e);
                            if (e != expression) {
                                e.replace(expression);
                            }
                        } catch (EvaluationException t) {
                            //
                        }
                    }
                } catch (Throwable exc) {
                    // happens in taclets
                }
            }
        }
    }
}
