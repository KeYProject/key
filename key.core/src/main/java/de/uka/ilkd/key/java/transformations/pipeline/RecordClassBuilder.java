/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.key.JmlDocModifier;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.type.Type;

import javax.annotation.processing.Generated;

import java.util.Arrays;
import java.util.List;
import java.util.Objects;

import static com.github.javaparser.ast.Modifier.DefaultKeyword.*;

/// This transformation is made to transform any found [RecordDeclaration] into a corresponding
/// [ClassOrInterfaceDeclaration].
///
/// @author weigl
/// @since 2026-03-11
public class RecordClassBuilder extends JavaTransformer {
    public RecordClassBuilder(TransformationPipelineServices pipelineServices) {
        super(pipelineServices);
    }

    @Override
    public void apply(CompilationUnit cu) {
        cu.walk(RecordDeclaration.class, it -> {
            ClassOrInterfaceDeclaration clazz = transform(it);
            it.replace(clazz);
        });
    }

    private ClassOrInterfaceDeclaration transform(RecordDeclaration recordDeclaration) {
        ClassOrInterfaceDeclaration clazz = new ClassOrInterfaceDeclaration();
        clazz.setModifiers(recordDeclaration.getModifiers());
        clazz.addModifier(FINAL);
        clazz.setName(recordDeclaration.getName());

        clazz.addExtendedType(java.lang.Record.class);

        clazz.addAnnotation(Generated.class);

        for (Parameter parameter : recordDeclaration.getParameters()) {
            FieldDeclaration field = clazz.addField(parameter.type(), parameter.getNameAsString(), PRIVATE, FINAL);
            field.getModifiers().addAll(parameter.getModifiers());

            MethodDeclaration getter = clazz.addMethod(parameter.getNameAsString());
            getter.setType(parameter.type());
            getter.addModifier(PUBLIC, FINAL);
            for(var mod : parameter.getModifiers()) {
              if(mod.getKeyword() instanceof JmlDocModifier) {
                  getter.getModifiers().add(mod.clone());
              }
            }
            getter.getBody().get().addStatement(new ReturnStmt(parameter.getNameAsExpression()));
        }

        // TODO generate equals and hashcode
        boolean hasNoEquals = recordDeclaration.getMethodsBySignature("equals", "java.lang.Object").isEmpty();
        boolean hasNoHashcode = recordDeclaration.getMethodsBySignature("hashCode").isEmpty();

        if (hasNoEquals) {
            MethodDeclaration equals = clazz.addMethod("hashCode", PUBLIC, FINAL);
            equals.addAnnotation(Override.class);
            equals.setType(Boolean.TYPE);
            Type tObject = StaticJavaParser.parseType("java.lang.Object");
            equals.getParameters().add(new Parameter(tObject, "o"));
            BlockStmt body = equals.getBody().get();
            body.addStatement(services.parseStatement("if(this == o) return true;"));
            body.addStatement(services.parseStatement("if(!(o instanceof %s that)) return false;".formatted(clazz.getNameAsString())));

            Expression equalFields = recordDeclaration.getParameters().stream()
                    .map(it -> callObjects("equals", it.getNameAsExpression(),
                            new FieldAccessExpr(new NameExpr("that"), it.getNameAsString())))
                    .reduce((a, b) -> new BinaryExpr(a, b, BinaryExpr.Operator.AND))
                    .orElse(new BooleanLiteralExpr(true));
            body.addStatement(new ReturnStmt(equalFields));

            body.addStatement(new ReturnStmt(new BooleanLiteralExpr(true)));
        }

        if (hasNoHashcode) {
            MethodDeclaration hashCode = clazz.addMethod("hashCode", PUBLIC, FINAL);
            hashCode.addAnnotation(Override.class);
            hashCode.setType(Integer.TYPE);
            List<Expression> args = recordDeclaration.getParameters()
                    .stream().map(NodeWithSimpleName::getNameAsExpression)
                    .map(it -> (Expression) it)
                    .toList();
            final Expression call = callObjects("hash", args);
            hashCode.getBody().get()
                    .addStatement(new ReturnStmt(call));
        }

        // TODO generate toString
        boolean hasNoToString = recordDeclaration.getMethodsBySignature("toString").isEmpty();
        if (hasNoToString) {
            MethodDeclaration toString = clazz.addMethod("toString", PUBLIC, FINAL, JML_NON_NULL);
            toString.addAnnotation(Override.class);
            toString.setType(String.class);
            ConcatBuilder concatBuilder = new ConcatBuilder();
            concatBuilder.addStr(clazz.getNameAsString() + "[");
            for (Parameter parameter : recordDeclaration.getParameters()) {
                concatBuilder.addStr(parameter.getNameAsString() + "=");
                concatBuilder.addVar(parameter.getNameAsString());
                concatBuilder.addStr(",");
            }
            concatBuilder.addStr("]");
            toString.getBody().get().addStatement(new ReturnStmt(concatBuilder.expr));
        }


        clazz.getMembers().addAll(recordDeclaration.getMembers());
        return clazz;
    }

    private Expression callObjects(String method, Expression... exprs) {
        return callObjects(method, Arrays.stream(exprs).toList());
    }

    private Expression callObjects(String method, List<Expression> exprs) {
        var objects = new FieldAccessExpr(new FieldAccessExpr(new NameExpr("java"), "lang"), "Objects");
        return new MethodCallExpr(objects, method, new NodeList<>(exprs));
    }

    private static final class ConcatBuilder {
        public Expression expr = null;


        public ConcatBuilder addStr(String s) {
            return concat(new StringLiteralExpr(s));
        }

        private ConcatBuilder concat(com.github.javaparser.ast.expr.Expression expr) {
            if (this.expr == null) {
                this.expr = expr;
            } else {
                this.expr = new BinaryExpr(this.expr, expr, BinaryExpr.Operator.PLUS);
            }
            return this;
        }

        public ConcatBuilder addVar(String s) {
            return concat(new NameExpr(s));
        }
    }
}
