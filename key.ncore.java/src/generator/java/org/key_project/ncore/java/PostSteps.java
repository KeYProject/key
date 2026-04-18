/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.ncore.java;

import java.nio.file.Paths;
import java.util.List;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.modifiers.NodeWithPrivateModifier;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.utils.SourceRoot;
import de.uka.ilkd.key.java.ast.expression.Assignment;
import de.uka.ilkd.key.java.ast.expression.ExpressionStatement;

import static com.github.javaparser.ast.Modifier.DefaultKeyword.PUBLIC;
import static org.key_project.ncore.java.Generator.ROOT;

public class PostSteps {
    public static void createVisitor(List<CompilationUnit> nodeUnits, SourceRoot sourceRoot) {
        var cu = new CompilationUnit();
        String name = "org.key_project.key.java.ast.visitor";
        cu.setPackageDeclaration(name);
        cu.setStorage(ROOT.resolve("org/key_project/java/ast/visitor/Visitor.java"));
        System.out.println(cu.getStorage().get().getPath());

        var generic = new TypeParameter("R");

        var type = cu.addClass("Visitor");
        type.setInterface(true);
        type.addTypeParameter(generic.clone());

        for (CompilationUnit clazz : nodeUnits) {
            try {
                var t = clazz.getPrimaryType().get();
                if (!(t instanceof ClassOrInterfaceDeclaration c)) continue;
                if (c.isInterface()) continue;

                cu.addImport(t.getFullyQualifiedName().get());

                var m = type.addMethod("visit");
                m.addParameter(new ClassOrInterfaceType(null, t.getNameAsString()), "n");
                m.setType(generic.clone());
                m.setBody(null);

                var accept = t.addMethod("accept", PUBLIC);
                accept.setType(generic.clone());
                accept.getTypeParameters().add(generic.clone());
                accept.addParameter(new ClassOrInterfaceType(null, new SimpleName(type.getFullyQualifiedName().get()),
                                new NodeList<>(generic.clone())),
                        "visitor");
                accept.getBody().get()
                        .addStatement("return visitor.visit(this);");
            } catch (Exception e) {
                System.err.println(e.getMessage() + " :: " + clazz.getStorage().get().getPath());
            }
        }
        sourceRoot.add(cu);
    }

    public static void createVoidVisitor(List<CompilationUnit> nodeUnits, SourceRoot sourceRoot) {
        var cu = new CompilationUnit();
        String name = "org.key_project.key.java.ast.visitor";
        cu.setPackageDeclaration(name);
        cu.setStorage(ROOT.resolve("org/key_project/java/ast/visitor/VoidVisitor.java"));
        System.out.println(cu.getStorage().get().getPath());

        var type = cu.addClass("VoidVisitor");
        type.setInterface(true);

        for (CompilationUnit clazz : nodeUnits) {
            try {
                var t = clazz.getPrimaryType().get();
                if (!(t instanceof ClassOrInterfaceDeclaration c)) continue;
                if (c.isInterface()) continue;

                cu.addImport(t.getFullyQualifiedName().get());

                var m = type.addMethod("visit");
                m.addParameter(new ClassOrInterfaceType(null, t.getNameAsString()), "n");
                m.setBody(null);


                var accept = t.addMethod("accept", PUBLIC);
                accept.addParameter(new ClassOrInterfaceType(null, type.getFullyQualifiedName().get()),
                        "visitor");
                accept.getBody().get().addStatement("visitor.visit(this);");


            } catch (Exception e) {
                System.err.println(e.getMessage() + " :: " + clazz.getStorage().get().getPath());
            }
        }
        sourceRoot.add(cu);
    }

    public static void createTraversalVisitor(List<CompilationUnit> nodeUnits, SourceRoot sourceRoot) {
        var cu = new CompilationUnit();
        String name = "org.key_project.key.java.ast.visitor";
        cu.setPackageDeclaration(name);
        cu.setStorage(ROOT.resolve("org/key_project/java/ast/visitor/TraversalVisitor.java"));
        System.out.println(cu.getStorage().get().getPath());

        var type = cu.addClass("TraversalVisitor", PUBLIC,
                Modifier.DefaultKeyword.ABSTRACT);
        type.getImplementedTypes().add(
                (ClassOrInterfaceType) StaticJavaParser.parseType("Visitor<Node>"));

        for (CompilationUnit clazz : nodeUnits) {
            try {
                var t = clazz.getPrimaryType().get();
                cu.addImport(t.getFullyQualifiedName().get());

                if (!(t instanceof ClassOrInterfaceDeclaration c)) continue;
                if (c.isInterface()) continue;

                var m = type.addMethod("visit", PUBLIC);
                m.addParameter(new ClassOrInterfaceType(null, t.getNameAsString()), "n");
                m.addAnnotation(Override.class);
                BlockStmt body = m.getBody().get();
                body.addStatement("var b = n.builder();");
                t.getFields()
                        .stream().filter(NodeWithPrivateModifier::isPrivate)
                        .forEach(f ->
                                body.addStatement(
                                        "b.%s = (%s) accept(n.%s());"
                                        .formatted(f.getVariable(0).getNameAsExpression(),
                                                f.getVariable(0).getTypeAsString(),
                                                f.getVariable(0).getNameAsExpression())));
                body.addStatement("return b.build();");
                m.setType(new ClassOrInterfaceType(null, t.getFullyQualifiedName().get()));
            } catch (Exception e) {
                System.err.println(e.getMessage() + " :: " + clazz.getStorage().get().getPath());
            }
        }
        sourceRoot.add(cu);
    }


    public static void createDeepCopyVisitor(List<CompilationUnit> nodeUnits, SourceRoot sourceRoot) {

    }

    public interface PostStep {
        void applyOn(List<CompilationUnit> nodeUnits, SourceRoot sourceRoot);
    }


}
