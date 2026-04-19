/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.ncore.java;

import java.util.List;
import java.util.stream.Collectors;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.modifiers.NodeWithPrivateModifier;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.utils.SourceRoot;

import static com.github.javaparser.ast.Modifier.DefaultKeyword.*;
import static org.key_project.ncore.java.Generator.ROOT;

public class PostSteps {
    public static void createVisitor(List<CompilationUnit> nodeUnits, SourceRoot sourceRoot) {
        var generic = new TypeParameter("R");

        var cu = new CompilationUnit();
        var type = createTypeAndSetDefaults(cu, "Visitor", PUBLIC);
        type.setInterface(true);
        type.addTypeParameter(generic.clone());

        for (CompilationUnit clazz : nodeUnits) {
            try {
                var t = clazz.getPrimaryType().get();
                if (!(t instanceof ClassOrInterfaceDeclaration c))
                    continue;
                if (c.isInterface())
                    continue;

                var m = type.addMethod("visit");
                m.addParameter(new ClassOrInterfaceType(null, t.getNameAsString()), "n");
                m.setType(generic.clone());
                m.setBody(null);

                var accept = t.addMethod("accept", PUBLIC);
                accept.setType(generic.clone());
                accept.getTypeParameters().add(generic.clone());
                accept.addParameter(
                    new ClassOrInterfaceType(null,
                        new SimpleName(type.getFullyQualifiedName().get()),
                        new NodeList<>(generic.clone())),
                    "visitor");
                accept.getBody().get()
                        .addStatement("return visitor.visit(this);");
            } catch (Exception e) {
                System.err.println(e.getMessage() + " :: " + clazz.getStorage().get().getPath());
            }
        }
        sourceRoot.add(cu);

        var s = StaticJavaParser.parseBlock("{return defaultVisit(n);}");
        var visitorWithDefaults = cu.clone();
        visitorWithDefaults.setStorage(
            ROOT.resolve("org/key_project/java/ast/visitor/VisitorWithDefaults.java"));
        final var vwdef = visitorWithDefaults.getType(0);
        vwdef.setName("VisitorWithDefaults");
        for (var method : vwdef.getMethods()) {
            method.addModifier(DEFAULT);
            method.setBody(s.clone());
        }
        visitorWithDefaults.addImport("org.key_project.java.ast.*");
        var m = vwdef.addMethod("defaultVisit");
        m.addParameter("JavaSourceElement", "n");
        m.setType(generic.clone());
        m.setBody(null);
        sourceRoot.add(visitorWithDefaults);
    }

    public static void createVoidVisitor(List<CompilationUnit> nodeUnits, SourceRoot sourceRoot) {
        var cu = new CompilationUnit();
        var type = createTypeAndSetDefaults(cu, "VoidVisitor", PUBLIC);
        type.setInterface(true);

        for (CompilationUnit clazz : nodeUnits) {
            try {
                var t = clazz.getPrimaryType().get();
                if (!(t instanceof ClassOrInterfaceDeclaration c))
                    continue;
                if (c.isInterface())
                    continue;

                var m = type.addMethod("visit");
                m.addParameter(new ClassOrInterfaceType(null, t.getNameAsString()), "n");
                m.setBody(null);


                var accept = t.addMethod("accept", PUBLIC);
                accept.addParameter(
                    new ClassOrInterfaceType(null, type.getFullyQualifiedName().get()),
                    "visitor");
                accept.getBody().get().addStatement("visitor.visit(this);");


            } catch (Exception e) {
                System.err.println(e.getMessage() + " :: " + clazz.getStorage().get().getPath());
            }
        }
        sourceRoot.add(cu);
    }

    public static void createTraversalVisitor(List<CompilationUnit> nodeUnits,
            SourceRoot sourceRoot) {
        var cu = new CompilationUnit();
        var type = createTypeAndSetDefaults(cu, "CopyVisitor", PUBLIC);
        type.getImplementedTypes().add(
            (ClassOrInterfaceType) StaticJavaParser.parseType("Visitor<JavaSourceElement>"));
        addAcceptMethods(type);

        for (CompilationUnit clazz : nodeUnits) {
            try {
                var t = clazz.getPrimaryType().get();

                if (!(t instanceof ClassOrInterfaceDeclaration c))
                    continue;
                if (c.isInterface())
                    continue;

                var m = type.addMethod("visit", PUBLIC);
                m.addParameter(new ClassOrInterfaceType(null, t.getNameAsString()), "n");
                m.addAnnotation(Override.class);
                BlockStmt body = m.getBody().get();
                body.addStatement("var b = n.builder();");
                t.getFields()
                        .stream().filter(NodeWithPrivateModifier::isPrivate)
                        .forEach(f -> body.addStatement(
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

    public static void createTraversalCopyOnDemandVisitor(List<CompilationUnit> nodeUnits,
            SourceRoot sourceRoot) {
        var cu = new CompilationUnit();
        var type = createTypeAndSetDefaults(cu, "CopyOnWriteVisitor", PUBLIC);

        type.getImplementedTypes().add(
            (ClassOrInterfaceType) StaticJavaParser.parseType("Visitor<JavaSourceElement>"));
        addAcceptMethods(type);


        for (CompilationUnit clazz : nodeUnits) {
            try {
                var t = clazz.getPrimaryType().get();

                if (!(t instanceof ClassOrInterfaceDeclaration c))
                    continue;
                if (c.isInterface())
                    continue;

                var m = type.addMethod("visit", PUBLIC);
                m.addParameter(new ClassOrInterfaceType(null, t.getNameAsString()), "n");
                m.addAnnotation(Override.class);
                BlockStmt body = m.getBody().get();
                body.addStatement("var b = n.builder();");
                t.getFields()
                        .stream()
                        .filter(NodeWithPrivateModifier::isPrivate)
                        .filter(PostSteps::isAstNode)
                        .forEach(f -> body.addStatement(
                            "b.%s = (%s) accept(n.%s());"
                                    .formatted(f.getVariable(0).getNameAsExpression(),
                                        f.getVariable(0).getTypeAsString(),
                                        f.getVariable(0).getNameAsExpression())));
                final var formatted = "boolean clean = %s;".formatted(
                    t.getFields().isEmpty() ? "false"
                            : t.getFields()
                                    .stream().filter(NodeWithPrivateModifier::isPrivate)
                                    .map(it -> {
                                        final var n = it.getVariable(0).getNameAsString();
                                        return "(n.%s() == b.%s)".formatted(n, n);
                                    })
                                    .collect(Collectors.joining("&&")));
                body.addStatement(formatted);
                body.addStatement("return clean?n:b.build();");
                m.setType(new ClassOrInterfaceType(null, t.getFullyQualifiedName().get()));
            } catch (Exception e) {
                System.err.println(e.getMessage() + " :: " + clazz.getStorage().get().getPath());
            }
        }
        sourceRoot.add(cu);
    }

    private static boolean isAstNode(FieldDeclaration field) {
        return isAstNode(field.getVariables().getFirst());
    }

    private static boolean isAstNode(VariableDeclarator v) {
        return isAstNode(v.getType());
    }

    private static boolean isAstNode(Type type) {
        if (type.isClassOrInterfaceType()) {
            var c = type.asClassOrInterfaceType();
            if (c.getNameAsString().equals("RoList")) {
                return isAstNode(c.getTypeArguments().get().getFirst());
            }

            final var name = c.getNameAsString();
            if (name.equals("String")) {
                return false;
            }
            try {
                c.toUnboxedType();
                return false;
            } catch (UnsupportedOperationException e) {
                return !(name.contains("Kind") || name.equals("PositionInfo")
                        || name.equals("JMLModifiers"));
            }
        }
        return false;
    }

    ///
    /// ```java
    /// <T extends Visitable> T accept(T n) {
    /// return n != null ? n.accept(this) : null;
    /// }
    /// <T extends Visitable> RoList<T> accept(RoList<T> n) {
    /// return n != null ? n.stream().map(it -> (T) it.accept(this)).toList() : null;
    /// }
    /// ```
    private static void addAcceptMethods(ClassOrInterfaceDeclaration type) {
        var t = StaticJavaParser.parseTypeParameter("T extends Visitable");
        var typeT = StaticJavaParser.parseType("T");

        {
            var accept = type.addMethod("accept", PROTECTED);
            accept.addTypeParameter(t);
            accept.addParameter(typeT, "n");
            accept.setType(typeT.clone());
            accept.getBody().get().addStatement("return n!=null?n.accept(this):null;");
        }

        {
            var acceptList = type.addMethod("accept", PROTECTED);
            acceptList.addTypeParameter(t.clone());
            acceptList.addParameter(StaticJavaParser.parseType("RoList<T>"), "n");
            acceptList.setType("RoList<T>");
            acceptList.getBody().get().addStatement(
                "return n != null ? n.stream().map(it -> (T) it.accept(this)).collect(RoList.collector()) : null;");
        }

        {
            var acceptList = type.addMethod("accept", PROTECTED);
            acceptList.addTypeParameter("T");
            acceptList.addParameter("T", "n");
            acceptList.setType("T");
            acceptList.getBody().get().addStatement("return n;");
        }
    }

    private static ClassOrInterfaceDeclaration createTypeAndSetDefaults(CompilationUnit cu,
            String typeName, Modifier.DefaultKeyword... mods) {
        String name = "org.key_project.java.ast.visitor";
        cu.setPackageDeclaration(name);
        cu.addImport("org.key_project.java.ast.visitor.*");
        cu.addImport("org.key_project.java.ast.*");
        cu.addImport("de.uka.ilkd.key.java.ast.PositionInfo");
        cu.addImport("org.key_project.util.collection.*");
        cu.setStorage(ROOT.resolve("org/key_project/java/ast/visitor/%s.java".formatted(typeName)));
        return cu.addClass(typeName, mods);
    }

    public static void createArgVisitor(List<CompilationUnit> nodeUnits, SourceRoot sourceRoot) {
        var cu = new CompilationUnit();
        var type = createTypeAndSetDefaults(cu, "ArgVisitor", PUBLIC);

        var generic = new TypeParameter("R");
        var argType = new TypeParameter("A");

        type.setInterface(true);
        type.addTypeParameter(generic.clone());
        type.addTypeParameter(argType.clone());

        for (CompilationUnit clazz : nodeUnits) {
            try {
                var t = clazz.getPrimaryType().get();
                if (!(t instanceof ClassOrInterfaceDeclaration c))
                    continue;
                if (c.isInterface())
                    continue;

                cu.addImport(t.getFullyQualifiedName().get());

                var m = type.addMethod("visit");
                m.addParameter(new ClassOrInterfaceType(null, t.getNameAsString()), "n");
                m.addParameter(argType.clone(), "arg");
                m.setType(generic.clone());
                m.setBody(null);

                var accept = t.addMethod("accept", PUBLIC);
                accept.setType(generic.clone());
                accept.getTypeParameters().add(generic.clone());
                accept.getTypeParameters().add(argType.clone());
                accept.addParameter(
                    new ClassOrInterfaceType(null,
                        new SimpleName(type.getFullyQualifiedName().get()),
                        new NodeList<>(generic.clone(), argType.clone())),
                    "visitor");
                accept.addParameter(argType.clone(), "arg");
                accept.getBody().get()
                        .addStatement("return visitor.visit(this,arg);");
            } catch (Exception e) {
                System.err.println(e.getMessage() + " :: " + clazz.getStorage().get().getPath());
            }
        }
        sourceRoot.add(cu);
    }


    public static void createDeepCopyVisitor(List<CompilationUnit> nodeUnits,
            SourceRoot sourceRoot) {

    }

    public interface PostStep {
        void applyOn(List<CompilationUnit> nodeUnits, SourceRoot sourceRoot);
    }
}
