/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.ncore.java;

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
import com.google.common.collect.Multimap;
import com.google.common.collect.MultimapBuilder;

import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

import static com.github.javaparser.ast.Modifier.DefaultKeyword.*;
import static org.key_project.ncore.java.Generator.ROOT;
import static org.key_project.ncore.java.NodeSteps.isNonTerminal;

public class PostSteps {
    public static void sealing(List<CompilationUnit> compilationUnits, SourceRoot sourceRoot) {
        Multimap<String, String> permittedTypes =
                MultimapBuilder.treeKeys().treeSetValues().build();

        for (var cu : compilationUnits) {
            for (var type : cu.getTypes()) {
                if (!(type instanceof ClassOrInterfaceDeclaration clazz))
                    continue;
                clazz.getExtendedTypes()
                        .forEach(s -> permittedTypes.put(s.getNameAsString(), clazz.getNameAsString()));
                clazz.getImplementedTypes()
                        .forEach(s -> permittedTypes.put(s.getNameAsString(), clazz.getNameAsString()));
            }
        }

        for (var cu : compilationUnits) {
            for (var type : cu.getTypes()) {
                if (type instanceof ClassOrInterfaceDeclaration clazz && clazz.hasModifier(SEALED)) {
                    var subtypes = permittedTypes.get(clazz.getNameAsString());
                    if (subtypes.isEmpty()) {
                        // Java forbids a sealed type without direct subclasses. Marker types
                        // without metamodel subtypes (e.g. IGuard, LoopInitializer) fall back to
                        // plain (non-sealed) interfaces.
                        clazz.removeModifier(SEALED);
                    } else {
                        for (var s : subtypes) {
                            clazz.getPermittedTypes().add(new ClassOrInterfaceType(null, s));
                        }
                    }
                }
            }
        }
    }

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
                if (isNonTerminal(c))
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
                if (isNonTerminal(c))
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

        Set<String> astTypes = collectAstTypes(nodeUnits);

        for (CompilationUnit clazz : nodeUnits) {
            try {
                var t = clazz.getPrimaryType().get();

                if (!(t instanceof ClassOrInterfaceDeclaration c))
                    continue;
                if (NodeSteps.isNonTerminal(c))
                    continue;

                var m = type.addMethod("visit", PUBLIC);
                m.addParameter(new ClassOrInterfaceType(null, t.getNameAsString()), "n");
                m.addAnnotation(Override.class);
                BlockStmt body = m.getBody().get();
                body.addStatement("var b = n.builder();");
                for (var field : builderFields(c, astTypes)) {
                    var v = field.getVariable(0);
                    if (isAstType(v.getType(), astTypes)) {
                        body.addStatement("b.%s = (%s) accept(n.%s());".formatted(
                                v.getNameAsString(), v.getTypeAsString(), v.getNameAsString()));
                    } else {
                        body.addStatement("b.%s = n.%s();".formatted(
                                v.getNameAsString(), v.getNameAsString()));
                    }
                }
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


        Set<String> astTypes = collectAstTypes(nodeUnits);

        for (CompilationUnit clazz : nodeUnits) {
            try {
                var t = clazz.getPrimaryType().get();

                if (!(t instanceof ClassOrInterfaceDeclaration c))
                    continue;
                if (isNonTerminal(c))
                    continue;

                var fields = builderFields(c, astTypes);
                var m = type.addMethod("visit", PUBLIC);
                m.addParameter(new ClassOrInterfaceType(null, t.getNameAsString()), "n");
                m.addAnnotation(Override.class);
                BlockStmt body = m.getBody().get();
                body.addStatement("var b = n.builder();");
                for (var f : fields) {
                    var v = f.getVariable(0);
                    if (isAstType(v.getType(), astTypes)) {
                        body.addStatement("b.%s = (%s) accept(n.%s());".formatted(
                                v.getNameAsString(), v.getTypeAsString(), v.getNameAsString()));
                    } else {
                        body.addStatement("b.%s = n.%s();".formatted(
                                v.getNameAsString(), v.getNameAsString()));
                    }
                }
                final var formatted = "boolean clean = %s;".formatted(fields.isEmpty() ? "false"
                        : fields.stream()
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
            if (c.getNameAsString().equals("ImmutableList")) {
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
        {
            var t = StaticJavaParser.parseTypeParameter("T extends Visitable");
            var accept = type.addMethod("accept", PROTECTED);
            accept.addTypeParameter(t);
            accept.addParameter(StaticJavaParser.parseType("T"), "n");
            accept.setType("T");
            accept.getBody().get().addStatement("return n != null ? (T) n.accept(this) : null;");
        }

        {
            var t = StaticJavaParser.parseTypeParameter("T extends Visitable");
            var acceptList = type.addMethod("accept", PROTECTED);
            acceptList.addTypeParameter(t);
            acceptList.addParameter(StaticJavaParser.parseType("ImmutableList<T>"), "n");
            acceptList.setType("ImmutableList<T>");
            acceptList.getBody().get().addStatement(
                    "return n != null ? n.stream().map(it -> (T) it.accept(this)).collect(ImmutableList.collector()) : null;");
        }
    }

    /// Generates the set of {@code org.key_project.java.ast} types, i.e. the metamodel types that
    /// participate in the sealed AST hierarchy (plus the {@code Visitable}/{@code Matchable}
    /// support interfaces). Everything else (primitives, String, enums, imported KeY types) is a
    /// leaf that the traversal visitors copy by reference.
    private static Set<String> collectAstTypes(List<CompilationUnit> nodeUnits) {
        Set<String> types = new TreeSet<>();
        for (var cu : nodeUnits) {
            if (cu.getPrimaryType().isPresent()
                    && cu.getPrimaryType().get() instanceof ClassOrInterfaceDeclaration c) {
                types.add(c.getNameAsString());
            }
        }
        types.add("Visitable");
        types.add("Matchable");
        return types;
    }

    private static boolean isAstType(Type type, Set<String> astTypes) {
        if (type.isClassOrInterfaceType()) {
            var c = type.asClassOrInterfaceType();
            if (c.getNameAsString().equals("ImmutableList") && c.getTypeArguments().isPresent()) {
                return isAstType(c.getTypeArguments().get().getFirst(), astTypes);
            }
            return astTypes.contains(c.getNameAsString());
        }
        return false;
    }

    /// The fields that end up on the generated {@code Builder}: private, non-constant (no
    /// initializer) fields, excluding the lazily computed {@code hashCode} slot which is only
    /// added to the class itself.
    private static List<FieldDeclaration> builderFields(ClassOrInterfaceDeclaration type,
            Set<String> astTypes) {
        return type.getFields().stream()
                .filter(NodeWithPrivateModifier::isPrivate)
                .filter(f -> f.getVariable(0).getInitializer().isEmpty())
                .filter(f -> !f.getVariable(0).getNameAsString().equals("hashCode"))
                .toList();
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
                if (isNonTerminal(c)) {
                    continue;
                }

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
