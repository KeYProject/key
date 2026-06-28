/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.ncore.java;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.utils.Utils;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import java.util.stream.Collectors;

import static com.github.javaparser.StaticJavaParser.*;
import static com.github.javaparser.ast.Modifier.DefaultKeyword.*;

/**
 *
 * @author Alexander Weigl
 * @version 1 (4/19/26)
 */
@SuppressWarnings("OptionalGetWithoutIsPresent")
public class NodeSteps {
    interface NodeStep {
        void applyOn(Generator generator, ClassOrInterfaceDeclaration target);
    }

    record addWiths() implements NodeStep {
        @Override
        public void applyOn(Generator generator, ClassOrInterfaceDeclaration target) {
            target.getFields().stream()
                    .filter(NodeSteps::fieldIsWritable)
                    .flatMap(it -> it.getVariables().stream()).forEach(it -> {
                        var args =
                                target.getFields().stream()
                                        .flatMap(f -> f.getVariables().stream())
                                        .map(v -> {
                                            if (v == it) {
                                                return (Expression) v.getNameAsExpression();
                                            } else {
                                                return new MethodCallExpr(null, v.getNameAsString());
                                            }
                                        }).toList();

                        var m = target.addMethod("with" + upperStart(it.getNameAsString()), PUBLIC);
                        m.addParameter(new Parameter(it.getType().clone(), it.getNameAsString()));
                        m.setType(new ClassOrInterfaceType(null, target.getNameAsString()));
                        m.getBody().get().addStatement(new ReturnStmt(
                                new ObjectCreationExpr(null,
                                        new ClassOrInterfaceType(null, target.getNameAsString()),
                                        new NodeList<>(args))));
                    });
        }
    }

    /// returns true, if the field is writable (no constant is set). Used for various places in which a field can get a value,
    private static boolean fieldIsWritable(FieldDeclaration fieldDeclaration) {
        return fieldDeclaration.getVariables()
                .getOFirst()
                .map(NodeSteps::fieldIsWritable).orElse(true);
    }

    private static String upperStart(String nameAsString) {
        var c = nameAsString.substring(0, 1).toUpperCase();
        return c + nameAsString.substring(1);
    }

    record addMatch() implements NodeStep {
        @Override
        public void applyOn(Generator generator, ClassOrInterfaceDeclaration target) {
            if (target.isAbstract() || target.isInterface()) {
                return;
            }
            MethodDeclaration equals = target.addMethod("match", PUBLIC);
            //equals.addModifier(FINAL);
            equals.addAnnotation(Override.class);
            equals.addAnnotation(Nullable.class);
            equals.setType("MatchConditions");
            final var o = getNullableObject();
            equals.getParameters().add(o);
            equals.addParameter("MatchConditions", "cond");

            BlockStmt body = equals.getBody().get();
            body.addStatement(parseStatement(
                    "if(!(o instanceof %s other)) return null;".formatted(target.getNameAsString())));
            var fields = target.getFields().stream()
                    .filter(it -> it.getAnnotationByName("EqEx").isEmpty())
                    .flatMap(it -> it.getVariables().stream())
                    .toList();
            for (var field : fields) {
                body.addStatement("cond = MatchHelper.match(%s, other.%s, cond);"
                        .formatted(field.getNameAsString(), field.getNameAsString()));
                body.addStatement("if(cond==null) {return null;}");
            }
            body.addStatement("return cond;");
        }
    }

    record addEquals() implements NodeStep {
        @Override
        public void applyOn(Generator generator, ClassOrInterfaceDeclaration target) {
            if (isNonTerminal(target)) {
                return;
            }

            MethodDeclaration equals = target.addMethod("equals", PUBLIC);
            //equals.addModifier(FINAL);
            equals.addAnnotation(Override.class);
            equals.setType(Boolean.TYPE);
            final var o = getNullableObject();
            equals.getParameters().add(o);

            BlockStmt body = equals.getBody().get();
            body.addStatement(
                    parseStatement("if(this == o) return true;"));
            body.addStatement(

                    parseStatement(
                            "if(!(o instanceof %s that)) return false;".formatted(target.getNameAsString())));
            Expression equalFields = target.getFields().stream()
                    .filter(it -> it.getAnnotationByName("EqEx").isEmpty())
                    .flatMap(it -> it.getVariables().stream())
                    .map(it -> callObjects("equals", it.getNameAsExpression(),
                            new FieldAccessExpr(new NameExpr("that"), it.getNameAsString())))
                    .reduce((a, b) -> new BinaryExpr(a, b, BinaryExpr.Operator.AND))
                    .orElse(new BooleanLiteralExpr(true));
            body.addStatement(new

                    ReturnStmt(equalFields));
        }
    }

    record addHashCode(boolean caching) implements NodeStep {
        addHashCode() {
            this(true);
        }

        @Override
        public void applyOn(Generator generator, ClassOrInterfaceDeclaration target) {
            if (isNonTerminal(target)) {
                return;
            }

            VariableDeclarator variable = new VariableDeclarator(new PrimitiveType(PrimitiveType.Primitive.INT), "xxx");
            if (caching) {
                FieldDeclaration field = target.addField(Integer.class, "hashCode", PRIVATE);
                variable = field.getVariables().getFirst();
                field.addAnnotation("EqEx");
                field.addAnnotation("Nullable");
                field.addAnnotation("Internal");
            }

            MethodDeclaration hashCode = target.addMethod("hashCode", PUBLIC);
            //hashCode.addModifier(FINAL);
            hashCode.addAnnotation(Override.class);
            hashCode.setType(Integer.TYPE);
            Expression[] args = target.getFields()
                    .stream()
                    .filter(it -> it.getAnnotationByName("EqEx").isEmpty())
                    .flatMap(it -> it.getVariables().stream())
                    .map(NodeWithSimpleName::getNameAsExpression)
                    .map(it -> (Expression) it)
                    .toArray(Expression[]::new);

            if (args.length == 0)
                assert false : "No defined fields";
            else {
                final Expression compute = callObjects("hash", args);
                if (caching) {
                    final Expression hashCodeIsNull = new BinaryExpr(variable.getNameAsExpression(), new NullLiteralExpr(), BinaryExpr.Operator.EQUALS);
                    final var setHashCode = new ExpressionStmt(new AssignExpr(variable.getNameAsExpression(), compute, AssignExpr.Operator.ASSIGN));
                    hashCode.getBody().get().addStatement(
                            new IfStmt(hashCodeIsNull, setHashCode, null));
                    hashCode.getBody().get().addStatement(new ReturnStmt(variable.getNameAsExpression()));
                } else {
                    hashCode.getBody().get().addStatement(new ReturnStmt(compute));
                }
            }
        }
    }

    record ToString() implements NodeStep {
        @Override
        public void applyOn(Generator generator, ClassOrInterfaceDeclaration clazz) {
            if (isNonTerminal(clazz)) {
                return;
            }

            MethodDeclaration toString = clazz.addMethod("toString", PUBLIC);
            toString.addAnnotation(Override.class);
            toString.setType(String.class);
            var parameters =
                    clazz.getFields().stream().flatMap(it -> it.getVariables().stream()).toList();
            var sb = (clazz.getNameAsString() + "[")
                    + parameters.stream().map(NodeWithSimpleName::getNameAsString).map(it -> it + "=%s")
                    .collect(Collectors.joining(", "))
                    + "]";

            var args = parameters.stream().map(NodeWithSimpleName::getNameAsExpression)
                    .map(it -> (Expression) it).toList();
            toString.getBody().get().addStatement(new ReturnStmt(
                    new MethodCallExpr(new StringLiteralExpr(sb), "formatted", new NodeList<>(args))));
        }
    }

    record handleRoot() implements NodeStep {
        @Override
        public void applyOn(Generator generator, ClassOrInterfaceDeclaration clazz) {
            if (isRoot(clazz)) {
                clazz.setInterface(false);
                clazz.addModifier(PUBLIC);
                clazz.getExtendedTypes().clear();
                clazz.setAnnotations(new NodeList<>());
                clazz.addAnnotation(NullMarked.class);
            } else if (isNonTerminal(clazz)) {

            }
        }
    }

    static boolean isRoot(ClassOrInterfaceDeclaration clazz) {
        return clazz.getAnnotationByName("Root").isPresent();
    }

    static boolean isNonTerminal(ClassOrInterfaceDeclaration clazz) {
        return isRoot(clazz) || clazz.isInterface() || clazz.hasModifier(ABSTRACT);
    }

    static boolean isTerminal(ClassOrInterfaceDeclaration clazz) {
        return !isNonTerminal(clazz);
    }

    private static Expression callObjects(String method, Expression... args) {
        return new MethodCallExpr(new NameExpr("Objects"), method, new NodeList<>(args));
    }

    private static @NonNull Parameter getNullableObject() {
        Type tObject = StaticJavaParser.parseType("java.lang.Object");
        return new Parameter(new NodeList<>(), tObject, new SimpleName("o"));
    }

    record AddAllFieldsConstructor() implements NodeStep {
        @Override
        public void applyOn(Generator generator, ClassOrInterfaceDeclaration target) {
            if (target.isInterface()) {
                return;
            }
            ConstructorDeclaration constr = new ConstructorDeclaration();
            var body = constr.getBody().get();
            var params = constr.getParameters();
            constr.setName(target.getNameAsString());
            constr.setModifiers(PUBLIC);

            for (var field : target.getFields()) {
                var isOptional = field.getAnnotations().stream()
                        .anyMatch(it -> it.getNameAsString().equals("Nullable"));
                for (var variable : field.getVariables()) {
                    if (variable.getInitializer().isPresent()) {
                        continue;
                    }
                    final var p = new Parameter(variable.getType().clone(), variable.getNameAsString());
                    field.getAnnotations().stream().map(AnnotationExpr::clone)
                            .forEach(p::addAnnotation);
                    params.add(p);
                    if (isOptional) {
                        body.addStatement(
                                "this.%s = %s;".formatted(
                                        variable.getNameAsString(), variable.getNameAsString()));
                    } else {
                        body.addStatement(
                                "this.%s = Objects.requireNonNull(%s);".formatted(
                                        variable.getNameAsString(), variable.getNameAsString()));
                    }
                }
            }


            target.addMember(constr);
        }
    }

    record addAllWoOptFieldsConstructor() implements NodeStep {
        @Override
        public void applyOn(Generator generator, ClassOrInterfaceDeclaration target) {
            if (target.isInterface()) {
                return;
            }

            var hasOptionalFields = target.getFields().stream().anyMatch(field ->
                    field.getAnnotations().stream().anyMatch(it -> it.getNameAsString().equals("Nullable")));
            if (!hasOptionalFields) {
                return;
            }

            ConstructorDeclaration constr = new ConstructorDeclaration();
            var body = constr.getBody().get();
            var params = constr.getParameters();
            constr.setName(target.getNameAsString());
            constr.setModifiers(PUBLIC);

            for (var field : target.getFields()) {
                var isOptional = field.getAnnotations().stream()
                        .anyMatch(it -> it.getNameAsString().equals("Nullable"));


                for (var variable : field.getVariables()) {
                    if (variable.getInitializer().isPresent()) {
                        continue;
                    }

                    if (isOptional) {
                        body.addStatement(
                                "this.%s = null;".formatted(variable.getNameAsString()));
                    } else {
                        final var p =
                                new Parameter(variable.getType().clone(), variable.getNameAsString());
                        field.getAnnotations().stream().map(AnnotationExpr::clone)
                                .forEach(p::addAnnotation);
                        params.add(p);
                        body.addStatement(
                                "this.%s = Objects.requireNonNull(%s);".formatted(
                                        variable.getNameAsString(), variable.getNameAsString()));
                    }
                }
            }

            target.addMember(constr);
        }
    }

    record addOverrideConstructor() implements NodeStep {
        @Override
        public void applyOn(Generator generator, ClassOrInterfaceDeclaration target) {
            if (target.isInterface()) {
                return;
            }

            ConstructorDeclaration constr = target.addConstructor(PUBLIC);
            var body = constr.getBody().get();
            var params = constr.getParameters();
            constr.setName(target.getNameAsString());
            params.add(
                    new Parameter(new ClassOrInterfaceType(null, target.getNameAsString()), "other"));

            params.add(new Parameter(parseType("Properties"), "map"));

            var args = target.getFields().stream()
                    .filter(NodeSteps::fieldIsWritable)
                    .flatMap(it -> it.getVariables().stream())
                    .map(NodeWithSimpleName::getNameAsString)
                    .map(it -> (Expression) parseExpression(
                            "map.get(PROPERTY_%s, other.%s)".formatted(it.toUpperCase(), it)))
                    .toList();
            body.addStatement(new MethodCallExpr(null, "this", new NodeList<>(args)));
        }
    }

    record addOverrideConstructor2() implements NodeStep {
        @Override
        public void applyOn(Generator generator, ClassOrInterfaceDeclaration target) {
            if (target.isInterface()) {
                return;
            }

            ConstructorDeclaration constr = target.addConstructor(PUBLIC);
            var body = constr.getBody().get();
            var params = constr.getParameters();
            constr.setName(target.getNameAsString());
            params.add(new Parameter(parseType("Properties"), "map"));

            var args = target.getFields().stream()
                    .filter(NodeSteps::fieldIsWritable)
                    .flatMap(it -> it.getVariables().stream())
                    .map(NodeWithSimpleName::getNameAsString)
                    .map(it -> (Expression) parseExpression(
                            "map.get(PROPERTY_%s)".formatted(it.toUpperCase())))
                    .toList();
            body.addStatement(new MethodCallExpr(null, "this", new NodeList<>(args)));
        }
    }

    record addGetProperties() implements NodeStep {
        @Override
        public void applyOn(Generator generator, ClassOrInterfaceDeclaration target) {
            if (target.isInterface()) {
                return;
            }

            var method = target.addMethod("properties", PUBLIC);
            method.setType("Properties");
            var body = method.getBody().get();


            body.addStatement("Properties p = new DefaultProperties();");
            target.getFields().stream()
                    .flatMap(it -> it.getVariables().stream())
                    .forEach(variable -> body.addStatement("p.set(PROPERTY_%s, %s());".formatted(
                            variable.getNameAsString().toUpperCase(), variable.getNameAsString())));
            body.addStatement("return p;");
        }
    }

    record addCopyConstructor() implements NodeStep {
        @Override
        public void applyOn(Generator generator, ClassOrInterfaceDeclaration target) {
            if (isNonTerminal(target)) {
                return;
            }

            ConstructorDeclaration constr = target.addConstructor(PUBLIC);
            var body = constr.getBody().get();
            var params = constr.getParameters();
            constr.setName(target.getNameAsString());
            params.add(
                    new Parameter(new ClassOrInterfaceType(null, target.getNameAsString()), "other"));

            /*
             * for (var field : target.getFields()) {
             * for (var variable : field.getVariables()) {
             * //params.add(new Parameter(variable.getType().clone(), variable.getNameAsString()));
             * body.addStatement(
             * new ExpressionStmt(new AssignExpr(
             * new FieldAccessExpr(new ThisExpr(), variable.getNameAsString()),
             * new FieldAccessExpr(new NameExpr("other"), variable.getNameAsString()),
             * AssignExpr.Operator.ASSIGN
             * ))
             * );
             * }
             * }
             */

            var args = target.getFields().stream()
                    .flatMap(it -> it.getVariables().stream())
                    .filter(NodeSteps::fieldIsWritable)
                    .map(NodeWithSimpleName::getNameAsString)
                    .map(it -> (Expression) new FieldAccessExpr(new NameExpr("other"), it))
                    .toList();
            body.addStatement(new MethodCallExpr(null, "this", new NodeList<>(args)));

        }
    }

    private static boolean fieldIsWritable(VariableDeclarator variableDeclarator) {
        return variableDeclarator.getInitializer().isEmpty();
    }

    record SetPackage(String packageName) implements NodeStep {
        SetPackage() {
            this("org.key_project.java.ast");
        }

        @Override
        public void applyOn(Generator generator, ClassOrInterfaceDeclaration target) {
            var annotation = target.getAnnotationByName("Package")
                    .map(NodeWithName::getNameAsString)
                    .orElse(packageName);

            CompilationUnit cu = target.findCompilationUnit().get();
            cu.setPackageDeclaration(annotation);

            cu.setStorage(Generator.ROOT.resolve(annotation.replace(".", "/"))
                    .resolve(target.getNameAsString() + ".java"));

            target.addAnnotation(NullMarked.class);
            target.addModifier(PUBLIC);

            boolean isAbstract = target.isAbstract() || target.isInterface();
            boolean isRoot = isRoot(target);
            if (isAbstract) {
                target.addModifier(SEALED);
                if (!isRoot) {
                    target.setInterface(true);
                    target.removeModifier(ABSTRACT);
                    target.getMethods().forEach(it -> it.addModifier(DEFAULT));
                }

                var permittedTypes = generator.getStep(PreSteps.PreComputation.class).permittedTypes;
                for (var s : permittedTypes.get(target.getNameAsString())) {
                    if (s.equals("BaseAstNode")) continue;
                    target.getPermittedTypes().add(new ClassOrInterfaceType(null, s));
                }
            } else {
                target.addModifier(FINAL);
                target.setImplementedTypes(target.getExtendedTypes());
                target.setExtendedTypes(new NodeList<>());
            }
        }
    }

    record ProcessFieldsAccessor() implements NodeStep {
        @Override
        public void applyOn(Generator generator, ClassOrInterfaceDeclaration target) {
            if (target.isInterface())
                return;

            target.findCompilationUnit().get().addImport("org.key_project.java.ast.Property");

            for (var field : target.getFields()) {
                for (var variable : field.getVariables()) {
                    final var dataKey = new ClassOrInterfaceType(null, new SimpleName("Property"),
                            new NodeList<>(toBoxType(variable.getType().clone())));
                    var f = target.addField(
                            dataKey, "PROPERTY_" + variable.getNameAsString().toUpperCase(), PUBLIC, STATIC,
                            FINAL);
                    f.getVariables().getFirst().setInitializer(
                            "new Property<>(\"%s\")".formatted(variable.getNameAsString()));
                }
            }
        }
    }

    private static Type toBoxType(Type clone) {
        if (clone instanceof PrimitiveType pt) {
            return pt.toBoxedType();
        }
        return clone;
    }

    record ProcessFields(boolean immutable) implements NodeStep {
        ProcessFields() {
            this(true);
        }

        @Override
        public void applyOn(Generator generator, ClassOrInterfaceDeclaration target) {
            boolean isAbstract = isNonTerminal(target);

            for (var field : target.getFields()) {
                if (isAbstract) {
                    field.remove();
                } else {
                    if (immutable) {
                        field.setModifiers(PRIVATE, FINAL);
                    } else {
                        field.setModifiers(PRIVATE);
                    }
                }

                for (var variable : field.getVariables()) {
                    if (isList(variable) && immutable) {
                        var old = variable.getType().asClassOrInterfaceType();
                        old.setName("RoList");
                    }

                    addGetter(target, field, variable, isAbstract);
                    if (!immutable) {
                        addSetter(target, field, variable, isAbstract);
                    }
                    field.getAnnotationByName("Override")
                            .ifPresent(it -> it.remove());
                }
            }
        }

        private static void addSetter(ClassOrInterfaceDeclaration target, FieldDeclaration field, VariableDeclarator variable, boolean isAbstract) {
            var setter = target.addMethod("set" + Utils.capitalize(variable.getNameAsString()));
            setter.setType(new ClassOrInterfaceType(null, target.getNameAsString()));

            var parameter = new Parameter(variable.getType().clone(), "value");

            var nullable = field.getAnnotationByName("Nullable");
            if (nullable.isPresent()) {
                parameter.addAndGetAnnotation(Nullable.class);
            }
            setter.addParameter(parameter);

            if (isAbstract) {
                setter.addModifier(Modifier.DefaultKeyword.ABSTRACT);
                setter.setBody(null);
            } else {
                setter.getBody().get().addStatement("%s = %s;".formatted(variable.getNameAsString(), "value"));
                setter.getBody().get().addStatement(new ReturnStmt(new ThisExpr()));
                setter.addModifier(PUBLIC);
            }
            field.getAnnotationByName("Override")
                    .ifPresent(it -> setter.addAnnotation(it.clone()));
        }

        private void addGetter(ClassOrInterfaceDeclaration target, FieldDeclaration field, VariableDeclarator variable, boolean isAbstract) {
            var getter = target.addMethod(variable.getNameAsString());
            //immutable ? variable.getNameAsString() : "get" + Utils.capitalize(variable.getNameAsString()));
            getter.setType(variable.getType().clone());

            var nullable = field.getAnnotationByName("Nullable");
            if (nullable.isPresent()) {
                getter.addAndGetAnnotation(Nullable.class);
            }

            if (isAbstract) {
                getter.addModifier(Modifier.DefaultKeyword.ABSTRACT);
                getter.setBody(null);
            } else {
                getter.getBody().get()
                        .addStatement(new ReturnStmt(variable.getNameAsExpression()));
                getter.addModifier(PUBLIC);
            }
            field.getAnnotationByName("Override")
                    .ifPresent(it -> getter.addAnnotation(it.clone()));
        }
    }

    record addBuilder() implements NodeStep {
        @Override
        public void applyOn(Generator generator, ClassOrInterfaceDeclaration target) {
            if (isNonTerminal(target)) {
                return;
            }

            var builder = new ClassOrInterfaceDeclaration();
            builder.setName("Builder");
            builder.addModifier(PUBLIC, FINAL, STATIC);

            for (var field : target.getFields()) {
                for (var variable : field.variables()) {
                    if (variable.getInitializer().isEmpty()) {
                        var f =
                                builder.addField(variable.getType().clone(), variable.getNameAsString(), PUBLIC);
                        f.addAnnotation(Nullable.class);
                    }
                }
            }

            var build = builder.addMethod("build", PUBLIC);
            build.setType(new ClassOrInterfaceType(null, target.getNameAsString()));

            var args = builder.getFields().stream()
                    .flatMap(it -> it.variables().stream())
                    .filter(NodeSteps::fieldIsWritable)
                    .map(it -> (Expression) it.getNameAsExpression())
                    .toList();
            build.getBody().get().addStatement(new ReturnStmt(
                    new ObjectCreationExpr(null,
                            new ClassOrInterfaceType(null, target.getNameAsString()),
                            new NodeList<>(args))));

            builder.getFields().stream()
                    .flatMap(it -> it.variables().stream())
                    .filter(NodeSteps::fieldIsWritable)
                    .forEach(it -> {
                        var m = builder.addMethod(it.getNameAsString(), PUBLIC);
                        m.addParameter(new Parameter(it.getType().clone(), it.getNameAsString()));
                        m.setType(new ClassOrInterfaceType(null, "Builder"));
                        m.getBody().get().addStatement(
                                "this.%s=%s;".formatted(it.getNameAsString(), it.getNameAsString()));
                        m.getBody().get().addStatement("return this;");
                    });


            builder.getFields().stream()
                    .flatMap(it -> it.variables().stream())
                    .filter(NodeSteps::fieldIsWritable)
                    .filter(NodeSteps::isList)
                    .forEach(it -> {
                        var m = builder.addMethod(it.getNameAsString(), PUBLIC);
                        var t =
                                it.getType().asClassOrInterfaceType().getTypeArguments().get().getFirst();
                        m.addParameter(new Parameter(t.clone(), it.getNameAsString()));
                        m.setType(new ClassOrInterfaceType(null, "Builder"));
                        m.getBody().get().addStatement("if(this.%s==null) this.%s = new ArrayList<>();"
                                .formatted(it.getNameAsString(), it.getNameAsString()));
                        m.getBody().get().addStatement(
                                "this.%s.add(%s);".formatted(it.getNameAsString(), it.getNameAsString()));
                        m.getBody().get().addStatement("return this;");
                    });

            target.addMember(builder);

            var tb = target.addMethod("builder", PUBLIC);
            tb.setType(new ClassOrInterfaceType(null, "Builder"));
            final var b = tb.getBody().get();
            b.addStatement("Builder b =  new Builder();");
            builder.getFields().stream()
                    .flatMap(it -> it.variables().stream())
                    .filter(NodeSteps::fieldIsWritable)
                    .forEach(it ->
                            b.addStatement("b.%s = %s;".formatted(it.getNameAsString(), it.getNameAsString())));
            b.addStatement("return b;");
        }
    }

    private static boolean isList(VariableDeclarator type) {
        if (type.getType().isClassOrInterfaceType()) {
            final var name = type.getType().asClassOrInterfaceType().getNameAsString();
            return name.equals("List") || name.equals("RoList");
        }
        return false;
    }

    ///
    public record EnforceHierarchy(String type) implements NodeStep {
        public EnforceHierarchy() {
            this("JavaSourceElement");
        }

        @Override
        public void applyOn(Generator generator, ClassOrInterfaceDeclaration decl) {
            if (isTerminal(decl)) {
                decl.addExtendedType(type);
            }
        }
    }


}
