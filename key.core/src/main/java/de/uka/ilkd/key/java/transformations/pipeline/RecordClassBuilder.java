/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.key.JmlDocModifier;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.Type;
import org.jspecify.annotations.Nullable;

import static com.github.javaparser.ast.Modifier.DefaultKeyword.*;
import static de.uka.ilkd.key.java.transformations.AstFactory.assign;
import static de.uka.ilkd.key.java.transformations.AstFactory.attributeThis;

/// This transformation is made to transform any found [RecordDeclaration] into a corresponding
/// [ClassOrInterfaceDeclaration].
///
/// @author weigl
/// @see [Java SE 25](https://docs.oracle.com/en/java/javase/25/language/records.html)
/// @since 2026-03-11
public class RecordClassBuilder extends JavaTransformerAbstract {
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
        if (clazz.isNestedType() || clazz.isLocalClassDeclaration()) {
            clazz.addModifier(STATIC); // do not have a pointer to the outer this.
        }
        clazz.setName(recordDeclaration.getName());
        clazz.addExtendedType(java.lang.Record.class);
        addGenerated(clazz);

        for (Parameter parameter : recordDeclaration.getParameters()) {
            FieldDeclaration field =
                clazz.addField(parameter.type(), parameter.getNameAsString(), PRIVATE, FINAL);
            field.getModifiers().addAll(parameter.getModifiers());
            addGenerated(field);

            // only create a getter public final <type> <name>() { return <name>;}
            // unless there is no declaration in the record.
            if (recordDeclaration.getMethodsByName(parameter.getNameAsString()).isEmpty()) {
                MethodDeclaration getter = clazz.addMethod(parameter.getNameAsString());
                getter.setType(parameter.type());
                getter.addModifier(PUBLIC, FINAL);
                for (var mod : parameter.getModifiers()) {
                    if (mod.getKeyword() instanceof JmlDocModifier) {
                        getter.getModifiers().add(mod.clone());
                    }
                }
                getter.getBody().get()
                        .addStatement(new ReturnStmt(parameter.getNameAsExpression()));
                addGenerated(getter);
            }
        }

        createConstructor(recordDeclaration, clazz);

        var generated =
            createEquals(recordDeclaration, clazz) && createHashCode(recordDeclaration, clazz);

        if (generated && false) { // weigl: disabled, further discussion required.
            services.attachTypeSpec(clazz,
                equalFieldsEqualRecords(recordDeclaration));

            services.attachTypeSpec(clazz,
                "public static invariant_free (\\forall %s a; a.equals(a));"
                        .formatted(recordDeclaration.getNameAsString()));

            services.attachTypeSpec(clazz,
                "public static invariant_free (\\forall %s a,b; a.equals(b); b.equals(a));"
                        .formatted(recordDeclaration.getNameAsString()));

            services.attachTypeSpec(clazz,
                "public static invariant_free (\\forall %s a,b,c; a.equals(b) && b.equals(c); a.equals(c));"
                        .formatted(recordDeclaration.getNameAsString()));

            services.attachTypeSpec(clazz,
                "public static invariant_free (\\forall %s a,b; a.equals(b); a.hashCode() == b.hashCode());"
                        .formatted(recordDeclaration.getNameAsString()));
        }

        createToString(recordDeclaration, clazz);

        clazz.getMembers().addAll(recordDeclaration.getMembers());
        return clazz;
    }

    private void createConstructor(RecordDeclaration recordDeclaration,
            ClassOrInterfaceDeclaration clazz) {
        String[] paramTypes = recordDeclaration.getParameters().stream()
                .map(it -> it.getType().asString())
                .toArray(String[]::new);
        var optConstructor = recordDeclaration.getConstructorByParameterTypes(paramTypes);
        ConstructorDeclaration fullConstructor;
        if (optConstructor.isPresent()) {
            fullConstructor = optConstructor.get();
        } else {
            fullConstructor = new ConstructorDeclaration();
            fullConstructor.setName(recordDeclaration.getNameAsString());
            fullConstructor.setModifiers(PUBLIC);
            addGenerated(fullConstructor);
            var body = fullConstructor.getBody().get();
            for (var parameter : recordDeclaration.getParameters()) {
                final var p = parameter.clone();
                fullConstructor.addParameter(p);
                body.addStatement(
                    assign(attributeThis(p.getNameAsString()), p.getNameAsExpression()));
            }
        }

        for (var compactConstructor : recordDeclaration.getCompactConstructors()) {
            fullConstructor.getBody().get().getStatements().add(0, compactConstructor.getBody());
        }

        for (var compactConstructor : recordDeclaration.getCompactConstructors()) {
            compactConstructor.remove();
        }

        var type = recordDeclaration.getNameAsString();
        // var marker = new KeYMarkerStatement(MarkerStatementHelper.KIND_ASSUME);
        var fieldParamEqual = recordDeclaration.getParameters()
                .stream()
                .map(NodeWithSimpleName::getNameAsString)
                // .map(it -> "(`int::select(heap, self, %s::#%s)` == this.%s)".formatted(type, it,
                // it))
                .map(it -> "%s == this.%s".formatted(it, it))
                .collect(Collectors.joining(" && "));

        services.attachSpec(fullConstructor, """
                public normal_behavior
                requires true;
                ensures %s;
                assignable this.*;
                """.formatted(fieldParamEqual));

        clazz.addMember(fullConstructor);
    }

    private void createToString(RecordDeclaration recordDeclaration,
            ClassOrInterfaceDeclaration clazz) {
        boolean hasNoToString = recordDeclaration.getMethodsBySignature("toString").isEmpty();
        if (hasNoToString) {
            MethodDeclaration toString = clazz.addMethod("toString", PUBLIC, FINAL, JML_NON_NULL);
            toString.addAnnotation(Override.class);
            toString.setType(String.class);
            ConcatBuilder concatBuilder = new ConcatBuilder();
            concatBuilder.addStr(clazz.getNameAsString() + "[");
            NodeList<Parameter> parameters = recordDeclaration.getParameters();
            for (int i = 0; i < parameters.size(); i++) {
                Parameter parameter = parameters.get(i);
                concatBuilder.addStr(parameter.getNameAsString() + "=");
                concatBuilder.addVar(parameter.getNameAsString());
                if (i < parameters.size() - 1) {
                    concatBuilder.addStr(",");
                }
            }
            concatBuilder.addStr("]");
            toString.getBody().get().addStatement(new ReturnStmt(concatBuilder.expr));
            addGenerated(toString);
        }
    }

    private boolean createHashCode(RecordDeclaration recordDeclaration,
            ClassOrInterfaceDeclaration clazz) {
        boolean hasNoHashcode = recordDeclaration.getMethodsBySignature("hashCode").isEmpty();
        if (hasNoHashcode) {
            MethodDeclaration hashCode = clazz.addMethod("hashCode", PUBLIC, FINAL);
            hashCode.addAnnotation(Override.class);
            hashCode.setType(Integer.TYPE);
            List<Expression> args = recordDeclaration.getParameters()
                    .stream().map(NodeWithSimpleName::getNameAsExpression)
                    .map(it -> (Expression) it)
                    .toList();
            hashCode.setBody(null);
            addGenerated(hashCode);

            services.attachSpec(hashCode, """
                    public normal_behavior
                    ensures true; requires true;
                    assignable \\strictly_nothing;
                    """);
        }
        return hasNoHashcode;
    }

    private boolean createEquals(RecordDeclaration recordDeclaration,
            ClassOrInterfaceDeclaration clazz) {
        boolean hasNoEquals =
            recordDeclaration.getMethodsBySignature("equals", "java.lang.Object").isEmpty()
                    && recordDeclaration.getMethodsBySignature("equals", "Object").isEmpty();
        if (hasNoEquals) {
            MethodDeclaration equals = clazz.addMethod("equals", PUBLIC, FINAL);
            equals.addAnnotation(Override.class);
            equals.setType(Boolean.TYPE);
            Type tObject = StaticJavaParser.parseType("java.lang.Object");
            var mods = new NodeList<Modifier>(/* new Modifier(JML_NULLABLE) */);
            equals.getParameters().add(new Parameter(mods, tObject, new SimpleName("o")));
            equals.setBody(null);


            services.attachSpec(equals, """
                    public normal_behavior
                    requires true;
                    ensures (
                                   (this == o) //equality of identity
                                || (o instanceof %s && o != null && %s)
                                || (o instanceof %s && o != null && %s)
                            ) <==> \\result;
                    ensures hashCode() != o.hashCode() ==> !\\result;
                    ensures o == null ==> !\\result;
                    assignable \\strictly_nothing;
                    """.formatted(
                recordDeclaration.getNameAsString(),
                recordDeclaration.getParameters().stream()
                        .map(NodeWithSimpleName::getNameAsString)
                        .map(it -> "this.%s==((%s)o).%s".formatted(it,
                            recordDeclaration.getNameAsString(), it))
                        .collect(Collectors.joining(" && ")),
                recordDeclaration.getNameAsString(),
                recordDeclaration.getParameters().stream()
                        .map(it -> {
                            String pname = it.getNameAsString();
                            if (it.getType() instanceof PrimitiveType)
                                return "(%s == ((%s)o).%s)".formatted(pname,
                                    recordDeclaration.getNameAsString(), pname);
                            else
                                return "( this.%s != null ? (this.%s.equals(((%s)o).%s)) : (o.%s == null))"
                                        .formatted(pname, pname,
                                            recordDeclaration.getNameAsString(), pname, pname);
                        })
                        .collect(Collectors.joining(" && "))));

            /*
             * Nobody only contract:
             * BlockStmt body = equals.getBody().get();
             * body.addStatement(
             * mark(services.parseStatement("if(this == o) return true;")));
             * body.addStatement(
             * mark(services.parseStatement("if(!(o instanceof %s)) return false;".formatted(clazz.
             * getNameAsString()))));
             *
             * body.addStatement(
             * mark(services.parseStatement("final %s that = (%s) o;"
             * .formatted(clazz.getNameAsString(), clazz.getNameAsString()))));
             *
             * Expression equalFields = recordDeclaration.getParameters().stream()
             * .map(it -> callObjects("equals", it.getNameAsExpression(),
             * new FieldAccessExpr(new NameExpr("that"), it.getNameAsString())))
             * .reduce((a, b) -> new BinaryExpr(a, b, BinaryExpr.Operator.AND))
             * .orElse(new BooleanLiteralExpr(true));
             * body.addStatement(mark(new ReturnStmt(equalFields)));
             *
             * body.addStatement(mark(new ReturnStmt(new BooleanLiteralExpr(true))));
             */
            addGenerated(equals);
        }
        return hasNoEquals;
    }

    private static @Nullable String equalFieldsEqualRecords(RecordDeclaration recordDeclaration) {
        if (recordDeclaration.getParameters().isEmpty()) {
            return null;
        }

        var identityOfFields = recordDeclaration.getParameters().stream()
                .map(Parameter::getNameAsString)
                .map(it -> "a.%s == b.%s".formatted(it, it))
                .collect(Collectors.joining(" && "));

        return "public invariant_free (\\forall %s a,b; %s; a.equals(b));".formatted(
            recordDeclaration.getNameAsString(),
            identityOfFields);
    }

    private Expression callObjects(String method, Expression... exprs) {
        return callObjects(method, Arrays.stream(exprs).toList());
    }

    private Expression callObjects(String method, List<Expression> exprs) {
        var objects =
            new FieldAccessExpr(new FieldAccessExpr(new NameExpr("java"), "lang"), "Objects");
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
