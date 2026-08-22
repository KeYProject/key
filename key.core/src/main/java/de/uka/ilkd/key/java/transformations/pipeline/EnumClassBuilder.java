/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.stream.Collectors;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserEnumConstantDeclaration;

import static com.github.javaparser.ast.Modifier.DefaultKeyword.*;

/// This transformation is made to transform any found [EnumDeclaration] into a corresponding
/// [ClassOrInterfaceDeclaration].
///
/// @author mulbrich, drodt
/// @version 2026-03-03
/// @since 2006-11-20
public class EnumClassBuilder extends JavaTransformerAbstract {
    /// a mapping of enums to the newly created class declarations.
    final Map<EnumDeclaration, ClassOrInterfaceDeclaration> substitutes = new LinkedHashMap<>();

    public EnumClassBuilder(TransformationPipelineServices pipelineServices) {
        super(pipelineServices);
    }

    @Override
    public void apply(CompilationUnit cu) {
        cu.walk(EnumDeclaration.class, it -> {
            it.replace(createEnumClassEquivalent(it));
            substitutes.put(it, createEnumClassEquivalent(it));
        });
        cu.walk(NameExpr.class, it -> {
            if (it.getParentNode().isPresent() && it.getParentNode().get() instanceof SwitchEntry
                    && it.resolve() instanceof JavaParserEnumConstantDeclaration ed) {
                it.replace(
                    new FieldAccessExpr(new NameExpr(ed.getType().toString()), ed.getName()));
            }
        });
        for (var e : substitutes.entrySet()) {
            e.getKey().replace(e.getValue());
        }
    }

    /// name of the static variable of the array holding the names of the constants.
    private static final String ENUM_NAMES = "$enumConstantNames";

    ClassOrInterfaceDeclaration createEnumClassEquivalent(EnumDeclaration declaration) {
        // clone once!
        var ed = declaration.clone();

        var cu = new ClassOrInterfaceDeclaration();
        cu.setName(ed.getName());
        cu.setModifiers(ed.getModifiers());

        if (!cu.hasModifier(FINAL)) {
            // enum is always final
            cu.addModifier(FINAL);
        }

        if (declaration.isNestedType() && !cu.hasModifier(STATIC)) {
            // enum is always final
            cu.addModifier(STATIC);
        }

        ed.getComment().ifPresent(cu::setComment);
        cu.addExtendedType(Enum.class);
        cu.setImplementedTypes(ed.getImplementedTypes());

        for (var e : ed.entries()) {
            makeConstantField(cu, e);
        }

        cu.getMembers().addAll(ed.getMembers());
        addFieldEnumNames(cu, declaration);
        addFieldEnumValues(cu, declaration);
        addMethodValues(cu, declaration);
        addMethodValueOf(cu, declaration);
        addMethodName(cu, declaration);
        addMethodOrdinal(cu, declaration);

        addNonnullInvariant(cu, declaration);
        addDisjointInvariant(cu, declaration);
        addAdtInvariant(cu, declaration);

        return cu;
    }

    private void addDisjointInvariant(ClassOrInterfaceDeclaration cu, EnumDeclaration declaration) {
        var consts = declaration.getEntries().stream()
                .map(NodeWithSimpleName::getNameAsString).toList();
        for (var a : consts) {
            for (var b : consts) {
                if (a == b)
                    continue;
                services.attachTypeSpec(cu, "static invariant %s != %s;".formatted(a, b));
            }
        }
    }

    private void addNonnullInvariant(ClassOrInterfaceDeclaration cu, EnumDeclaration declaration) {
        var constNonNull = declaration.getEntries().stream()
                .map(NodeWithSimpleName::getNameAsString)
                .map("%s != null"::formatted)
                .collect(Collectors.joining(" && "));
        services.attachTypeSpec(cu, "static invariant %s;".formatted(constNonNull));
    }

    private void addAdtInvariant(ClassOrInterfaceDeclaration cu, EnumDeclaration declaration) {
        var constNonNull = declaration.getEntries().stream()
                .map(NodeWithSimpleName::getNameAsString)
                .map("%s == x"::formatted)
                .collect(Collectors.joining(" || "));
        services.attachTypeSpec(cu, "static invariant (\\forall %s x; %s);".formatted(
            cu.getNameAsString(), constNonNull));
    }

    /**
     * get all declared enum constants for this enum. return them as a list.
     *
     * @return a list of the enum constants, not null
     *         <p>
     *         public List<EnumConstantDeclaration> getEnumConstantDeclarations() {
     *         return enumConstants;
     *         }
     */
    private void makeConstantField(ClassOrInterfaceDeclaration cu, EnumConstantDeclaration e) {
        var args = e.arguments();
        final var type = new ClassOrInterfaceType(null, cu.getNameAsString());
        var init = new ObjectCreationExpr(null, type.clone(), args);
        var field = cu.addField(type, e.name().getIdentifier(), PUBLIC, STATIC, FINAL);
        field.getVariables().getFirst().setInitializer(init);
    }

    private void addFieldEnumNames(ClassOrInterfaceDeclaration target, EnumDeclaration source) {
        var init = new ArrayInitializerExpr();
        for (var ec : source.getEntries()) {
            init.values().add(new StringLiteralExpr(ec.getNameAsString()));
        }
        var field = target.addField(String[].class, ENUM_NAMES, PRIVATE, STATIC, FINAL);
        field.getVariables().getFirst().setInitializer(init);
    }

    private void addFieldEnumValues(ClassOrInterfaceDeclaration target, EnumDeclaration source) {
        var init = new ArrayInitializerExpr();
        for (var ec : source.getEntries()) {
            init.values().add(ec.getNameAsExpression());
        }
        final var type = new ClassOrInterfaceType(null, target.getNameAsString());
        final var arrayType = new ArrayType(type);
        var field = target.addField(arrayType, "values", PRIVATE, STATIC, FINAL);
        field.getVariables().getFirst().setInitializer(init);
    }


    /// `public static #E[] values() { return new #E { #consts }; }`
    private void addMethodValues(ClassOrInterfaceDeclaration target, EnumDeclaration source) {
        var consts =
            source.getEntries().stream().map(EnumConstantDeclaration::getNameAsExpression).toList();
        var method = target.addMethod("values", PUBLIC, STATIC);
        final var type = new ClassOrInterfaceType(null, target.getNameAsString());
        final var arrayType = new ArrayType(type);
        method.getBody().get().addStatement(new ReturnStmt(new NameExpr("values")));
    }

    private void addMethodValueOf(ClassOrInterfaceDeclaration target, EnumDeclaration source) {
        // public static #E valueOf(String string) { for (#E e : values()) { if
        // (e.name().equals(string)) return e; } throw new IllegalArgumentException(); }
        var mtd = target.addMethod("valueOf", PUBLIC, STATIC);

        mtd.setType(new ClassOrInterfaceType(null, target.getNameAsString()));
        mtd.addParameter(String.class, "name");
        BlockStmt body = new BlockStmt();
        for (var entry : source.getEntries()) {
            var equality = callEquals(strLiteral(entry.getNameAsString()), new NameExpr("name"));
            var ifStmt = new IfStmt(equality, new ReturnStmt(entry.getNameAsExpression()), null);
            body.addAndGetStatement(ifStmt);
        }

        body.addStatement("throw new IllegalArgumentException();");
        mtd.setBody(body);
    }

    /// `public String name() { return $enumConstantNames[ordinal()]; }`
    private void addMethodName(ClassOrInterfaceDeclaration target, EnumDeclaration source) {
        var method = target.addMethod("name", PUBLIC);
        method.setType(String.class);
        method.getBody().get()
                .addStatement(new ReturnStmt(new ArrayAccessExpr(new NameExpr(ENUM_NAMES),
                    new MethodCallExpr("ordinal"))));
    }

    /// `public int ordinal() { if(this==A) return 0; ... if(this==Z) return 26; return 0; }`
    private void addMethodOrdinal(ClassOrInterfaceDeclaration target, EnumDeclaration source) {
        var method = target.addMethod("ordinal", PUBLIC);
        method.setType(new PrimitiveType(PrimitiveType.Primitive.INT));
        NodeList<EnumConstantDeclaration> entries = source.getEntries();
        for (int i = 0, entriesSize = entries.size(); i < entriesSize; i++) {
            var entry = entries.get(i);
            var equality = new BinaryExpr(new ThisExpr(), entry.getNameAsExpression(),
                BinaryExpr.Operator.EQUALS);
            var ifStmt = new IfStmt(equality,
                new ReturnStmt(new IntegerLiteralExpr(Integer.valueOf(i))), null);
            method.getBody().get().addAndGetStatement(ifStmt);
        }
        method.getBody().get()
                .addAndGetStatement(new ReturnStmt(new IntegerLiteralExpr(Integer.valueOf(0))));
    }


    private Expression callEquals(Expression scope, Expression arg) {
        return new MethodCallExpr(scope, "equals", new NodeList<>(arg));
    }

    private StringLiteralExpr strLiteral(String n) {
        return new StringLiteralExpr(n);
    }
}
