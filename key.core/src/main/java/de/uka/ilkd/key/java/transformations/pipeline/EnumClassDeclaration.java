/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import java.util.List;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;

/// This class is used to describe an enum type by its equivalent class declaration.
/// The transformation [EnumClassBuilder] transform an [EnumDeclaration] to an
/// EnumClassDeclaration by
/// - adding static fields for the enum constants
/// - adding static field for names
/// - adding the methods as specified in the JLS 8.9
/// - adding "extends Enum" to the ClassDeclaration
///
/// Currently anonymous implementations for constants are not supported as they are anonymous inner
/// classes which are not supported by KeY.
///
/// The additional methods are constructed as follows (E is the name of the enum, (e1, ..., en) its
/// constants):
/// <pre>
/// public static E[] values() { return new E[] { e1,..., en } };
///
/// public static E valueOf(java.lang.String string) {
/// for(E e : values()) {
/// if(e.name().equals(string))
/// return e;
/// }
/// throw new IllegalArgumentException();
/// }
///
/// public java.lang.String name() { return ENUM_NAMES[ordinal()]; }
/// </pre>
///
/// Additionally the fields that are enum constants are remembered.
///
/// @author mulbrich, drodt
/// @since 2006-11-18
/// @version 2026-03-03
public class EnumClassDeclaration extends ClassOrInterfaceDeclaration {
    /// name of the static variable of the array holding the names of the constants.
    private static final String ENUM_NAMES = "$enumConstantNames";

    /// store the EnumConstantDeclarations here. **NB: The AST-parent cannot be set to _this_
    /// because it is not a EnumDeclaration.
    private final List<EnumConstantDeclaration> enumConstants;

    public EnumClassDeclaration() {
        super();
        enumConstants = new NodeList<>();
    }

    public EnumClassDeclaration(EnumDeclaration ed) {
        this();

        setName(ed.getName().clone());

        var modifiers = new NodeList<Modifier>();
        for (var m : ed.modifiers()) {
            modifiers.add(m.clone());
        }
        if (!ed.hasModifier(Modifier.Keyword.FINAL)) {
            // enum is always final
            modifiers.add(new Modifier(Modifier.Keyword.FINAL));
        }
        setModifiers(modifiers);

        if (ed.getComment().isPresent()) {
            setComment(ed.getComment().get().clone());
        }

        setExtendedTypes(new NodeList<>(new ClassOrInterfaceType(
            new ClassOrInterfaceType(new ClassOrInterfaceType(null, "java"), "lang"), "Enum")));

        var implementsTypes = new NodeList<ClassOrInterfaceType>();
        for (var it : ed.implementedTypes()) {
            implementsTypes.add(it.clone());
        }
        setImplementedTypes(implementsTypes);

        for (var e : ed.entries()) {
            enumConstants.add(e.clone());
            makeConstantField(e);
        }

        for (var m : ed.members()) {
            addMember(m.clone());
        }

        addInternalFields();

        addImplicitMethods();
    }

    /**
     * get all declared enum constants for this enum. return them as a list.
     *
     * @return a list of the enum constants, not null
     */
    public List<EnumConstantDeclaration> getEnumConstantDeclarations() {
        return enumConstants;
    }

    private void makeConstantField(EnumConstantDeclaration e) {
        var args = new NodeList<Expression>();
        for (var a : e.arguments()) {
            args.add(a.clone());
        }
        var init =
            new ObjectCreationExpr(null, new ClassOrInterfaceType(null, getNameAsString()), args);
        addMember(new FieldDeclaration(
            new NodeList<>(new Modifier(Modifier.Keyword.PUBLIC),
                new Modifier(Modifier.Keyword.STATIC), new Modifier(Modifier.Keyword.FINAL)),
            new VariableDeclarator(new ClassOrInterfaceType(null, getNameAsString()), e.name(),
                init)));
    }

    private void addInternalFields() {
        var init = new ArrayInitializerExpr();
        for (var ec : getEnumConstantDeclarations()) {
            init.values().add(new StringLiteralExpr(ec.getNameAsString()));
        }
        addMember(new FieldDeclaration(
            new NodeList<>(new Modifier(Modifier.Keyword.PRIVATE),
                new Modifier(Modifier.Keyword.STATIC)),
            new VariableDeclarator(new ArrayType(new ClassOrInterfaceType(null, "String")),
                ENUM_NAMES, init)));
    }

    private void addImplicitMethods() {
        // public static #E[] values() { return new #E { #consts }; }
        var consts = new NodeList<Expression>();
        for (var ec : getEnumConstantDeclarations()) {
            consts.add(new NameExpr(ec.getNameAsString()));
        }
        addMember(new MethodDeclaration(
            new NodeList<>(new Modifier(Modifier.Keyword.PUBLIC),
                new Modifier(Modifier.Keyword.STATIC)),
            new NodeList<>(), new NodeList<>(),
            new ArrayType(new ClassOrInterfaceType(null, getNameAsString())),
            new SimpleName("values"), new NodeList<>(), new NodeList<>(), new BlockStmt(
                new NodeList<>(new ReturnStmt(new ArrayInitializerExpr(consts))))));

        // public static #E valueOf(String string) { for (#E e : values()) { if
        // (e.name().equals(string)) return e; } throw new IllegalArgumentException(); }
        addMember(new MethodDeclaration(
            new NodeList<>(new Modifier(Modifier.Keyword.PUBLIC),
                new Modifier(Modifier.Keyword.STATIC)),
            new NodeList<>(), new NodeList<>(), new ClassOrInterfaceType(null, getNameAsString()),
            new SimpleName("valueOf"),
            new NodeList<>(new Parameter(new ClassOrInterfaceType(null, "String"), "string")),
            new NodeList<>(), new BlockStmt(
                new NodeList<>(
                    new ForEachStmt(
                        new VariableDeclarationExpr(
                            new ClassOrInterfaceType(null, getNameAsString()), "e"),
                        new MethodCallExpr("values"), new BlockStmt(
                            new NodeList<>(new IfStmt(
                                new MethodCallExpr(new MethodCallExpr(new NameExpr("e"), "name"),
                                    "equals", new NodeList<>(new NameExpr("string"))),
                                new ReturnStmt(new NameExpr("e")), null)))),
                    new ThrowStmt(new ObjectCreationExpr(null,
                        new ClassOrInterfaceType(null, "IllegalArgumentException"),
                        new NodeList<>()))))));

        // public String name() { return $enumConstantNames[ordinal()]; }
        addMember(new MethodDeclaration(new NodeList<>(new Modifier(Modifier.Keyword.PUBLIC)),
            new NodeList<>(), new NodeList<>(), new ClassOrInterfaceType(null, getNameAsString()),
            new SimpleName("name"), new NodeList<>(), new NodeList<>(), new BlockStmt(
                new NodeList<>(new ReturnStmt(new ArrayAccessExpr(new NameExpr(ENUM_NAMES),
                    new MethodCallExpr("ordinal")))))));
    }
}
