/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.declaration;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.abstraction.Constructor;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import org.key_project.util.collection.ImmutableArray;

import java.util.List;


/**
 * The getTypeReference method returns null - constructors do not have explicite return types. A
 * constructor declaration contains its own name even though it must match the class name: the name
 * occurs as syntactical element and hence must be represented. taken from COMPOST and changed to
 * achieve an immutable structure
 */
public class ConstructorDeclaration extends MethodDeclaration implements Constructor {
    /**
     * Constructor declaration.
     *
     * @param modifiers
     *        a modifier array.
     * @param name
     *        an identifier.
     * @param parameters
     *        a parameter declaration mutable list.
     * @param exceptions
     *        a throws.
     * @param body
     *        a statement block.
     * @param parentIsInterfaceDeclaration
     *        a boolean set true iff parent is an InterfaceDeclaration
     */
    @Deprecated
    public ConstructorDeclaration(Modifier[] modifiers, ProgramElementName name,
            ParameterDeclaration[] parameters, Throws exceptions, StatementBlock body,
            boolean parentIsInterfaceDeclaration) {
        super(modifiers, null, name, parameters, exceptions, body, parentIsInterfaceDeclaration);
    }

    public ConstructorDeclaration(PositionInfo pi, List<Comment> c, ImmutableArray<Modifier> map,
            TypeReference o, Comment[] comments, ProgramElementName name,
            ImmutableArray<ParameterDeclaration> map1,
            Throws exceptions, StatementBlock body, boolean parentIsInterfaceDeclaration) {
        super(pi, c, map, o, comments, name, map1, exceptions, body, parentIsInterfaceDeclaration);
    }


    /**
     * Constructors are never abstract.
     */
    @Override
    public boolean isAbstract() {
        return false;
    }


    /**
     * Constructors are never final.
     */
    @Override
    public boolean isFinal() {
        return false;
    }


    /**
     * Constructors are never native.
     */
    @Override
    public boolean isNative() {
        return false;
    }


    /**
     * Constructors are never static.
     */
    @Override
    public boolean isStatic() {
        return false;
    }


    /**
     * Constructors are never strictfp.
     */
    @Override
    public boolean isStrictFp() {
        return false;
    }


    /**
     * Constructors are never synchronized.
     */
    @Override
    public boolean isSynchronized() {
        return false;
    }


    @Override
    public void visit(Visitor v) {
        v.performActionOnConstructorDeclaration(this);
    }
}
