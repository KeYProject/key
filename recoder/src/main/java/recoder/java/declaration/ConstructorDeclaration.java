/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration;

import recoder.abstraction.Constructor;
import recoder.java.Identifier;
import recoder.java.SourceVisitor;
import recoder.java.StatementBlock;
import recoder.java.declaration.modifier.VisibilityModifier;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

/**
 * The getTypeReference method returns null - constructors do not have explicit return types. A
 * constructor declaration contains its own name even though it must match the class name: the name
 * occurs as syntactical element and hence must be represented.
 */

public class ConstructorDeclaration extends MethodDeclaration implements Constructor {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -1852257105076401562L;

    /**
     * Constructor declaration.
     */

    public ConstructorDeclaration() {
        // nothing to do here
    }

    /**
     * Constructor declaration.
     *
     * @param modifier a visibility modifier.
     * @param name an identifier.
     * @param parameters a parameter declaration mutable list.
     * @param exceptions a throws.
     * @param body a statement block.
     */

    public ConstructorDeclaration(VisibilityModifier modifier, Identifier name,
            ASTList<ParameterDeclaration> parameters, Throws exceptions, StatementBlock body) {
        super(null, null, name, parameters, exceptions, body);
        ASTList<DeclarationSpecifier> mods = new ASTArrayList<>(1);
        if (mods != null) {
            mods.add(modifier);
            setDeclarationSpecifiers(mods);
        }
        makeParentRoleValid();
    }

    /**
     * Constructor declaration.
     *
     * @param proto a constructor declaration.
     */

    protected ConstructorDeclaration(ConstructorDeclaration proto) {
        super(proto);
        // makeParentRoleValid not neccessary
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public ConstructorDeclaration deepClone() {
        return new ConstructorDeclaration(this);
    }

    /**
     * Constructors are never abstract.
     */

    public boolean isAbstract() {
        return false;
    }

    /**
     * Constructors are never final.
     */

    public boolean isFinal() {
        return false;
    }

    /**
     * Constructors are never native.
     */

    public boolean isNative() {
        return false;
    }

    /**
     * Constructors are never static.
     */

    public boolean isStatic() {
        return false;
    }

    /**
     * Constructors are never strictfp.
     */

    public boolean isStrictFp() {
        return false;
    }

    /**
     * Constructors are never synchronized.
     */

    public boolean isSynchronized() {
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitConstructorDeclaration(this);
    }
}
