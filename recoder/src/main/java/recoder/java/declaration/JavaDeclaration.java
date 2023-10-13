/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration;

import java.util.ArrayList;
import java.util.List;

import recoder.java.Declaration;
import recoder.java.JavaNonTerminalProgramElement;
import recoder.java.declaration.modifier.*;
import recoder.list.generic.ASTList;

/**
 * Java declaration.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class JavaDeclaration extends JavaNonTerminalProgramElement implements Declaration {

    /**
     * Modifiers.
     */

    protected ASTList<DeclarationSpecifier> declarationSpecifiers;

    /**
     * Java declaration.
     */

    public JavaDeclaration() {
        // nothing to do here
    }

    /**
     * Java declaration.
     *
     * @param mods a modifier mutable list.
     */

    public JavaDeclaration(ASTList<DeclarationSpecifier> mods) {
        setDeclarationSpecifiers(mods);
        // makeParentRoleValid() called by subclasses' constructors
    }

    /**
     * Java declaration.
     *
     * @param proto a java declaration.
     */

    protected JavaDeclaration(JavaDeclaration proto) {
        super(proto);
        if (proto.declarationSpecifiers != null) {
            declarationSpecifiers = proto.declarationSpecifiers.deepClone();
        }
        // makeParentRoleValid() called by subclasses' constructors
    }

    /**
     * Get modifiers.
     *
     * @return an list containing all modifiers but no annotations. Changes on the list do not
     *         reflect changes on the AST!
     */
    public List<Modifier> getModifiers() {
        if (declarationSpecifiers == null) {
            return new ArrayList<>(0);
        }
        List<Modifier> mml = new ArrayList<>();
        for (DeclarationSpecifier ds : declarationSpecifiers) {
            if (ds instanceof Modifier) {
                mml.add((Modifier) ds);
            }
        }
        return mml;
    }

    /**
     * @return a list of annotations
     */
    public List<AnnotationUseSpecification> getAnnotations() {
        if (declarationSpecifiers == null) {
            return new ArrayList<>(0);
        }
        List<AnnotationUseSpecification> result =
            new ArrayList<>(declarationSpecifiers.size());
        int s = declarationSpecifiers.size();
        for (DeclarationSpecifier ds : declarationSpecifiers) {
            if (ds instanceof AnnotationUseSpecification) {
                result.add((AnnotationUseSpecification) ds);
            }
        }
        return result;
    }

    public ASTList<DeclarationSpecifier> getDeclarationSpecifiers() {
        return declarationSpecifiers;
    }

    public void setDeclarationSpecifiers(ASTList<DeclarationSpecifier> m) {
        declarationSpecifiers = m;
    }

    /**
     * Returns a Public, Protected, or Private Modifier, if there is one, null otherwise. A return
     * value of null can usually be interpreted as package visibility.
     */

    public VisibilityModifier getVisibilityModifier() {
        if (declarationSpecifiers == null) {
            return null;
        }
        for (int i = declarationSpecifiers.size() - 1; i >= 0; i -= 1) {
            DeclarationSpecifier m = declarationSpecifiers.get(i);
            if (m instanceof VisibilityModifier) {
                return (VisibilityModifier) m;
            }
        }
        return null;
    }

    final boolean containsModifier(Class type) {
        int s = (declarationSpecifiers == null) ? 0 : declarationSpecifiers.size();
        for (int i = 0; i < s; i += 1) {
            if (type.isInstance(declarationSpecifiers.get(i))) {
                return true;
            }
        }
        return false;
    }

    /**
     * Test whether the declaration is abstract.
     */

    protected boolean isAbstract() {
        return containsModifier(Abstract.class);
    }

    /**
     * Test whether the declaration is private.
     */

    protected boolean isPrivate() {
        return containsModifier(Private.class);
    }

    /**
     * Test whether the declaration is protected.
     */

    protected boolean isProtected() {
        return containsModifier(Protected.class);
    }

    /**
     * Test whether the declaration is public.
     */

    protected boolean isPublic() {
        return containsModifier(Public.class);
    }

    /**
     * Test whether the declaration is static.
     */

    protected boolean isStatic() {
        return containsModifier(Static.class);
    }

    /**
     * Test whether the declaration is transient.
     */

    protected boolean isTransient() {
        return containsModifier(Transient.class);
    }

    /**
     * Test whether the declaration is volatile.
     */

    protected boolean isVolatile() {
        return containsModifier(Volatile.class);
    }

    /**
     * Test whether the declaration is strictfp.
     */

    protected boolean isStrictFp() {
        return containsModifier(StrictFp.class);
    }

    /**
     * Test whether the declaration is final.
     */

    protected boolean isFinal() {
        return containsModifier(Final.class);
    }

    /**
     * Test whether the declaration is native.
     */

    protected boolean isNative() {
        return containsModifier(Native.class);
    }

    /**
     * Test whether the declaration is synchronized.
     */

    protected boolean isSynchronized() {
        return containsModifier(Synchronized.class);
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (declarationSpecifiers != null) {
            for (int i = declarationSpecifiers.size() - 1; i >= 0; i -= 1) {
                declarationSpecifiers.get(i).setParent(this);
            }
        }
    }
}
