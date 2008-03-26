// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.declaration;

import de.uka.ilkd.key.java.Declaration;
import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.declaration.modifier.*;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Java declaration.
 * taken from COMPOST and changed to achieve an immutable structure
 */

public abstract class JavaDeclaration extends JavaNonTerminalProgramElement
 implements Declaration {

    /**
     * Modifiers.
     * caches the wrapper for the modifiers. The wrapper is needed to get access
     * to the array without hurting immutabilitiy */
    protected final ArrayOfModifier modArray;

    /**
     *      Java declaration.
     */
    public JavaDeclaration() {
	modArray=null;
    }



    public JavaDeclaration(Modifier[] mods) {
	modArray=new ArrayOfModifier(mods);
    }

    public JavaDeclaration(ArrayOfModifier mods) {
	modArray =  mods;
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes. May
     * include: several Modifier (taken as modifiers of the declaration), 
     * a Comment
     */     
    public JavaDeclaration(ExtList children) {
	super(children);
	modArray=new ArrayOfModifier((Modifier[])children.collect(Modifier.class));
    }


    /**
     *      Get modifiers.
     *      @return the modifier array wrapper.
     */

    public ArrayOfModifier getModifiers() {
        return modArray;
    }

    /**
     *      Returns a Public, Protected, or Private Modifier, if there
     *      is one, null otherwise. A return value of null can usually be
     *      interpreted as package visibility.
     */

    public VisibilityModifier getVisibilityModifier() {
        if (modArray == null) {
            return null;
        }
        for (int i = modArray.size() - 1; i >= 0; i -= 1) {
            Modifier m = modArray.getModifier(i);
            if (m instanceof VisibilityModifier) {
                return (VisibilityModifier)m;
            }
        }
        return null;
    }


    private boolean containsModifier(Class type) {
        int s = (modArray == null) ? 0 : modArray.size();
        for (int i = 0; i < s; i += 1) {
            if (type.isInstance(modArray.getModifier(i))) {
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
     * Test whether the declaration is model (the jml modifier is meant).
     */

    protected boolean isModel() {
        return containsModifier(Model.class);
    }

    /**
     * Test whether the declaration is ghost (the jml modifier is meant).
     */

    protected boolean isGhost() {
        return containsModifier(Ghost.class);
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

}
