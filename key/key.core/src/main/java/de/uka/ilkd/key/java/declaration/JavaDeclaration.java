// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.declaration;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Declaration;
import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.declaration.modifier.Abstract;
import de.uka.ilkd.key.java.declaration.modifier.Final;
import de.uka.ilkd.key.java.declaration.modifier.Ghost;
import de.uka.ilkd.key.java.declaration.modifier.Model;
import de.uka.ilkd.key.java.declaration.modifier.Native;
import de.uka.ilkd.key.java.declaration.modifier.NoState;
import de.uka.ilkd.key.java.declaration.modifier.Private;
import de.uka.ilkd.key.java.declaration.modifier.Protected;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.declaration.modifier.Static;
import de.uka.ilkd.key.java.declaration.modifier.StrictFp;
import de.uka.ilkd.key.java.declaration.modifier.Synchronized;
import de.uka.ilkd.key.java.declaration.modifier.Transient;
import de.uka.ilkd.key.java.declaration.modifier.TwoState;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.declaration.modifier.Volatile;

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
    protected final ImmutableArray<Modifier> modArray;

    
    /**
     *      Java declaration.
     */
    public JavaDeclaration() {
	modArray = null;
    }


    public JavaDeclaration(Modifier[] mods) {
	modArray = new ImmutableArray<Modifier>(mods);
    }

    
    public JavaDeclaration(ImmutableArray<Modifier> mods) {
	modArray = mods;
    }

    
    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes. May
     * include: several Modifier (taken as modifiers of the declaration), 
     * a Comment
     */     
    public JavaDeclaration(ExtList children) {
	super(children);
	modArray = new ImmutableArray<Modifier>(children.collect(Modifier.class));
    }


    /**
     *      Get modifiers.
     *      @return the modifier array wrapper.
     */
    public ImmutableArray<Modifier> getModifiers() {
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
            Modifier m = modArray.get(i);
            if (m instanceof VisibilityModifier) {
                return (VisibilityModifier)m;
            }
        }
        return null;
    }


    private boolean containsModifier(Class<?> type) {
        int s = (modArray == null) ? 0 : modArray.size();
        for (int i = 0; i < s; i += 1) {
            if (type.isInstance(modArray.get(i))) {
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
     * Get the state count of the declaration
     */
    protected int getStateCount() {
        if(containsModifier(TwoState.class)) { return 2; }
        if(containsModifier(NoState.class)) { return 0; }
        return 1;
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
