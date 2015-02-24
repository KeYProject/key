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

package de.uka.ilkd.key.java.declaration.modifier;

import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.util.ExtList;


/**
 *  Visibility modifier.
 *  Public, protected, and private modifiers are represented by instances of respective subclasses.
 *  Beware: package-privacy is represented by <code>null</code>!
 *  For comparison of modifiers, please use the static methods of this class instead of <code>instanceof</code>.
 *  @author <TT>AutoDoc</TT>
 */

public abstract class VisibilityModifier 
    extends Modifier implements Comparable<VisibilityModifier>{

    public VisibilityModifier() {
    }


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     *  May contain: Comments
     */
    public VisibilityModifier(ExtList children) {
	super(children);
    }

    /** Whether it represents a <code>public</code> modifier. */
    public static boolean isPublic (VisibilityModifier vm){
        assert sane(vm) : "Unknown visibility modifier: "+vm;
        return vm != null && vm instanceof Public;
    }
    
    /** Whether it represents at least a <code>protected</code> modifier. */
    public static boolean allowsInheritance (VisibilityModifier vm){
        assert sane(vm) : "Unknown visibility modifier: "+vm;
        return vm != null && (vm instanceof Public || vm instanceof Protected);
    }
    
    /** Whether it represents at least default (package-private) visibility. */
    public static boolean isPackageVisible (VisibilityModifier vm){
        assert sane(vm) : "Unknown visibility modifier: "+vm;
        return vm == null || vm instanceof Public || vm instanceof Protected;
    }
    
    /** Whether it represents a <code>private</code> modifier. */
    public static boolean isPrivate (VisibilityModifier vm){
        assert sane(vm) : "Unknown visibility modifier: "+vm;
        return vm  != null && vm instanceof Private;
    }
    
    private static boolean sane (VisibilityModifier vm){
        return vm == null || vm instanceof Public || vm instanceof Protected || vm instanceof Private;
    }
}