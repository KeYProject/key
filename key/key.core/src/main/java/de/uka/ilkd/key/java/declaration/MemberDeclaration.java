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

import de.uka.ilkd.key.java.Declaration;
import de.uka.ilkd.key.java.NonTerminalProgramElement;

/**
 *  Member declaration.
 * taken from COMPOST and changed to achieve an immutable structure
 */

public interface MemberDeclaration extends Declaration, NonTerminalProgramElement {

    /**
     * Test whether the declaration is private.
     */
    boolean isPrivate();

    /**
     * Test whether the declaration is protected.
     */
    boolean isProtected();

    /**
     * Test whether the declaration is public.
     */
    boolean isPublic();

    /**
     * Test whether the declaration is static.
     */
    boolean isStatic();

    /**
     * Test whether the declaration is strictfp.
     */
    boolean isStrictFp();
}