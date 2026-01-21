package de.uka.ilkd.key.java.declaration;

import de.uka.ilkd.key.java.Declaration;
import de.uka.ilkd.key.java.NonTerminalProgramElement;

/**
 * Member declaration. taken from COMPOST and changed to achieve an immutable structure
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
