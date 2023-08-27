/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

import recoder.ModelException;
import recoder.abstraction.ProgramModelElement;
import recoder.java.Declaration;

/**
 * Exception indicating that a particular declaration is ambiguous.
 *
 * @author AL
 */
public class AmbiguousDeclarationException extends ModelException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -412059506748522072L;

    private Declaration declaration;

    private ProgramModelElement conflictingElement;

    /**
     * Empty constructor.
     */
    public AmbiguousDeclarationException() {
        // Empty constructor.
    }

    /**
     * Constructor without explanation text.
     *
     * @param declaration the declaration found to be ambiguous.
     * @param conflictingElement the alternative declaration, found earlier.
     */
    public AmbiguousDeclarationException(Declaration declaration,
            ProgramModelElement conflictingElement) {
        this.declaration = declaration;
        this.conflictingElement = conflictingElement;
    }

    /**
     * Constructor with an explanation text.
     *
     * @param s an explanation.
     * @param declaration the declaration found to be ambiguous.
     * @param conflictingElement the alternative declaration, found earlier.
     */
    public AmbiguousDeclarationException(String s, Declaration declaration,
            ProgramModelElement conflictingElement) {
        super(s);
        this.declaration = declaration;
        this.conflictingElement = conflictingElement;
    }

    /**
     * Returns the declaration that was found ambiguous.
     */
    public Declaration getAmbiguousDeclaration() {
        return declaration;
    }

    /**
     * Returns the conflicting element.
     */
    public ProgramModelElement getConflictingElement() {
        return conflictingElement;
    }

}
