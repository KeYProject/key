package de.uka.ilkd.key.java.ast.abstraction;

import de.uka.ilkd.key.java.ast.NamedModelElement;

/**
 * An entity of the program meta model.
 *
 * @author AL
 * @author RN
 */
public interface ProgramModelElement extends NamedModelElement {

    /**
     * Returns the maximal expanded name including all applicable qualifiers.
     *
     * @return the full name of this program model element.
     */
    String getFullName();


}
