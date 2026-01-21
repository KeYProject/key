package de.uka.ilkd.key.java.abstraction;

import de.uka.ilkd.key.java.expression.Literal;

/**
 * A program model element representing types.
 *
 * @author AL
 * @author RN
 */
public interface Type extends ProgramModelElement {

    /**
     * returns the default value of the given type according to JLS Sect. 4.5.5
     *
     * @return the default value of the given type according to JLS Sect. 4.5.5
     */
    Literal getDefaultValue();

}
