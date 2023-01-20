package de.uka.ilkd.key.java;

/**
 * A model element that carries a name.
 */
public interface NamedModelElement extends ModelElement {

    /**
     * Return the name of the model element.
     *
     * @return the name of the model element.
     */
    String getName();

}
