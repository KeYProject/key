package de.uka.ilkd.key.java.declaration.modifier;

import de.uka.ilkd.key.java.declaration.Modifier;

import org.key_project.util.ExtList;


/**
 * The JML modifier "model".
 */
public class Model extends Modifier {

    public Model() {}


    public Model(ExtList children) {
        super(children);
    }


    protected String getSymbol() {
        return "model";
    }
}
