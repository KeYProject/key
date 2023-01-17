package de.uka.ilkd.key.java.declaration.modifier;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.declaration.Modifier;


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
