package de.uka.ilkd.key.java.declaration.modifier;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.declaration.Modifier;


/**
 * The JML modifier "ghost".
 */
public class Ghost extends Modifier {

    public Ghost() {}


    public Ghost(ExtList children) {
        super(children);
    }


    protected String getSymbol() {
        return "ghost";
    }
}
