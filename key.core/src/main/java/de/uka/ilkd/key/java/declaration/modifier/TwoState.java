package de.uka.ilkd.key.java.declaration.modifier;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.declaration.Modifier;


/**
 * The JML modifier "two_state".
 */
public class TwoState extends Modifier {

    public TwoState() {}


    public TwoState(ExtList children) {
        super(children);
    }


    protected String getSymbol() {
        return "two_state";
    }
}
