package de.uka.ilkd.key.java.recoderext;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;


public class Ghost extends Modifier {

    /**
     *
     */
    private static final long serialVersionUID = -4883937081008486072L;


    public Ghost() {
    }


    protected Ghost(Ghost proto) {
        super(proto);
    }


    public Ghost deepClone() {
        return new Ghost(this);
    }


    public void accept(SourceVisitor v) {
    }
}
