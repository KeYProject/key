package de.uka.ilkd.key.java.ast.declaration.modifier;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.declaration.Modifier;


/**
 * The JML modifier "two_state".
 */
public class TwoState extends Modifier {

    public TwoState() {}


    public TwoState(PositionInfo pi, List<Comment> c) {
        super(pi, c);
    }


    protected String getSymbol() {
        return "two_state";
    }
}
