package de.uka.ilkd.key.gui;
import de.uka.ilkd.key.logic.Term;

import java.util.EventListener;
import java.util.EventObject;

public interface SequentInteractionListener extends EventListener {

    void hover(Term t);

    void leaveHover();

}