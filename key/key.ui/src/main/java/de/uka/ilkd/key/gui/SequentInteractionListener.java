package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.PosInSequent;

import java.util.EventListener;

public interface SequentInteractionListener extends EventListener {

    void hover(PosInSequent pos, Term t);

    void leaveHover();

    void click(PosInSequent pos, Term t);

}
