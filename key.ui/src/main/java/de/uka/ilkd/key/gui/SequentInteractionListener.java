package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.pp.PosInSequent;

import java.util.EventListener;

public interface SequentInteractionListener extends EventListener {

    void hover(PosInSequent pos, JTerm t);

    void leaveHover();

    void click(PosInSequent pos, JTerm t);

}