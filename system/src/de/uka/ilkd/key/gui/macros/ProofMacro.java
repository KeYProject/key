package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.PosInOccurrence;

public interface ProofMacro {

    public String getName();

    public String getDescription();
    
    public boolean canApplyTo(KeYMediator mediator, PosInOccurrence posInOcc);

    public void applyTo(KeYMediator mediator, PosInOccurrence posInOcc);
}
