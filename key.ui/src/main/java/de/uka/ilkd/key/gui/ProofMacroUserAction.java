package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.Proof;

public class ProofMacroUserAction extends ProofModifyingUserAction {
    private KeYMediator mediator;
    private ProofMacro macro;
    private PosInOccurrence pio;

    ProofMacroUserAction(KeYMediator mediator, ProofMacro macro, PosInOccurrence pio, Proof proof) {
        super(mediator, proof);
        this.mediator = mediator;
        this.macro = macro;
        this.pio = pio;
    }

    @Override
    public void apply() {
        if (mediator.isInAutoMode()) {
            return;
        }
        mediator.getUI().getProofControl().runMacro(mediator.getSelectedNode(), macro, pio);
    }

    @Override
    public void undo() {
        super.undo();
    }
}