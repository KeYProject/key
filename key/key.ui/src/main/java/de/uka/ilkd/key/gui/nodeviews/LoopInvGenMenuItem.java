package de.uka.ilkd.key.gui.nodeviews;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.loopinvgen.LIGNew;
import de.uka.ilkd.key.loopinvgen.LoopInvariantGenerationResult;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.io.ProofSaver;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

public class LoopInvGenMenuItem extends JMenuItem {
    private final KeYMediator mediator;
    private final PosInSequent posInSequent;

    public LoopInvGenMenuItem(KeYMediator mediator, PosInSequent posInSequent) {
        super("LoopInvGeneration");
        this.mediator = mediator;
        this.posInSequent = posInSequent;
        addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                PosInOccurrence pos = posInSequent.getPosInOccurrence();
                System.out.println(ProofSaver.printAnything(pos.subTerm(), mediator.getServices()));
                System.out.println(pos.isInAntec() + ": " + pos.posInTerm());

                final LIGNew loopInvGenerator = new LIGNew(mediator.getSelectedGoal().sequent(), mediator.getServices());
                LoopInvariantGenerationResult result = loopInvGenerator.generate();
                System.out.println(result.toString());
            }
        });
    }
}
