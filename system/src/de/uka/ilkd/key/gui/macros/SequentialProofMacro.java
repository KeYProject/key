package de.uka.ilkd.key.gui.macros;

import javax.swing.SwingUtilities;

import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.ProofEvent;

public abstract class SequentialProofMacro implements ProofMacro {
    
    private ProofMacro[] proofMacros = null;

    protected abstract ProofMacro[] createProofMacroArray();

    @Override 
    public boolean canApplyTo(KeYMediator mediator, PosInOccurrence posInOcc) {
        return getProofMacros()[0].canApplyTo(mediator, posInOcc);
    }

    @Override 
    public void applyTo(final KeYMediator mediator, final PosInOccurrence posInOcc) {
        mediator.addAutoModeListener(new AutoModeListener() {

            private int curMacro = 0;
            private ProofMacro[] proofMacros = getProofMacros();

            @Override 
            public void autoModeStopped(ProofEvent e) {
                curMacro ++;
                if(curMacro >= proofMacros.length) {
                    mediator.removeAutoModeListener(this);
                } else {
                    assert SwingUtilities.isEventDispatchThread();
                    SwingUtilities.invokeLater(new Runnable() {
                        @Override public void run() {
                            proofMacros[curMacro].applyTo(mediator, posInOcc);
                        }
                    });
                }
            }

            @Override 
            public void autoModeStarted(ProofEvent e) {
            }
        });

        getProofMacros()[0].applyTo(mediator, posInOcc);
    }

    /**
     * @return the proofMacros
     */
    public ProofMacro[] getProofMacros() {
        if(proofMacros == null) {
            this.proofMacros = createProofMacroArray();
            assert proofMacros != null;
            assert proofMacros.length > 0;
        }
        return proofMacros;
    }


}
