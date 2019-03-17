package de.uka.ilkd.key.ui;

import de.uka.ilkd.key.informationflow.macros.FullInformationFlowAutoPilotMacro;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.speclang.Contract;

/**
 * weigl on 17.08.16.
 */
public class NIProofObligationSelector extends ConsoleProofObligationSelector {
    public NIProofObligationSelector(ConsoleUserInterfaceControl ui, InitConfig initConfig) {
        super(ui, initConfig);
    }

    @Override
    public boolean selectProofObligation() {
        /**
         * I feel so sorry for you. You dug through a huge pile of crap
         * until you have reached this comment. And some of this crappy
         * code is from me. Sorry for that. But you can surely believe me,
         * when I say it only get worse.
         */


        for (Contract c : contracts) {
            if (c.getDisplayName().startsWith("Non-interference")) {
                try {
                    System.out.println("Selecting: " + c.getDisplayName());
                    ProofOblInput obl = c.createProofObl(initConfig, c);
                    ProblemInitializer pi = new ProblemInitializer(ui, initConfig.getServices(), ui);
                    ProofAggregate pl = pi.startProver(initConfig, obl);
                    ProofEnvironment env = ui.createProofEnvironmentAndRegisterProof(obl, pl, initConfig);
                    System.out.println(env.description());
                    ui.getMediator().setInteractive(false);

                    // is there no other way to load a proof?
                    ui.getProofControl().startAndWaitForAutoMode(pl.getFirstProof());

                    ui.getProofControl().runMacro(pl.getFirstProof().root(),
                            new FullInformationFlowAutoPilotMacro(),
                            null// whether this is a good idea? The debugger will tell...
                    );


                    System.out.println(pl.getFirstProof());
                    //ui.saveProof(true, pl.getFirstProof(), null);
                } catch (ProofInputException e) {
                    e.printStackTrace();
                }
            }
        }

        System.exit(0);

        if (ui.allProofsSuccessful) {

        }

        return true;
    }
}
