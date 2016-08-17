package de.uka.ilkd.key.ui;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.Contract;
import org.key_project.util.collection.ImmutableSet;

/**
 * Created by weigl on 17.08.16.
 */
public class AutoProofObligationSelector
        extends ConsoleProofObligationSelector {
    public AutoProofObligationSelector(ConsoleUserInterfaceControl ui, InitConfig initConfig) {
        super(ui, initConfig);

        printAvailableProofObligations();
    }

    @Override
    public boolean selectProofObligation() {
        //TODO write code to select the non-interference proof.
        for (Contract c : contracts) {

        }
        return false;
    }
}
