package de.uka.ilkd.key.ui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.KeYTypeUtil;
import org.key_project.util.collection.ImmutableSet;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

public class ConsoleProofObligationSelector implements ProofObligationSelector {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(ConsoleProofObligationSelector.class);

    public static final String TAB = "   ";

    private final KeYMediator mediator;
    protected InitConfig initConfig;
    protected ConsoleUserInterfaceControl ui;

    protected List<Contract> contracts;

    public ConsoleProofObligationSelector(ConsoleUserInterfaceControl ui, InitConfig initConfig) {
        this.ui = ui;
        this.mediator = ui.getMediator();

        this.initConfig = initConfig;
        initializeContractsArray();
    }

    private void initializeContractsArray() {
        ImmutableSet<Contract> contracts =
            initConfig.getServices().getSpecificationRepository().getAllContracts();
        this.contracts = new ArrayList<>();
        // int i = 0;

        for (Contract c : contracts) {

            if (KeYTypeUtil.isLibraryClass(c.getKJT())) {
                continue;
            }

            this.contracts.add(c);
        }
    }


    protected void printAvailableProofObligations() {
        LOGGER.info("Available Contracts: ");
        for (int i = 0; i < contracts.size(); i++) {
            printContract(i);
        }
    }

    private void printContract(int i) {
        LOGGER.info("Contract " + i + ":");
        LOGGER.info(TAB + "Method: " + contracts.get(i).getTarget().name());
        LOGGER.info(TAB + "PO:" + contracts.get(i).getDisplayName());
    }

    protected ProofOblInput createPOForSelectedContract() {
        final Contract contract = selectContract();
        LOGGER.info("Contract: " + contract);
        return contract == null ? null : contract.createProofObl(initConfig, contract);
    }

    protected void findOrStartProof(ProofOblInput po) {


        Proof proof = findPreferablyClosedProof(po);

        // LOGGER.info("Proof: "+proof);
        if (proof == null) {
            ProblemInitializer pi = new ProblemInitializer(ui, initConfig.getServices(), ui);
            try {

                final ProofAggregate pl = pi.startProver(initConfig, po);

                ui.createProofEnvironmentAndRegisterProof(po, pl, initConfig);

                mediator.setProof(pl.getFirstProof());

            } catch (ProofInputException exc) {
                exc.printStackTrace();
            }
        } else {
            mediator.setProof(proof);
        }


    }

    private Proof findPreferablyClosedProof(ProofOblInput po) {
        ImmutableSet<Proof> proofs =
            initConfig.getServices().getSpecificationRepository().getProofs(po);

        // no proofs?
        if (proofs.isEmpty()) {
            return null;
        }

        // try to find closed proof
        for (Proof proof : proofs) {
            if (proof.mgt().getStatus().getProofClosed()) {
                return proof;
            }
        }

        // just take any proof
        return proofs.iterator().next();
    }

    public boolean selectProofObligation() {
        ProofOblInput po = createPOForSelectedContract();
        // LOGGER.info("PO: "+po.getPO().getProofs().length);
        findOrStartProof(po);
        return true;
    }


    private Contract selectContract() {
        printAvailableProofObligations();

        LOGGER.info("Choose PO, enter number between 0 and " + (contracts.size() - 1));
        int cNr = readContractNumber();
        return contracts.get(cNr);


    }

    private int readContractNumber() {
        int i = -1;
        while (i == -1) {
            try {
                System.out.print("PO nr: ");
                i = readInt();
                if (i >= 0 && i < contracts.size()) {
                    return i;
                }
                i = -1;
                LOGGER.error("Contract number out of range!");
            } catch (NumberFormatException e) {
                LOGGER.info("NumberFormatException!", e);
            } catch (IOException e) {
                LOGGER.error("IOException!", e);
            }
        }
        return -1;
    }

    private int readInt() throws NumberFormatException, IOException {
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
        return Integer.parseInt(br.readLine());
    }


}
