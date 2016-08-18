package de.uka.ilkd.key.ui;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.proof.init.*;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.KeYTypeUtil;

public class ConsoleProofObligationSelector implements ProofObligationSelector{

    public static final String TAB = "   ";

    private KeYMediator mediator;
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
        ImmutableSet<Contract> contracts = initConfig.getServices().getSpecificationRepository().getAllContracts();
        this.contracts = new ArrayList<Contract>();
        //int i = 0;

        for (Contract c : contracts) {

            if (KeYTypeUtil.isLibraryClass(c.getKJT())) {
                continue;
            }

            this.contracts.add(c);
        }
    }


    protected void printAvailableProofObligations() {
        System.out.println("Available Contracts: ");
        for (int i = 0; i < contracts.size(); i++) {
            printContract(i);
        }
    }

    private void printContract(int i) {
        System.out.println("Contract " + i + ":");
        System.out.println(TAB + "Method: " + contracts.get(i).getTarget().name());
        System.out.println(TAB + "PO:" + contracts.get(i).getDisplayName());
    }

    protected ProofOblInput createPOForSelectedContract() {
        final Contract contract = selectContract();
        System.out.println("Contract: " + contract);
        return contract == null
                ? null
                : contract.createProofObl(initConfig, contract);
    }

    protected void findOrStartProof(ProofOblInput po) {


        Proof proof = findPreferablyClosedProof(po);

        //System.out.println("Proof: "+proof);
        if (proof == null) {
            ProblemInitializer pi =
                    new ProblemInitializer(ui, initConfig.getServices(), ui);
            try {

                final ProofAggregate pl = pi.startProver(initConfig, po);

                ui.createProofEnvironmentAndRegisterProof(po, pl, initConfig);

            } catch (ProofInputException exc) {
                exc.printStackTrace();
            }
        } else {
            mediator.setProof(proof);
        }


    }

    private Proof findPreferablyClosedProof(ProofOblInput po) {

        ImmutableSet<Proof> proofs = initConfig.getServices().getSpecificationRepository().getProofs(po);

        //no proofs?
        if (proofs.isEmpty()) {
            return null;
        }

        //try to find closed proof
        for (Proof proof : proofs) {
            if (proof.mgt().getStatus().getProofClosed()) {
                return proof;
            }
        }

        //just take any proof
        return proofs.iterator().next();
    }

    public boolean selectProofObligation() {
        ProofOblInput po = createPOForSelectedContract();
        //System.out.println("PO: "+po.getPO().getProofs().length);
        findOrStartProof(po);
        return true;
    }


    private Contract selectContract() {
        printAvailableProofObligations();

        System.out.println("Choose PO, enter number between 0 and " + (contracts.size() - 1));
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
                System.out.println("Contract number out of range!");

            } catch (NumberFormatException e) {
                System.out.println("NumberFormatException!");
            } catch (IOException e) {
                System.out.println("IOException!");
            }
        }
        return -1;
    }

    private int readInt() throws NumberFormatException, IOException {
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
        int result = Integer.parseInt(br.readLine());
        return result;
    }


}
