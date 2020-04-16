package org.key_project.proofmanagement.check;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.io.consistency.TrivialFileRepo;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.SLEnvInput;
import de.uka.ilkd.key.util.ProgressMonitor;
import org.key_project.proofmanagement.io.LogLevel;

import java.nio.file.Path;
import java.util.*;

/**
 * Checks that there exists a closed proof for every contract.
 * Has to be combined with other checkers to ensure that the proofs are actually consistent
 * as well as correct.
 *
 * @author Wolfram Pfeifer
 */
public class MissingProofsChecker implements Checker {

    @Override
    public void check(List<Path> proofFiles, CheckerData data) throws ProofManagementException {
        data.addCheck("missing");
        data.print("Running missing proofs checker ...");

        ProverService.ensureProofsLoaded(proofFiles, data);
        ProverService.ensureSourceLoaded(data);

        /* check that for all contracts found in Java source (in directory "src" in bundle)
         * there is a closed proof */
        try {
            Profile profile = AbstractProfile.getDefaultProfile();
            ProgressMonitor control = ProgressMonitor.Empty.getInstance();
            ProblemInitializer pi = new ProblemInitializer(control, new Services(profile),
                    new DefaultUserInterfaceControl());
            pi.setFileRepo(new TrivialFileRepo());

            SLEnvInput slenv = data.getSlenv();
            InitConfig ic = pi.prepare(slenv);
            SpecificationRepository specRepo = ic.getServices().getSpecificationRepository();
            Set<Contract> contracts = specRepo.getAllContracts().toSet();
            Set<Contract> copy = new HashSet<>(contracts);

            List<Proof> closedProofs = new ArrayList<>();
            for (CheckerData.ProofEntry pl : data.getProofEntries()) {
                // TODO: proofs can only be closed if replayed
                if (pl.proof != null && pl.proof.closed()) {
                    closedProofs.add(pl.proof);
                }
            }

            // TODO: proof categories? open/closed/started/not-replayed proofs?

            // compare: Is there a closed proof for every contract?
            for (Proof p : closedProofs) {
                SpecificationRepository sr = p.getServices().getSpecificationRepository();
                ContractPO cpo = sr.getPOForProof(p);
                Contract foundContract = cpo.getContract();

                if (foundContract == null) {
                    // should not happen
                    throw new ProofManagementException("Missing contract for proof: " + p.name());
                } else {
                    data.print(LogLevel.INFO, "Contract found for proof: " + p.name());

                    // search for matching contract and delete it (this contract has a proof)
                    Contract rem = null;
                    for (Contract contr : copy) {
                        if (contr.getName().equals(foundContract.getName())) {
                            rem = contr;
                            break;
                        }
                    }
                    if (rem != null) {
                        copy.remove(rem);
                    }
                }
            }

            // report all contracts that are left unproven, store check results in data
            for (Contract c : copy) {
                // TODO: currently contracts from inside java.* package are filtered/ignored
                //  better filter by folder?
                if (c.getName().startsWith("java.")) {
                    data.addUnprovenContract(c, true);
                    data.print(LogLevel.DEBUG, "Ignoring internal contract " + c.getName());
                } else {
                    data.addUnprovenContract(c, false);
                    data.print(LogLevel.WARNING, "Missing proof for contract " + c.getName());
                    data.setConsistent(false); // at least one contract is left unproven!
                }
            }
        } catch (ProofInputException e) {
            throw new ProofManagementException("EnvInput could not be loaded!" + System.lineSeparator()
                + e.getMessage());
        }
    }
}
