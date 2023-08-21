/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.check;

import java.net.URI;
import java.util.*;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.io.consistency.TrivialFileRepo;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.SLEnvInput;
import de.uka.ilkd.key.util.ProgressMonitor;

import org.key_project.proofmanagement.io.LogLevel;
import org.key_project.proofmanagement.io.ProofBundleHandler;

/**
 * Checks that there exists a proof for every contract.
 * Has to be combined with other checkers to ensure that the proofs are actually replayable
 * as well as closed.
 *
 * @author Wolfram Pfeifer
 */
public class MissingProofsChecker implements Checker {

    @Override
    public void check(ProofBundleHandler pbh, CheckerData data) throws ProofManagementException {
        data.addCheck("missing_proofs");
        data.print("Running missing proofs checker ...");

        KeYFacade.ensureSourceLoaded(data);
        KeYFacade.ensureProofsLoaded(data);

        Profile profile = AbstractProfile.getDefaultProfile();
        ProgressMonitor control = ProgressMonitor.Empty.getInstance();
        ProblemInitializer pi = new ProblemInitializer(control, new Services(profile),
            new DefaultUserInterfaceControl());
        pi.setFileRepo(new TrivialFileRepo());

        SLEnvInput slenv = data.getSlenv();

        /*
         * check that for all contracts found in Java source (in directory "src" in bundle)
         * there is a proof
         */
        try {
            InitConfig ic = pi.prepare(slenv);
            SpecificationRepository specRepo = ic.getServices().getSpecificationRepository();
            Set<Contract> contracts = specRepo.getAllContracts().toSet();

            // Remove all contracts that have a corresponding proof file from set.
            // The proof is not checked to be closed here!
            removeContractsWithProof(contracts, data);

            // report all contracts that are left without proof, store check results in data
            reportContractsWithoutProof(contracts, data);
        } catch (ProofInputException e) {
            throw new ProofManagementException("EnvInput could not be loaded!"
                + System.lineSeparator() + e.getMessage());
        }
    }

    private static void removeContractsWithProof(Set<Contract> contracts, CheckerData data)
            throws ProofManagementException {

        // compare: Is there a proof for every contract?
        for (CheckerData.ProofEntry entry : data.getProofEntries()) {
            Proof p = entry.proof;
            SpecificationRepository sr = p.getServices().getSpecificationRepository();
            ContractPO cpo = sr.getPOForProof(p);
            Contract foundContract = cpo.getContract();

            if (foundContract == null) {
                // should not happen
                throw new ProofManagementException("Missing contract for proof: " + p.name());
            } else {
                // search for matching contract and delete it (this contract has a proof)
                Iterator<Contract> it = contracts.iterator();
                while (it.hasNext()) {
                    Contract c = it.next();
                    if (c.getName().equals(foundContract.getName())) {
                        data.print(LogLevel.INFO, "Proof exists for contract " + c.getName());
                        it.remove();
                    }
                }
            }
        }
    }

    private static void reportContractsWithoutProof(Set<Contract> contracts, CheckerData data) {
        for (Contract c : contracts) {
            // Only contracts defined in files inside src directory of bundle are
            // considered. For other contracts (e.g. from bootclasspath) a message is
            // printed if loglevel is low enough.
            Type type = c.getKJT().getJavaType();
            if (type instanceof TypeDeclaration) {
                TypeDeclaration td = (TypeDeclaration) type;
                PositionInfo positionInfo = td.getPositionInfo();
                URI uri = positionInfo.getURI().orElseThrow().normalize();
                URI srcURI = data.getPbh().getPath("src").toAbsolutePath().normalize().toUri();


                // ignore contracts from files not in src path (e.g. from bootclasspath)
                // (this check works independent from number of slashes in URIs)
                if (srcURI.relativize(uri).isAbsolute()) {
                    data.addContractWithoutProof(c, true);
                    data.print(LogLevel.DEBUG, "Ignoring internal contract " + c.getName());
                    continue;
                }
            }
            data.addContractWithoutProof(c, false);
            data.print(LogLevel.WARNING, "No proof found for contract " + c.getName());
        }
    }
}
