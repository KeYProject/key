/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.KeYProjectFile;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.MiscTools;

import java.nio.file.Path;

public final class HeavyweightProject extends LightweightProject {

    HeavyweightProject(Path projectFolder) {
        super(projectFolder);
        Runtime.getRuntime().addShutdownHook(new Thread(this::flushAll));
        /*
         * Runtime.getRuntime().addShutdownHook(new Thread( () -> {
         * loadedProofs.forEach((key, value) -> value.dispose());
         * }
         * ));
         */
    }

    @Override
    public void registerProof(ProofOblInput po, Proof proof) {
        super.registerProof(po, proof);
        if (po instanceof ContractPO cpo) {
            Contract contract = cpo.getContract();
            String proofName = MiscTools.toValidFileName(contract.getName()) + ".proof";
            Path proofPath = initialPath.resolve(proofDir).resolve(proofName);
            storedProofs.put(contract, proofPath);
            proof.addProofDisposedListener(this);
        }
    }

    @Override
    public void flushAll() {
        flush();
        loadedProofs.entrySet().forEach(e -> writeProofToDisk(e.getValue()));
    }

    @Override
    public void flushSingleProof(Proof proof) {
        writeProofToDisk(proof);
    }

    @Override
    public void proofDisposing(ProofDisposedEvent e) {
        super.proofDisposing(e);
        flush();
    }
}
