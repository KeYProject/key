/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.mgt;

import java.util.EventObject;

import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import org.jspecify.annotations.Nullable;

public class ProofEnvironmentEvent extends EventObject {
    private final @Nullable ProofOblInput po;
    private final ProofAggregate proofList;

    public ProofEnvironmentEvent(ProofEnvironment source,
                                 @Nullable ProofOblInput po,
                                 ProofAggregate proofList) {
        super(source);
        this.po = po;
        this.proofList = proofList;
    }


    @Override
    public ProofEnvironment getSource() {
        return (ProofEnvironment) super.getSource();
    }


    public ProofAggregate getProofList() {
        return proofList;
    }


    public @Nullable ProofOblInput getPo() {
        return po;
    }



}
