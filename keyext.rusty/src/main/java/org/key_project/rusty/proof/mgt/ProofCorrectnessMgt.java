/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.mgt;

import java.util.LinkedHashSet;
import java.util.Set;

import org.key_project.rusty.proof.Proof;
import org.key_project.rusty.rule.RuleApp;
import org.key_project.rusty.speclang.Contract;
import org.key_project.util.collection.ImmutableList;

public final class ProofCorrectnessMgt {
    private final Proof proof;
    private final SpecificationRepository specRepos;

    private final Set<RuleApp> cachedRuleApps = new LinkedHashSet<>();
    private ProofStatus proofStatus = ProofStatus.OPEN;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public ProofCorrectnessMgt(Proof p) {
        this.proof = p;
        this.specRepos = p.getServices().getSpecificationRepository();
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------


    private boolean allHaveMeasuredBy(ImmutableList<Contract> contracts) {
        for (Contract contract : contracts) {
            if (!contract.hasMby()) {
                return false;
            }
        }
        return true;
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    public RuleJustification getJustification(RuleApp r) {
        return proof.getInitConfig().getJustifInfo().getJustification(r, proof.getServices());
    }

    /**
     * Tells whether a contract for the passed target may be applied in the passed goal without
     * creating circular dependencies.
     */
    public boolean isContractApplicable(Contract contract) {
        return true;
    }
}
