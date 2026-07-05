/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProofOblInput;

import org.key_project.logic.Name;

/**
 * Proof obligation input for the soundness proof of a taclet created by a
 * {@link LemmaTacletGenerator}. The proof obligation itself is created eagerly when the lemma is
 * generated (see {@link GeneratedLemmaRegistry}); this class merely identifies it towards the
 * proof environment.
 */
public class GeneratedLemmaPO implements ProofOblInput {

    private final Name tacletName;
    private final ProofAggregate po;

    public GeneratedLemmaPO(Name tacletName, ProofAggregate po) {
        this.tacletName = tacletName;
        this.po = po;
    }

    @Override
    public String name() {
        return "Taclet: " + tacletName;
    }

    @Override
    public void readProblem() {
        // the proof obligation has already been constructed
    }

    @Override
    public ProofAggregate getPO() {
        return po;
    }

    @Override
    public boolean implies(ProofOblInput po) {
        return this == po;
    }

    @Override
    public KeYJavaType getContainerType() {
        return null;
    }
}
