/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Defines the basic methods and properties each element in the symbolic execution tree model has.
 *
 * @author Martin Hentschel
 */
public interface IExecutionElement {
    /**
     * Returns the {@link ITreeSettings} to use.
     *
     * @return The {@link ITreeSettings} to use.
     */
    ITreeSettings getSettings();

    /**
     * Returns the {@link Services} used by {@link #getProof()}.
     *
     * @return The {@link Services} used by {@link #getProof()}.
     */
    Services getServices();

    /**
     * Returns the {@link InitConfig} used by {@link #getProof()}.
     *
     * @return The {@link InitConfig} used by {@link #getProof()}.
     */
    InitConfig getInitConfig();

    /**
     * Returns the {@link Proof} from which the symbolic execution tree was extracted.
     *
     * @return The {@link Proof} from which the symbolic execution tree was extracted.
     */
    Proof getProof();

    /**
     * Returns the {@link Node} in KeY's proof tree which is represented by this execution tree
     * node.
     *
     * @return The {@link Node} in KeY's proof tree which is represented by this execution tree
     *         node.
     */
    Node getProofNode();

    /**
     * Returns the applied {@link RuleApp}.
     *
     * @return The applied {@link RuleApp}.
     */
    RuleApp getAppliedRuleApp();

    /**
     * Returns the {@link PosInOccurrence} of the modality of interest including updates.
     *
     * @return The {@link PosInOccurrence} of the modality of interest including updates.
     */
    PosInOccurrence getModalityPIO();

    /**
     * Returns the {@link NodeInfo} of {@link #getProofNode()}.
     *
     * @return The {@link NodeInfo} of {@link #getProofNode()}.
     */
    NodeInfo getProofNodeInfo();

    /**
     * Returns a human readable name which describes this element.
     *
     * @return The human readable name which describes this element.
     * @throws ProofInputException Occurred Exception.
     */
    String getName() throws ProofInputException;

    /**
     * Returns a human readable element type name.
     *
     * @return The human readable element type.
     */
    String getElementType();

    /**
     * Checks if the proof is disposed.
     *
     * @return {@code true} proof is disposed, {@code false} proof is not disposed and still valid.
     */
    boolean isDisposed();
}
