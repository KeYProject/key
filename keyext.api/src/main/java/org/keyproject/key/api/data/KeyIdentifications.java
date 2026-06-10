/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

import java.util.Objects;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import java.util.HashMap;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (29.10.23)
 */
public class KeyIdentifications {
    private final Map<EnvironmentId, KeyEnvironmentContainer> mapEnv = new HashMap<>(16);

    public KeyEnvironmentContainer getContainer(EnvironmentId environmentId) {
        return Objects.requireNonNull(mapEnv.get(environmentId),
            "Could not find environment for id" + environmentId);
    }

    public ProofContainer getContainer(ProofId proofId) {
        return Objects.requireNonNull(getContainer(proofId.env()).mapProof.get(proofId),
            "Could not find proof for id" + proofId);
    }

    public KeYEnvironment<?> find(EnvironmentId envid) {
        return getContainer(envid).env;
    }

    public Proof find(ProofId proofId) {
        return getContainer(proofId).wProof;
    }

    public NodeText find(NodeTextId nodeTextId) {
        return Objects.requireNonNull(
            getContainer(nodeTextId.nodeId().proofId()).mapGoalText.get(nodeTextId),
            "Could not find a print-out with the id " + nodeTextId);
    }

    public void dispose(NodeTextId nodeTextId) {
        var c = getContainer(nodeTextId.nodeId().proofId());
        c.mapGoalText.remove(nodeTextId);
    }

    public void dispose(ProofId id) {
        var c = getContainer(id);
        getContainer(id.env).mapProof.remove(id);
        c.dispose();
    }

    public void dispose(EnvironmentId id) {
        var c = getContainer(id);
        c.mapProof.forEach(((proofId, proofContainer) -> this.dispose(proofId)));
        mapEnv.remove(id);
        c.dispose();
    }

    public Node find(NodeId nodeId) {
        Proof p = find(nodeId.proofId);
        var id = Integer.parseInt(nodeId.nodeId());
        var opt = p.findAny(it -> it.serialNr() == id);
        return Objects.requireNonNull(opt, "Could not find node with serialNr  " + nodeId.nodeId);
    }

    public ProofId register(EnvironmentId envId, Proof proof) {
        var id = new ProofId(envId, proof.name().toString());
        getContainer(envId).mapProof.put(id, new ProofContainer(proof));
        return id;
    }

    public void register(NodeTextId nodeId, NodeText nodeText) {
        var c = getContainer(nodeId.nodeId().proofId());
        c.mapGoalText().put(nodeId, nodeText);

    }

    public EnvironmentId register(EnvironmentId envId, KeYEnvironment<?> env) {
        mapEnv.put(envId, new KeyEnvironmentContainer(env));
        return envId;
    }

    public ProofId register(ProofId proofId, Proof proof) {
        getContainer(proofId.env()).mapProof.put(proofId, new ProofContainer(proof));
        return proofId;
    }

    /// All proofs currently registered (across all environments).
    /// Used to let a reconnecting client resume existing proofs.
    public java.util.List<ProofId> allProofIds() {
        var result = new java.util.ArrayList<ProofId>();
        mapEnv.forEach((envId, c) -> result.addAll(c.mapProof().keySet()));
        return result;
    }


    /**
     * @author Alexander Weigl
     * @version 1 (28.10.23)
     */
    public record EnvironmentId(String envId) implements KeYDataTransferObject {
    }

    /**
     * @author Alexander Weigl
     * @version 1 (28.10.23)
     */
    public record ContractId(EnvironmentId envId, String contractId)
            implements KeYDataTransferObject {
    }

    /**
     * @author Alexander Weigl
     * @version 1 (29.10.23)
     */
    public record NodeId(ProofId proofId, String nodeId) implements KeYDataTransferObject {
    }

    public record ProofId(EnvironmentId env, String proofId) implements KeYDataTransferObject {
    }

    /**
     * @author Alexander Weigl
     * @version 1 (29.10.23)
     */
    public record NodeTextId(NodeId nodeId, int nodeTextId) implements KeYDataTransferObject {
    }


    /**
     * @author Alexander Weigl
     * @version 1 (13.10.23)
     */
    public record TermActionId(NodeTextId nodeTextId, String pio, String id, int caretPos)
            implements KeYDataTransferObject {
    }

    /**
     * @author Alexander Weigl
     * @version 1 (13.10.23)
     */
    public record TreeNodeId(String id) implements KeYDataTransferObject {
    }


    /**
     * @author Alexander Weigl
     * @version 1 (28.10.23)
     */
    public record KeyEnvironmentContainer(KeYEnvironment<?> env,
            Map<ProofId, ProofContainer> mapProof) {

        public KeyEnvironmentContainer(KeYEnvironment<?> env) {
            this(env, new HashMap<>(1));
        }

        void dispose() {
            mapProof.clear();
            env.dispose();
        }
    }

    private record ProofContainer(Proof wProof,
            Map<NodeId, Node> mapNode,
            Map<TreeNodeId, TreeNodeDesc> mapTreeNode,
            // A plain Map, NOT a BiMap: values are records with structural
            // equality, and printing the same goal twice (e.g. pure prints,
            // where the position table is null) yields equal values.
            Map<NodeTextId, NodeText> mapGoalText) {
        public ProofContainer(Proof proof) {
            this(proof, new HashMap<>(16), new HashMap<>(16), new HashMap<>(16));
        }

        void dispose() {
            mapNode.clear();
        }
    }
}
