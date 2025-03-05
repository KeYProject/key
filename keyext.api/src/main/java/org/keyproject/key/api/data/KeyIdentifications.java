/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

import java.lang.ref.WeakReference;
import java.util.Objects;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import org.jspecify.annotations.NonNull;
import org.keyproject.key.api.internal.NodeText;

/**
 * @author Alexander Weigl
 * @version 1 (29.10.23)
 */
public class KeyIdentifications {
    private final BiMap<EnvironmentId, KeyEnvironmentContainer> mapEnv = HashBiMap.create(16);

    public KeyEnvironmentContainer getContainer(EnvironmentId environmentId) {
        return Objects.requireNonNull(mapEnv.get(environmentId),
            "Could not find environment for id" + environmentId);
    }

    public ProofContainer getContainer(ProofId proofId) {
        return Objects.requireNonNull(getContainer(proofId.env()).mapProof.get(proofId),
            "Could not find proof for id" + proofId);
    }

    public KeYEnvironment<?> find(EnvironmentId envid) {
        return Objects.requireNonNull(getContainer(envid).env.get(),
            "Environment was removed by gc");
    }

    @NonNull
    public Proof find(ProofId proofId) {
        return Objects.requireNonNull(getContainer(proofId).wProof.get(),
            "Could not find a proof for id " + proofId);
    }

    @NonNull
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
        @NonNull
        Proof p = find(nodeId.proofId);
        var opt = p.findAny(it -> it.serialNr() == nodeId.nodeId());
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


    /**
     * @author Alexander Weigl
     * @version 1 (28.10.23)
     */
    public record EnvironmentId(String envId) {
    }

    /**
     * @author Alexander Weigl
     * @version 1 (28.10.23)
     */
    public record ContractId(EnvironmentId envId, String contractId) {
    }

    /**
     * @author Alexander Weigl
     * @version 1 (29.10.23)
     */
    public record NodeId(ProofId proofId, int nodeId) {
    }

    public record ProofId(EnvironmentId env, String proofId) {
    }

    /**
     * @author Alexander Weigl
     * @version 1 (29.10.23)
     */
    public record NodeTextId(NodeId nodeId, int nodeTextId) {
    }


    /**
     * @author Alexander Weigl
     * @version 1 (13.10.23)
     */
    public record TermActionId(NodeId nodeId, String pio, String id) {
    }

    /**
     * @author Alexander Weigl
     * @version 1 (13.10.23)
     */
    public record TreeNodeId(String id) {
    }


    /**
     * @author Alexander Weigl
     * @version 1 (28.10.23)
     */
    public record KeyEnvironmentContainer(WeakReference<KeYEnvironment<?>> env,
                                          BiMap<ProofId, ProofContainer> mapProof
    ) {

        public KeyEnvironmentContainer(KeYEnvironment<?> env) {
            this(new WeakReference<>(env), HashBiMap.create(1));
        }

        void dispose() {
            env.clear();
            mapProof.clear();
        }
    }

    private record ProofContainer(WeakReference<Proof> wProof,
                                  BiMap<NodeId, WeakReference<Node>> mapNode,
                                  BiMap<TreeNodeId, WeakReference<TreeNodeDesc>> mapTreeNode,
                                  BiMap<NodeTextId, NodeText> mapGoalText
    ) {
        public ProofContainer(Proof proof) {
            this(new WeakReference<>(proof), HashBiMap.create(16), HashBiMap.create(16), HashBiMap.create(16));
        }

        void dispose() {
            mapNode.clear();
        }
    }
}
