package org.keyproject.key.api.data;

import org.checkerframework.checker.nullness.qual.Nullable;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
public record NodeDesc(KeyIdentifications.NodeId nodeid, String branchLabel,
                       boolean scriptRuleApplication,
                       @Nullable List<NodeDesc> children
) {
    public NodeDesc(KeyIdentifications.ProofId proofId, int serialNr, String branchLabel, boolean scriptRuleApplication) {
        this(new KeyIdentifications.NodeId(proofId, serialNr), branchLabel, scriptRuleApplication, null);
    }
}
