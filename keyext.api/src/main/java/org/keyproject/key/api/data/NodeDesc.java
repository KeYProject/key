/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

import java.util.List;

import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
public record NodeDesc(KeyIdentifications.NodeId nodeid,
                       String branchLabel,
                       boolean scriptRuleApplication,
                       @Nullable List<NodeDesc> children,
                       String description
) implements KeYDataTransferObject {
    public NodeDesc(KeyIdentifications.ProofId proofId, int serialNr, String branchLabel, boolean scriptRuleApplication, String description) {
        this(new KeyIdentifications.NodeId(proofId, serialNr), branchLabel, scriptRuleApplication, null, description);
    }
}
