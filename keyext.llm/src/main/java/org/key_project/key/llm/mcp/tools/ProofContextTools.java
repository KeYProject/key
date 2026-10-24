/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.util.List;

import org.key_project.key.llm.ProofContextCollector;
import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.AgentToolProvider;
import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.ProofSelector;
import org.key_project.key.llm.mcp.ToolCategory;

/**
 * The {@code get_proof_context} tool: the current proof state as a text block (name, open/closed
 * goals, current sequent, open goal sequents, model info and the computation path).
 *
 * @author Alexander Weigl
 */
public final class ProofContextTools implements AgentToolProvider {
    @Override
    public List<AgentTool> get() {
        return List.of(AgentTool.tool(KeYAgentTools.TOOL_GET_PROOF_CONTEXT, ToolCategory.PROOF,
            "Returns a text block describing the current proof state: name, open/closed goals,"
                + " the current sequent, open goal sequents, model info and the computation path"
                + " from the root to the selected node.",
            AgentTool.schema("include_compute_path",
                JsonSchema.builder().withType("boolean")
                        .withDescription("include the computation path")
                        .build()),
            args -> {
                var proof = ProofSelector.selectedProof();
                if (proof == null) {
                    return "(no proof selected)";
                }
                var node = ProofSelector.selectedNode();
                return ProofContextCollector.contextBlock(proof, node);
            }));
    }
}
