/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.gui.MainWindow;

import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.AgentToolProvider;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.ProofSelector;

/**
 * The {@code list_proofs} tool: enumerates the currently open proofs with an identifier (name or
 * index) that the taclet tools accept in their optional {@code proof} parameter.
 *
 * @author Alexander Weigl
 */
public final class ProofListTools implements AgentToolProvider {
    @Override
    public List<AgentTool> get() {
        return List.of(AgentTool.tool(KeYAgentTools.TOOL_LIST_PROOFS,
            "Lists all currently open proofs with an identifier (name or index). Pass the"
                + " identifier as the optional 'proof' parameter of the taclet tools"
                + " (list_taclets, list_taclet_options, export_taclet, add_taclet,"
                + " remove_taclet); omitting it targets the currently selected proof.",
            ProofListTools::listProofs));
    }

    private static String listProofs(Map<String, Object> args) {
        var mediator = MainWindow.getInstance() == null ? null
                : MainWindow.getInstance().getMediator();
        if (mediator == null) {
            return "(no proofs are open)";
        }
        var selected = mediator.getSelectedProof();
        var opened = mediator.getCurrentlyOpenedProofs();
        return ProofSelector.proofsBlock(opened, selected);
    }
}
