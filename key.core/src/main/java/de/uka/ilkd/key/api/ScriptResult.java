/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.api;

import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.proof.Node;

/**
 * Object that represents one result goal of a script command It holds a reference to its parent
 * node and to the list of variables and their values for this result Created by S. Grebing
 */
public class ScriptResult {

    /**
     * The current goal node
     */
    private ProjectedNode newNode;

    /**
     * the parent scriptNode to which the scriptcommand was applied
     */
    private ProjectedNode parentNode;

    /**
     * The scriptcommand that lead to this result
     */
    private ProofScriptCommandCall<?> call;

    /**
     * The reference to the variableassingments for this result
     */
    // private VariableAssignments assignments;

    /**
     * The list of labels for the result
     */
    private Set<List<String>> labels;

    /**
     * List with line numbers
     */
    private List<PositionInfo> linenumbers;

    // getLineNumbers hier

    /**
     *
     */
    ScriptResult() {
        // nulls
    }

    public static <T> ScriptResult create(Node node, ProjectedNode onNode,
            ProofScriptCommandCall<T> call) {
        ScriptResult sr = new ScriptResult();
        sr.parentNode = onNode;
        sr.newNode = new ProjectedNode(node, onNode);
        sr.call = call;
        return sr;
    }

    public ProjectedNode getNewNode() {
        return newNode;
    }

    public ScriptResult setNewNode(ProjectedNode newNode) {
        this.newNode = newNode;
        return this;
    }

    public ProjectedNode getParentNode() {
        return parentNode;
    }

    public ScriptResult setParentNode(ProjectedNode parentNode) {
        this.parentNode = parentNode;
        return this;
    }

    public ProofScriptCommandCall<?> getCall() {
        return call;
    }

    public ScriptResult setCall(ProofScriptCommandCall<?> call) {
        this.call = call;
        return this;
    }

    public Set<List<String>> getLabels() {
        return labels;
    }

    public ScriptResult setLabels(Set<List<String>> labels) {
        this.labels = labels;
        return this;
    }

    public List<PositionInfo> getLinenumbers() {
        return linenumbers;
    }

    public ScriptResult setLinenumbers(List<PositionInfo> linenumbers) {
        this.linenumbers = linenumbers;
        return this;
    }

    public ProjectedNode getProjectedNode() {
        return getNewNode();
    }
}
