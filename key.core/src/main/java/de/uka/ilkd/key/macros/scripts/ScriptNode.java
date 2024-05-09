/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.proof.Node;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ScriptNode {
    private static final Logger LOGGER = LoggerFactory.getLogger(ScriptNode.class);

    private final Map<String, String> command;
    private final int fromPos;
    private final int toPos;
    private final @Nullable ScriptNode parent;
    private final List<ScriptNode> children = new LinkedList<>();
    private @Nullable Node proofNode;
    private @Nullable Throwable encounteredException;

    public ScriptNode(@Nullable ScriptNode parent, Map<String, String> command, int fromPos,
            int toPos) {
        this.parent = parent;
        this.command = command;
        this.fromPos = fromPos;
        this.toPos = toPos;
    }

    public void addNode(ScriptNode node) {
        children.add(node);
    }

    public void dump(int indent) {
        LOGGER.debug("{} {} {}", " ".repeat(indent),
            proofNode == null ? "xxx" : proofNode.serialNr(), command);
        for (ScriptNode child : children) {
            child.dump(indent + 1);
        }
    }

    public Map<String, String> getCommand() {
        return command;
    }

    public @Nullable Node getProofNode() {
        return proofNode;
    }

    public void setProofNode(Node proofNode) {
        this.proofNode = proofNode;
    }

    public List<ScriptNode> getChildren() {
        return children;
    }

    public int getFromPos() {
        return fromPos;
    }

    public int getToPos() {
        return toPos;
    }

    public void clearChildren() {
        children.clear();
    }

    public @Nullable Throwable getEncounteredException() {
        return encounteredException;
    }

    public void setEncounteredException(Throwable encounteredException) {
        this.encounteredException = encounteredException;
    }

    public ScriptNode getParent() {
        return parent;
    }

    public boolean isRoot() {
        return (parent == null);
    }


}
