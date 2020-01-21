package org.key_project.proofmanagement.io.report;

import org.key_project.proofmanagement.check.CheckerData;
import org.key_project.proofmanagement.check.PathNode;
import org.key_project.proofmanagement.check.dependency.DependencyGraph;

import java.util.List;

public class CheckerDataView {
    final CheckerData cd;

    public CheckerDataView(CheckerData cd) {
        this.cd = cd;
    }

    public PathNode getFileTree() {     // TODO: filter
        return cd.getFileTree();
    }

    public List<CheckerData.ProofLine> getProofLines() {     // TODO: filter
        return cd.getProofLines();
    }

    public DependencyGraph getDependencyGraph() {           // TODO: filter
        return cd.getDependencyGraph();
    }
}
