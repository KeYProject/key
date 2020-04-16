package org.key_project.proofmanagement.io.report;

import org.key_project.proofmanagement.check.CheckerData;
import org.key_project.proofmanagement.check.PathNode;
import org.key_project.proofmanagement.check.dependency.DependencyGraph;

import java.util.List;
import java.util.Map;

public class CheckerDataView { //implements InvocationHandler {
    final CheckerData cd;

    public CheckerDataView(CheckerData cd) {
        this.cd = cd;
    }

    public PathNode getFileTree() {     // TODO: filter
        return cd.getFileTree();
    }

    public List<CheckerData.ProofEntry> getProofLines() {     // TODO: filter
        return cd.getProofEntries();
    }

    public DependencyGraph getDependencyGraph() {           // TODO: filter
        return cd.getDependencyGraph();
    }

    public Map<String, String> checks() {
        return cd.getChecks();
    }

    public CheckerData getCheckerData() {
        return cd;
    }

    public String lineSeparator() {
        return System.lineSeparator();
    }

    /*
    public List<String> choices() {

        return cd.get
    }*/

    /*
    @Override
    public Object invoke(Object proxy, Method method, Object[] args) throws Throwable {
        // TODO: delegate method to cd if not found here
        return null;
    }
    */
}
