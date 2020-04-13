package org.key_project.proofmanagement.check;

import java.nio.file.Path;
import java.util.List;

import org.key_project.proofmanagement.check.dependency.DependencyGraph;
import org.key_project.proofmanagement.check.dependency.DependencyNode;
import org.key_project.proofmanagement.io.LogLevel;

import static org.key_project.proofmanagement.check.dependency.DependencyGraph.EdgeType.TERMINATION_SENSITIVE;

/**
 * Checks for illegal cyclic dependencies between proofs.<br>
 * Algorithm description:
 *  <ul>
 *      <li>create the dependency graph:<br>
 *          for each proof p
 *          <ul>
 *              <li>create a node containing the contract of p</li>
 *              <li>create edges for proofs p depends on, i.e. to all contracts applied in p
 *                  (operation contracts, dependency contracts, model method contract axioms)</li>
 *              <li>for each edge store if termination has to be proven. This is the case if:
 *                  <ul>
 *                      <li>an operation contract has been applied under diamond modality or</li>
 *                      <li>the applied contract is a dependency contract or</li>
 *                      <li>a contract axiom for a model method has been applied</li>
 *                  </ul>
 *              </li>
 *          </ul>
 *      </li>
 *      <li>calculate the strongly connected components (SCCs) of the graph (only considering
 *          termination sensitive edges</li>
 *      <li>check for each SCC that each contract has a decreases clause or all edges
 *          are termination insensitive</li>
 * </ul>
 *
 * Possible results are:
 * <ul>
 *      <li>no unsound dependencies</li>
 *      <li>illegal cycle (termination arguments needed for contracts ...)</li>
 * </ul>
 *
 * <b>Note:</b> We do not check if the contract actually is applicable (i.e. no box contract is
 * applied inside a diamond modality). This can be checked by the replay checker.
 *
 * @author Wolfram Pfeifer
 */
public class DependencyChecker implements Checker {

    /** data container used to store checker result and share intermediate data
     * (for example proof AST, dependency graph, ...) */
    private CheckerData data;

    @Override
    public void check(List<Path> proofFiles, CheckerData checkerData)
            throws ProofManagementException {
        this.data = checkerData;
        data.addCheck("dependency");
        data.print("Running dependency checker ...");

        // for each proof: parse and construct intermediate AST
        ProverService.ensureProofsLoaded(proofFiles, data);

        // build dependency graph
        ProverService.ensureDependencyGraphBuilt(data);
        DependencyGraph graph = data.getDependencyGraph();

        // check if graph contains illegal structures, e.g. cycles, unproven dependencies, ...
        if (checkGraph(graph)) {
            data.print(LogLevel.INFO, "No illegal dependencies found.");
        } else {
            data.print(LogLevel.INFO, "Illegal dependency found." +
                    " Skipping further dependency checks.");
        }
    }

    /**
     * Checks if the given graph is legal, i.e. has no unsound cyclic dependencies.
     * @param graph the graph to check
     * @return true iff the graph is legal
     */
    private boolean checkGraph(DependencyGraph graph) {

        for (DependencyGraph.SCC scc : graph.getAllSCCs()) {
            // IMPORTANT: we do not check that the modalities inside a cycle match,
            //  i.e. that from diamond modalities only "diamond" contracts are used ...
            //  This (check that a rule is actually applicable) is the job of the replay checker!

            if (!terminationInsensitive(scc) && !terminationEnsured(scc)) {
                scc.setLegal(false);
                return false;
            }
        }
        return true;
    }

    /**
     * Checks if all edges inside the given SCC are termination insensitive.
     * @param scc the given strongly connected component
     * @return true iff all edges are termination insensitive
     */
    private boolean terminationInsensitive(DependencyGraph.SCC scc) {
        // are all edges inside scc termination insensitive?
        for (DependencyNode node : scc.getNodes()) {
            for (DependencyGraph.EdgeType term : scc.internalEdges(node).values()) {
                if (term == TERMINATION_SENSITIVE) {
                    // found single termination sensitive contract application
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * Checks if all contracts in SCC have termination arguments (decreases/measured by clause).
     * <br>
     * <b>Note:</b> We do not check here that the decreases clause is actually proven/the proof
     * is actually closed.
     * @param scc the given strongly connected component
     * @return true iff termination is ensured for all contracts in SCC
     */
    private boolean terminationEnsured(DependencyGraph.SCC scc) {
        for (DependencyNode node : scc.getNodes()) {
            for (DependencyNode next : scc.internalEdges(node).keySet()) {
                // cycle is illegal if:
                // edge is termination sensitive and target contract does not have mby
                if (node.getDependencies().get(next) == TERMINATION_SENSITIVE
                        && !next.getContract().hasMby()) {
                    // TODO: print illegal SCC/cycle in a readable format
                    data.print(LogLevel.WARNING, "Illegal cycle, contract has no termination"
                            + " argument: " + node.getContract().getName());
                    return false;
                }
            }
        }
        return true;
    }
}
