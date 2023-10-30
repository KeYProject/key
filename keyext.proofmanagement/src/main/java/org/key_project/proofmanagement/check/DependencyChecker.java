/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.check;

import java.util.HashSet;
import java.util.Set;

import org.key_project.proofmanagement.check.dependency.DependencyGraph;
import org.key_project.proofmanagement.check.dependency.DependencyNode;
import org.key_project.proofmanagement.io.LogLevel;
import org.key_project.proofmanagement.io.ProofBundleHandler;

import static org.key_project.proofmanagement.check.dependency.DependencyGraph.EdgeType.TERMINATION_SENSITIVE;

/**
 * Checks for illegal cyclic dependencies between proofs.<br>
 * Algorithm description:
 * <ul>
 * <li>create the dependency graph:<br>
 * for each proof p
 * <ul>
 * <li>create a node containing the contract of p</li>
 * <li>create edges for proofs p depends on, i.e. to all contracts applied in p
 * (operation contracts, dependency contracts, model method contract axioms)</li>
 * <li>for each edge store if termination has to be proven. This is the case if:
 * <ul>
 * <li>an operation contract has been applied under diamond modality or</li>
 * <li>the applied contract is a dependency contract or</li>
 * <li>a contract axiom for a model method has been applied</li>
 * </ul>
 * </li>
 * </ul>
 * </li>
 * <li>calculate the strongly connected components (SCCs) of the graph (only considering
 * termination sensitive edges</li>
 * <li>check for each SCC that each contract has a decreases clause or all edges
 * are termination insensitive</li>
 * </ul>
 *
 * Possible results are:
 * <ul>
 * <li>no unsound dependencies</li>
 * <li>illegal cycle (termination arguments needed for contracts ...)</li>
 * </ul>
 *
 * <b>Note:</b> We do not check if the contract actually is applicable (i.e. no box contract is
 * applied inside a diamond modality). This can be checked by the replay checker.
 *
 * @author Wolfram Pfeifer
 */
public class DependencyChecker implements Checker {

    /**
     * data container used to store checker result and share intermediate data
     * (for example proof AST, dependency graph, ...)
     */
    private CheckerData data;

    @Override
    public void check(ProofBundleHandler pbh, CheckerData checkerData)
            throws ProofManagementException {
        this.data = checkerData;
        data.addCheck("dependency");
        data.print("Running dependency checker ...");

        // for each proof: parse and construct intermediate AST
        KeYFacade.ensureProofsLoaded(data);

        // build dependency graph
        KeYFacade.ensureDependencyGraphBuilt(data);
        DependencyGraph graph = data.getDependencyGraph();

        // check if graph contains illegal cycles
        if (hasIllegalCycles(graph)) {
            data.print(LogLevel.WARNING, "Illegal cyclic dependency found" +
                " (further illegal cycles may exist but will not be reported)!");
        } else {
            data.print(LogLevel.INFO, "No illegal dependencies found.");
        }

        // TODO: due to early aborting, dependency results may be wrong if a cyclic dep is found

        data.print(LogLevel.DEBUG, "Searching for unproven dependencies ...");

        // TODO: this should be a separate checker!
        // replay is needed to determine if a proof is closed or not
        // TODO: could be determined with proof tree (without replay)
        if (data.getChecks().get("replay") != null) {
            // check for unproven dependencies
            if (hasUnprovenDependencies(graph, data)) {
                data.print(LogLevel.INFO, "Unproven dependencies found in bundle!");
            } else {
                data.print(LogLevel.INFO, "No unproven dependencies found in bundle!");
            }
        } else {
            data.print(LogLevel.INFO, "Replay is disabled. Skipping check for unproven" +
                "dependencies");
        }

        data.print(LogLevel.INFO, "Dependency checks completed!");
    }

    private boolean hasUnprovenDependencies(DependencyGraph graph, CheckerData data)
            throws ProofManagementException {
        // needs replay (to ensure that proof can be closed)
        KeYFacade.ensureProofsReplayed(data);

        // TODO: probably, topological sorting from Tarjan could be used for speedup ...
        /*
         * time complexity in O(n*n):
         * C <- find closed proofs without dependencies
         * while (C gets larger)
         * n <- find node that has only dependencies in C
         * C <- C + n
         */
        Set<DependencyNode> closed = new HashSet<>();
        boolean changed = true;
        while (changed) {
            changed = false;
            for (DependencyNode n : graph.getNodes()) {
                if (!closed.contains(n)) {
                    CheckerData.ProofEntry entry = data.getProofEntryByContract(n.getContract());
                    if (entry != null) {
                        if (entry.proofState == CheckerData.ProofState.CLOSED
                                && closed.containsAll(n.getDependencies().keySet())) {
                            closed.add(n);

                            // update status in data object
                            entry.dependencyState = CheckerData.DependencyState.OK;
                            data.print(LogLevel.INFO, "Proof is closed and has no" +
                                " unproven dependencies: " + entry.proof.name());

                            changed = true;
                        }
                    }
                    // else {
                    // // These nodes have been created during intermediate proof tree traversal.
                    // // There is no proof for them, therefore they are not considered closed.
                    // }
                }
            }
        }

        boolean hasUnprovenDeps = false;

        // update data: all other (successfully replayed) closed proofs
        // have dependencies left unproven
        for (CheckerData.ProofEntry entry : data.getProofEntries()) {
            if (entry.dependencyState == CheckerData.DependencyState.UNKNOWN
                    && entry.replayState == CheckerData.ReplayState.SUCCESS) {
                entry.dependencyState = CheckerData.DependencyState.UNPROVEN_DEP;
                data.print(LogLevel.WARNING, "Unproven dependencies found for proof "
                    + entry.proof.name());
                hasUnprovenDeps = true;
            }
        }

        return hasUnprovenDeps;
    }

    /**
     * Checks if the given graph is legal, i.e. has no unsound cyclic dependencies.
     *
     * @param graph the graph to check
     * @return true iff the graph is legal
     */
    private boolean hasIllegalCycles(DependencyGraph graph) {

        for (DependencyGraph.SCC scc : graph.getAllSCCs()) {
            // IMPORTANT: we do not check that the modalities inside a cycle match,
            // i.e. that from diamond modalities only "diamond" contracts are used ...
            // This (check that a rule is actually applicable) is the job of the replay checker!

            if (!terminationInsensitive(scc) && !terminationEnsured(scc)) {
                scc.setLegal(false);

                // update all nodes from SCC to illegal cycle state
                for (DependencyNode n : scc.getNodes()) {
                    CheckerData.ProofEntry entry = data.getProofEntryByContract(n.getContract());
                    // TODO: entry == null can not happen
                    // (if node has dependencies it has been parsed,
                    // thus also a proof entry exists)
                    // assert entry != null;
                    entry.dependencyState = CheckerData.DependencyState.ILLEGAL_CYCLE;
                }
                return true; // cycle found
            }
        }
        return false; // no cycle
    }

    /**
     * Checks if all edges inside the given SCC are termination insensitive.
     *
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
     *
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
                    data.print(LogLevel.WARNING, "Illegal cycle/SCC, contract has no termination"
                        + " argument: " + node.getContract().getName());
                    data.print(LogLevel.WARNING, "The illegal SCC is: " + scc);
                    return false;
                }
            }
        }
        return true;
    }
}
