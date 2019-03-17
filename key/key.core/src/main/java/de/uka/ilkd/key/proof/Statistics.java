package de.uka.ilkd.key.proof;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.informationflow.proof.SideProofStatistics;
import de.uka.ilkd.key.rule.AbstractBlockSpecificationElementBuiltInRuleApp;
import de.uka.ilkd.key.rule.ContractRuleApp;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.OneStepSimplifier.Protocol;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.UseDependencyContractApp;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.util.EnhancedStringBuffer;
import de.uka.ilkd.key.util.Pair;

/**
 * Instances of this class encapsulate statistical information about proofs,
 * such as the number of nodes, or the number of interactions.
 * @author bruns
 *
 */
public class Statistics {
    public final int nodes;
    public final int branches;
    public final int interactiveSteps;
    public final int symbExApps;
    public final int quantifierInstantiations;
    public final int ossApps;
    public final int mergeRuleApps;
    public final int totalRuleApps;
    public final int smtSolverApps;
    public final int dependencyContractApps;
    public final int operationContractApps;
    public final int blockLoopContractApps;
    public final int loopInvApps;
    public final long autoModeTimeInMillis;
    public final long timeInMillis;
    public final float timePerStepInMillis;

    private List<Pair<String, String>> summaryList =
                    new ArrayList<Pair<String, String>>(14);

    private final HashMap<String, Integer> interactiveAppsDetails =
            new HashMap<String, Integer>();

    protected Statistics(int nodes,
                         int branches,
                         int interactiveSteps,
                         int symbExApps,
                         int quantifierInstantiations,
                         int ossApps,
                         int mergeRuleApps,
                         int totalRuleApps,
                         int smtSolverApps,
                         int dependencyContractApps,
                         int operationContractApps,
                         int blockLoopContractApps,
                         int loopInvApps,
                         long autoModeTimeInMillis,
                         long timeInMillis,
                         float timePerStepInMillis) {
        this.nodes = nodes;
        this.branches = branches;
        this.interactiveSteps = interactiveSteps;
        this.symbExApps = symbExApps;
        this.quantifierInstantiations = quantifierInstantiations;
        this.ossApps = ossApps;
        this.mergeRuleApps = mergeRuleApps;
        this.totalRuleApps = totalRuleApps;
        this.smtSolverApps = smtSolverApps;
        this.dependencyContractApps = dependencyContractApps;
        this.operationContractApps = operationContractApps;
        this.blockLoopContractApps = blockLoopContractApps;
        this.loopInvApps = loopInvApps;
        this.autoModeTimeInMillis = autoModeTimeInMillis;
        this.timeInMillis = timeInMillis;
        this.timePerStepInMillis = timePerStepInMillis;
    }

    Statistics(Node startNode) {
        final Iterator<Node> it = startNode.subtreeIterator();

        TemporaryStatistics tmp = new TemporaryStatistics();

        Node node;
        while (it.hasNext()) {
            node = it.next();
            tmp.changeOnNode(node, interactiveAppsDetails);
        }

        this.nodes = tmp.nodes;
        this.branches = tmp.branches;
        this.interactiveSteps = tmp.interactive;
        this.symbExApps = tmp.symbExApps;
        this.quantifierInstantiations = tmp.quant;
        this.ossApps = tmp.oss;
        this.mergeRuleApps = tmp.mergeApps;
        this.totalRuleApps = tmp.nodes + tmp.ossCaptured - 1;
        this.smtSolverApps = tmp.smt;
        this.dependencyContractApps = tmp.dep;
        this.operationContractApps = tmp.contr;
        this.blockLoopContractApps = tmp.block;
        this.loopInvApps = tmp.inv;
        this.autoModeTimeInMillis = startNode.proof().getAutoModeTime();
        this.timeInMillis = (System.currentTimeMillis() - startNode.proof().creationTime);
        timePerStepInMillis = nodes <= 1 ? .0f : (autoModeTimeInMillis / (float)(nodes - 1));

        generateSummary(startNode.proof());
    }

    Statistics(Proof proof) {
        this(proof.root());
    }

    static Statistics create(Statistics side, long creationTime) {
        return new Statistics(side.nodes,
                              side.branches,
                              side.interactiveSteps,
                              side.symbExApps,
                              side.quantifierInstantiations,
                              side.ossApps,
                              side.mergeRuleApps,
                              side.totalRuleApps,
                              side.smtSolverApps,
                              side.dependencyContractApps,
                              side.operationContractApps,
                              side.blockLoopContractApps,
                              side.loopInvApps,
                              side.autoModeTimeInMillis,
                              System.currentTimeMillis() - creationTime,
                              side.timePerStepInMillis);
    }

    private void generateSummary(Proof proof) {
        Statistics stat = this;

        boolean sideProofs = false;
        if (proof instanceof InfFlowProof) { // TODO: get rid of that instanceof by subclassing
            sideProofs = ((InfFlowProof) proof).hasSideProofs();
            if (sideProofs) {
                final long autoTime = proof.getAutoModeTime()
                        + ((InfFlowProof)proof).getSideProofStatistics().autoModeTimeInMillis;
                final SideProofStatistics side =
                        ((InfFlowProof) proof).getSideProofStatistics()
                                    .add(this).setAutoModeTime(autoTime);
                stat = Statistics.create(side, proof.creationTime);
            }
        }

        final String nodeString =
                        EnhancedStringBuffer.format(stat.nodes).toString();
        summaryList.add(new Pair<String, String>("Nodes", nodeString));
        summaryList.add(new Pair<String, String>("Branches",
                        EnhancedStringBuffer.format(stat.branches).toString()));
        summaryList.add(new Pair<String, String>("Interactive steps", "" +
                        stat.interactiveSteps));
        summaryList.add(new Pair<String, String>("Symbolic execution steps", "" +
                stat.symbExApps));


        final long time = sideProofs ? stat.autoModeTimeInMillis : proof.getAutoModeTime();

        summaryList.add(new Pair<String, String>("Automode time",
                        EnhancedStringBuffer.formatTime(time).toString()));
        if (time >= 10000L) {
            summaryList.add(new Pair<String, String>("Automode time", time + "ms"));
        }
        if (stat.nodes > 0) {
            String avgTime = "" + (stat.timePerStepInMillis);
            // round to 3 digits after point
            int i = avgTime.indexOf('.') + 4;
            if (i > avgTime.length()) {
                i = avgTime.length();
            }
            avgTime = avgTime.substring(0, i);
            summaryList.add(new Pair<String, String>("Avg. time per step", "" + avgTime + "ms"));
        }

        summaryList.add(new Pair<String, String>("Rule applications", ""));
        summaryList.add(new Pair<String, String>("Quantifier instantiations",
                                                 "" + stat.quantifierInstantiations));
        summaryList.add(new Pair<String, String>("One-step Simplifier apps", "" +
                        stat.ossApps));
        summaryList.add(new Pair<String, String>("SMT solver apps", "" +
                        stat.smtSolverApps));
        summaryList.add(new Pair<String, String>("Dependency Contract apps", "" +
                        stat.dependencyContractApps));
        summaryList.add(new Pair<String, String>("Operation Contract apps", "" +
                        stat.operationContractApps));
        summaryList.add(new Pair<String, String>("Block/Loop Contract apps", "" +
                stat.blockLoopContractApps));
        summaryList.add(new Pair<String, String>("Loop invariant apps", "" +
                        stat.loopInvApps));
        summaryList.add(new Pair<String, String>("Merge Rule apps", "" +
                stat.mergeRuleApps));
        summaryList.add(new Pair<String, String>("Total rule apps",
                        EnhancedStringBuffer.format(stat.totalRuleApps).toString()));
    }


    public List<Pair<String, String>> getSummary() {
        return summaryList;
    }

    public HashMap<String, Integer> getInteractiveAppsDetails() {
        return interactiveAppsDetails;
    }

    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer("Proof Statistics:\n");
        for (Pair<String, String> p: summaryList) {
            final String c = p.first;
            final String s = p.second;
            sb = sb.append(c);
            if (!"".equals(s)) {
                sb = sb.append(": ").append(s);
            }
            sb = sb.append('\n');
        }
        sb.deleteCharAt(sb.length() - 1);
        return sb.toString();
    }

    /**
     * Helper class to add up all rule applications for some nodes
     * @author Michael Kirsten
     */
    private class TemporaryStatistics {
        int nodes = 0; // proof nodes
        int branches = 1; // proof branches
        int interactive = 0; // interactive steps
        int symbExApps = 0; // symbolic execution steps
        int quant = 0; // quantifier instantiations
        int oss = 0; // OSS applications
        int mergeApps = 0; // merge rule applications
        int ossCaptured = 0; // rules apps in OSS protocol
        int smt = 0; // SMT rule apps
        int dep = 0; // dependency contract apps
        int contr = 0; // functional contract apps
        int block = 0; // block and loop contract apps
        int inv = 0; // loop invariants

        /**
         * Increment numbers of rule applications according to given node
         * and (already collected) interactive rule applications
         * @param node the given node
         * @param interactiveAppsDetails already collected interactive rule applications
         */
        private void changeOnNode(final Node node,
                                  final HashMap<String, Integer> interactiveAppsDetails) {
            nodes++;

            branches += childBranches(node);
            interactive += interactiveRuleApps(node, interactiveAppsDetails);
            symbExApps += NodeInfo.isSymbolicExecutionRuleApplied(node) ? 1 : 0;

            final RuleApp ruleApp = node.getAppliedRuleApp();
            if (ruleApp != null) {
                if (ruleApp instanceof de.uka.ilkd.key.rule.OneStepSimplifierRuleApp) {
                    oss++;
                    ossCaptured += tmpOssCaptured(ruleApp);
                } else if (ruleApp instanceof de.uka.ilkd.key.smt.RuleAppSMT) {
                    smt++;
                } else if (ruleApp instanceof UseDependencyContractApp) {
                    dep++;
                } else if (ruleApp instanceof ContractRuleApp) {
                    contr++;
                } else if (ruleApp instanceof AbstractBlockSpecificationElementBuiltInRuleApp) {
                    block++;
                } else if (ruleApp instanceof LoopInvariantBuiltInRuleApp) {
                    inv++;
                } else if (ruleApp instanceof MergeRuleBuiltInRuleApp) {
                    mergeApps++;
                } else if (ruleApp instanceof TacletApp) {
                    quant += tmpQuantificationRuleApps(ruleApp);
                }
            }
        }

        /**
         * Add the node's children's branches (minus one) to current number of branches
         * @param node the node of which we compute its children's branches
         * @return the children's branches minus one
         */
        private int childBranches(final Node node) {
            final int c = node.childrenCount();
            if (c > 1) {
                return c - 1;
            }
            return 0;
        }

        /**
         * Compute number of interactive rule applications and collect their names.
         * @param node the considered node
         * @param intAppsDetails the already collected interactive rule applications
         * @return the number of interactive rule apllications
         */
        private int interactiveRuleApps(final Node node,
                                        final HashMap<String, Integer>
                                                  intAppsDetails) {
            final int res;
            if (node.getNodeInfo().getInteractiveRuleApplication()) {
                res = 1;
                final String ruleAppName =
                        node.getAppliedRuleApp().rule().name().toString();
                if (!intAppsDetails.containsKey(ruleAppName)) {
                    intAppsDetails.put(ruleAppName, 1);
                } else {
                    intAppsDetails.put(ruleAppName, intAppsDetails.get(ruleAppName) + 1);
                }
            } else {
                res = 0;
            }
            return res;
        }

        /**
         * Compute number of available one-step-simplification rules
         * @param ruleApp the rule application considered
         * @return the number of captured oss rule applications
         */
        private int tmpOssCaptured(final RuleApp ruleApp) {
            int tmpOssCaptured = 0;
            final Protocol protocol =
                    ((de.uka.ilkd.key.rule.OneStepSimplifierRuleApp) ruleApp).getProtocol();
            if (protocol != null) {
                tmpOssCaptured = protocol.size() - 1;
            }
            return tmpOssCaptured;
        }

        /**
         * Compute all rule applications regarding quantifiers
         * @param ruleApp the considered rule application
         * @return the number of quantifier rules
         */
        private int tmpQuantificationRuleApps(final RuleApp ruleApp) {
            final int res;
            final String tName =
                    ((TacletApp)ruleApp).taclet().name().toString();
            if (tName.startsWith("allLeft")
                    || tName.startsWith("exRight")
                    || tName.startsWith("inst")) {
                res = 1;
            } else {
                res = 0;
            }
            return res;
        }
    }
}