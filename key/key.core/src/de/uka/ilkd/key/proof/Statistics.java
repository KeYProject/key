package de.uka.ilkd.key.proof;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.informationflow.proof.SideProofStatistics;
import de.uka.ilkd.key.rule.ContractRuleApp;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.OneStepSimplifier.Protocol;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.UseDependencyContractApp;
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
    public final int quantifierInstantiations;
    public final int ossApps;
    public final int totalRuleApps;
    public final int smtSolverApps;
    public final int dependencyContractApps;
    public final int operationContractApps;
    public final int loopInvApps;
    public final long autoModeTimeInNano;
    public final long timeInNano;
    public final float timePerStepInNano;

    private List<Pair<String, String>> summaryList =
                    new ArrayList<Pair<String, String>>(14);

    protected Statistics(int nodes,
                       int branches,
                       int interactiveSteps,
                       int quantifierInstantiations,
                       int ossApps,
                       int totalRuleApps,
                       int smtSolverApps,
                       int dependencyContractApps,
                       int operationContractApps,
                       int loopInvApps,
                       long autoModeTimeInNano,
                       long timeInNano,
                       float timePerStepInNano) {
        this.nodes = nodes;
        this.branches = branches;
        this.interactiveSteps = interactiveSteps;
        this.quantifierInstantiations = quantifierInstantiations;
        this.ossApps = ossApps;
        this.totalRuleApps = totalRuleApps;
        this.smtSolverApps = smtSolverApps;
        this.dependencyContractApps = dependencyContractApps;
        this.operationContractApps = operationContractApps;
        this.loopInvApps = loopInvApps;
        this.autoModeTimeInNano = autoModeTimeInNano;
        this.timeInNano = timeInNano/1000000;
        this.timePerStepInNano = timePerStepInNano;
    }

    static Statistics create(Statistics side, long creationTime) {
    	return new Statistics(side.nodes,
                                  side.branches,
                                  side.interactiveSteps,
                                  side.quantifierInstantiations,
                                  side.ossApps,
                                  side.totalRuleApps,
                                  side.smtSolverApps,
                                  side.dependencyContractApps,
                                  side.operationContractApps,
                                  side.loopInvApps,
                                  side.autoModeTimeInNano,
                                  System.nanoTime() - creationTime,
                                  side.timePerStepInNano);
    }

    Statistics(Proof proof) {
        final Iterator<Node> it = proof.root().subtreeIterator();

        int tmpNodes = 0; // proof nodes
        int tmpBranches = 1; // proof branches
        int tmpInteractive = 0; // interactive steps
        int tmpQuant = 0; // quantifier instantiations
        int tmpOss = 0; // OSS applications
        int tmpOssCaptured = 0; // rules apps in OSS protocol
        int tmpSmt = 0; // SMT rule apps
        int tmpDep = 0; // dependency contract apps
        int tmpContr = 0; // functional contract apps
        int tmpInv = 0; // loop invariants

        while (it.hasNext()) {
            tmpNodes++;
            final Node node = it.next();
            final int c = node.childrenCount();
            if (c > 1) {
                tmpBranches += c - 1;
            }

            if (node.getNodeInfo().getInteractiveRuleApplication()) {
                tmpInteractive++;
            }

            final RuleApp ruleApp = node.getAppliedRuleApp();
            if (ruleApp != null) {

                if (ruleApp instanceof de.uka.ilkd.key.rule.OneStepSimplifierRuleApp) {
                    tmpOss++;
                    final Protocol protocol =
                                    ((de.uka.ilkd.key.rule.OneStepSimplifierRuleApp) ruleApp).getProtocol();
                    if (protocol != null) {
                        tmpOssCaptured += protocol.size() - 1;
                    }
                } else if (ruleApp instanceof de.uka.ilkd.key.smt.RuleAppSMT) {
                    tmpSmt++;
                } else if (ruleApp instanceof UseDependencyContractApp) {
                    tmpDep++;
                } else if (ruleApp instanceof ContractRuleApp) {
                    tmpContr++;
                } else if (ruleApp instanceof LoopInvariantBuiltInRuleApp) {
                    tmpInv++;
                } else if (ruleApp instanceof TacletApp) {
                    final de.uka.ilkd.key.rule.Taclet t = ((TacletApp)ruleApp).taclet();
                    final String tName = t.name().toString();
                    if (tName.startsWith("allLeft")
                            || tName.startsWith("exRight")
                            || tName.startsWith("inst")) {
                        tmpQuant++;
                    }
                }
            }
        }

        this.nodes = tmpNodes;
        this.branches = tmpBranches;
        this.interactiveSteps = tmpInteractive;
        this.quantifierInstantiations = tmpQuant;
        this.ossApps = tmpOss;
        this.totalRuleApps = tmpNodes + tmpOssCaptured -1;
        this.smtSolverApps = tmpSmt;
        this.dependencyContractApps = tmpDep;
        this.operationContractApps = tmpContr;
        this.loopInvApps = tmpInv;
        this.autoModeTimeInNano = proof.getAutoModeTime();
        this.timeInNano = (System.nanoTime() - proof.creationTime);
        timePerStepInNano = nodes<=1? .0f: (autoModeTimeInNano/(float)(nodes-1));

        generateSummary(proof);
    }

    private void generateSummary(Proof proof) {
        Statistics stat = this;
       
        boolean sideProofs = false;
        if (proof instanceof InfFlowProof) { // TODO: get rid of that instanceof by subclassing
            sideProofs = ((InfFlowProof) proof).hasSideProofs();
            if (sideProofs) {
                final long autoTime = proof.getAutoModeTime()
                        + ((InfFlowProof)proof).getSideProofStatistics().autoModeTimeInNano;
                final SideProofStatistics side = ((InfFlowProof) proof).getSideProofStatistics().add(this).setAutoModeTime(autoTime);
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
        
        
        final long time = sideProofs ? stat.autoModeTimeInNano : proof.getAutoModeTime();
        
        summaryList.add(new Pair<String, String>("Automode time",
                        EnhancedStringBuffer.formatTime(time/1000000).toString()));
        if (time >= 10000000000L) {
            summaryList.add(new Pair<String, String>("Automode time", "" +
                            (time/1000000) +
                            "ms"));
        }
        if (stat.nodes > 0) {
            String avgTime = "" + (stat.timePerStepInNano/1000000);
            // round to 3 digits after point
            int i = avgTime.indexOf('.')+4;
            if (i > avgTime.length()) i = avgTime.length();
            avgTime = avgTime.substring(0,i);
            summaryList.add(new Pair<String, String>("Avg. time per step", "" +
                            avgTime +
                            "ms"));
        }

        summaryList.add(new Pair<String, String>("Rule applications", ""));
        summaryList.add(new Pair<String, String>("Quantifier instantiations",
                                                 ""+stat.quantifierInstantiations));
        summaryList.add(new Pair<String, String>("One-step Simplifier apps", "" +
                        stat.ossApps));
        summaryList.add(new Pair<String, String>("SMT solver apps", "" +
                        stat.smtSolverApps));
        summaryList.add(new Pair<String, String>("Dependency Contract apps", "" +
                        stat.dependencyContractApps));
        summaryList.add(new Pair<String, String>("Operation Contract apps", "" +
                        stat.operationContractApps));
        summaryList.add(new Pair<String, String>("Loop invariant apps", "" +
                        stat.loopInvApps));
        summaryList.add(new Pair<String, String>("Total rule apps",
                        EnhancedStringBuffer.format(stat.totalRuleApps).toString()));
    }


    public List<Pair<String, String>> getSummary() {
        return summaryList;
    }

    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer("Proof Statistics:\n");
        for (Pair<String,String> p: summaryList) {
            final String c = p.first;
            final String s = p.second;
            sb = sb.append(c);
            if (!"".equals(s)) {
                sb = sb.append(": ").append(s);
            }
            sb = sb.append('\n');
        }
        sb.deleteCharAt(sb.length()-1);
        return sb.toString();
    }
}