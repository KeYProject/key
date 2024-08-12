/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import org.key_project.rusty.Services;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.logic.Sequent;
import org.key_project.rusty.logic.SequentChangeInfo;
import org.key_project.rusty.rule.NoPosTacletApp;
import org.key_project.rusty.rule.RuleApp;
import org.key_project.rusty.rule.Taclet;
import org.key_project.rusty.rule.inst.SVInstantiations;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.ArrayList;
import java.util.List;

public final class Goal {
    private Node node;
    /**
     * The namespaces local to this goal. This may evolve over time.
     */
    private NamespaceSet localNamespaces;
    /**
     * list of all applied rule applications at this branch
     */
    private ImmutableList<RuleApp> appliedRuleApps = ImmutableSLList.nil();

    private final RuleAppIndex ruleAppIndex;

    /**
     * creates a new goal referencing the given node
     */
    public Goal(Node node, TacletIndex tacletIndex, NamespaceSet localNamespace) {
        this.node = node;
        this.localNamespaces = localNamespace;
        ruleAppIndex = new RuleAppIndex(tacletIndex, this, node.proof().getServices());
    }

    public Goal(Node n, TacletIndex tacletIndex, Services services) {
        this(n, tacletIndex, services.getNamespaces().copy());
    }

    /**
     * copy constructor
     */
    private Goal(Node node, RuleAppIndex ruleAppIndex, ImmutableList<RuleApp> appliedRuleApps,
                  NamespaceSet localNamespace) {
        this.node = node;
        this.ruleAppIndex = ruleAppIndex.copy(this);
        this.appliedRuleApps = appliedRuleApps;
        this.localNamespaces = localNamespace;
    }

    public Node getNode() {
        return node;
    }

    public void setNode(Node node) {
        this.node = node;
    }

    /**
     * returns the namespaces for this goal.
     *
     * @return an up-to-date non-null namespaces-set.
     */
    public NamespaceSet getLocalNamespaces() {
        return localNamespaces;
    }

    public RuleAppIndex ruleAppIndex() {
        return ruleAppIndex;
    }

    /**
     * puts a RuleApp to the list of the applied rule apps at this goal and stores it in the node of
     * the goal
     *
     * @param app the applied rule app
     */
    public void addAppliedRuleApp(RuleApp app) {
        // Last app first makes inserting and searching faster
        appliedRuleApps = appliedRuleApps.prepend(app);
        getNode().setAppliedRuleApp(app);
    }

    public Sequent sequent() {
        return getNode().sequent();
    }

    /**
     * creates n new nodes as children of the referenced node and new n goals that have references
     * to these new nodes.
     *
     * @param n number of goals to create
     * @return the list of new created goals.
     */
    public ImmutableList<Goal> split(int n) {
        ImmutableList<Goal> goalList = ImmutableSLList.nil();

        final Node parent = node; // has to be stored because the node
        // of this goal will be replaced

        if (n == 1) {
            Node newNode = new Node(parent.proof(), parent.sequent(), parent);

            parent.add(newNode);
            this.setNode(newNode);
            goalList = goalList.prepend(this);
        } else if (n > 1) { // this would also work for n ==1 but the above avoids unnecessary
            // creation of arrays
            Node[] newNode = new Node[n];

            for (int i = 0; i < n; i++) {
                // create new node and add to tree
                newNode[i] = new Node(parent.proof(), parent.sequent(), parent);
            }

            parent.addAll(newNode);

            this.setNode(newNode[0]);
            goalList = goalList.prepend(this);

            for (int i = 1; i < n; i++) {
                goalList = goalList.prepend(clone(newNode[i]));
            }
        }

        return goalList;
    }

    /**
     * clones the goal (with copy of tacletindex and ruleAppIndex).
     * <p>
     * The local symbols are reused. This is taken care of later.
     *
     * @param node the new Node to which the goal is attached
     * @return Object the clone
     */
    public Goal clone(Node node) {
        Goal clone;
        clone = new Goal(node, ruleAppIndex, appliedRuleApps, localNamespaces);
        return clone;
    }

    public Proof proof() {
        return node.proof();
    }

    /**
     * sets the sequent of the node
     *
     * @param sci SequentChangeInfo containing the sequent to be set and describing the applied
     *        changes to the sequent of the node currently pointed to by this goal
     */
    public void setSequent(SequentChangeInfo sci) {
        assert sci.getOriginalSequent() == getNode().sequent();
        if (!sci.hasChanged()) {
            assert sci.sequent().equals(sci.getOriginalSequent());
            return;
        }
        getNode().setSequent(sci.sequent());
       // getNode().getNodeInfo().setSequentChangeInfo(sci);
    }

    public void setBranchLabel(String name) {
        // TODO @ DD
    }

    /**
     * puts the NoPosTacletApp to the set of TacletApps at the node of the goal and to the current
     * RuleAppIndex.
     *
     * @param app the TacletApp
     */
    public void addNoPosTacletApp(NoPosTacletApp app) {
        getNode().addNoPosTacletApp(app);
        ruleAppIndex.addNoPosTacletApp(app);
    }

    /**
     * creates a new TacletApp and puts it to the set of TacletApps at the node of the goal and to
     * the current RuleAppIndex.
     *
     * @param rule the Taclet of the TacletApp to create
     * @param insts the given instantiations of the TacletApp to be created
     */
    public void addTaclet(Taclet rule, SVInstantiations insts, boolean isAxiom) {
        NoPosTacletApp tacletApp =
                NoPosTacletApp.createFixedNoPosTacletApp(rule, insts, proof().getServices());
        if (tacletApp != null) {
            addNoPosTacletApp(tacletApp);
            /*if (proof().getInitConfig() != null) { // do not break everything
                // because of ProofMgt
                proof().getInitConfig().registerRuleIntroducedAtNode(tacletApp,
                        node.parent() != null ? node.parent() : node, isAxiom);
            }*/
        }
    }
}
