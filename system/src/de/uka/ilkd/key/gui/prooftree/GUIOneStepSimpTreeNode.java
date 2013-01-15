package de.uka.ilkd.key.gui.prooftree;

import java.util.Enumeration;

import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.OneStepSimplifier.Protocol;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.rule.RuleApp;

public class GUIOneStepSimpTreeNode extends GUIAbstractTreeNode {

    private final GUIProofTreeModel model;
    private final Node node;
    private final Protocol protocol;
    
    public class GUIOneStepChildTreeNode extends GUIAbstractTreeNode {

        private final RuleApp app;

        public GUIOneStepChildTreeNode(GUIProofTreeModel tree, RuleApp app) {
            super(tree);
            this.app = app;
        }

        @Override public Node getNode() {
            return node;
        }
        
        @Override public TreeNode getChildAt(int childIndex) {
            return null;
        }

        @Override public int getChildCount() {
            return 0;
        }

        @Override public TreeNode getParent() {
            return GUIOneStepSimpTreeNode.this;
        }

        @Override public boolean isLeaf() {
            return true;
        }
        
        @Override public String toString() {
            return app.rule().name() + " @ " + app.posInOccurrence().subTerm();
        }
    }

    public GUIOneStepSimpTreeNode(GUIProofTreeModel guiProofTreeModel, Node n) {
        super(guiProofTreeModel);
        assert n.getAppliedRuleApp() instanceof OneStepSimplifierRuleApp :
            "This kind of gui nodes is only for OSS rule apps";
        
        this.model = guiProofTreeModel;
        this.node = n;
        OneStepSimplifierRuleApp ruleApp = (OneStepSimplifierRuleApp) n.getAppliedRuleApp();
        this.protocol = ruleApp .getProtocol();
    }

    @Override 
    public TreeNode getChildAt(int childIndex) {
        final RuleApp ra = protocol.get(childIndex);
        return new GUIOneStepChildTreeNode(model, ra);
    }

    @Override 
    public int getChildCount() {
        if(protocol != null) {
            return protocol.size();
        } else {
            return 0;
        }
    }

    @Override 
    public TreeNode getParent() {
        Node n = node;
        if(n==null)return null;
        while (n.parent()!=null
               && findChild ( n.parent() ) != null ) {
            n = n.parent();
        }
        return findBranch(n);
    }

    @Override 
    public boolean isLeaf() {
        return getChildCount() == 0;
    }

    @Override 
    public Node getNode() {
        return node;
    }

}
