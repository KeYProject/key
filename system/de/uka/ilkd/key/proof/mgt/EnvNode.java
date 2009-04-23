// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.MutableTreeNode;

import de.uka.ilkd.key.proof.Proof;

public class EnvNode extends DefaultMutableTreeNode implements TaskTreeNode{

    private ProofEnvironment env;

    public EnvNode(ProofEnvironment e) {
	super(e);
	env=e;
    }

    public String shortDescr() {
	return env.description();
    }

    public String toString() {
	return shortDescr();
    }

    public ProofEnvironment getProofEnv() {
	return env;
    }

    public Proof proof() {
	return getChildCount()>0 
	    ? ((TaskTreeNode) getChildAt(0)).proof() : null;
    }

    public Proof[] allProofs() {
	return new Proof[0];
    }


    public void insertNode(TaskTreeModel model, MutableTreeNode parentNode) {
	model.insertNodeInto(this, parentNode, model.getChildCount(parentNode));
    }

    public ProofStatus getStatus() {
	return null;
    }

    public String getDiffToLast() {
	EnvNode lastSibl = (EnvNode) getPreviousSibling();
	if (lastSibl==null) {
	    return "First proof environment. Nothing to diff.";
	}
	return getProofEnv().getDiffUserInfo(lastSibl.getProofEnv());
    }

    public void decoupleFromEnv() {
	// do nothing
    }

}
