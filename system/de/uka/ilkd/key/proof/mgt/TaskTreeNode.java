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

import javax.swing.tree.MutableTreeNode;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.proof.Proof;

public interface TaskTreeNode extends MutableTreeNode{

    ProofEnvironment getProofEnv();

    String shortDescr();

    Proof proof();

    Proof[] allProofs();

    void insertNode(TaskTreeModel model, MutableTreeNode parent);

    TreeNode[] getPath() ;

    ProofStatus getStatus();

    void decoupleFromEnv();
}
