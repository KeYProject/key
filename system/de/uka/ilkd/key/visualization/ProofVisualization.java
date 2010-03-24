// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.visualization;


import java.util.HashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;



public class ProofVisualization {

    Node node;
    VisualizationStrategy visualizationStrategy;
    VisualizationModel visModel;

    public ProofVisualization(Node node,Services serv, 
			      HashSet ignoreNodes, boolean ignoreAntec){
	this(node, null, serv, ignoreNodes, ignoreAntec);
    }
      
    public ProofVisualization(Node node, Services serv){
	this(node, null, serv, new HashSet(), false);
    }

    
    public ProofVisualization(Node node, VisualizationStrategy visStr, 
			      Services serv, HashSet ignoreNodes,
			      boolean ignoreAntec){
        if (visStr == null) {
            visStr = new SimpleVisualizationStrategy(serv);
        }
        this.node = node;
	visualizationStrategy = visStr;
	visModel = ((SimpleVisualizationStrategy) visualizationStrategy).
	    createVisualizationModel(node, ignoreNodes, ignoreAntec);
    }

    public VisualizationModel getVisualizationModel(){
	return visModel;
    }

    public Node getNode() {
        return node;
    }

}


