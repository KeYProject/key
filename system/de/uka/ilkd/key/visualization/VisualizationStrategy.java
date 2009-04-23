// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.visualization;

import de.uka.ilkd.key.proof.Node;

public interface VisualizationStrategy{

    public VisualizationModel createVisualizationModel(Node node);

}
