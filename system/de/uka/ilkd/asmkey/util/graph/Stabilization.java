// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.util.graph;

import de.uka.ilkd.key.logic.IteratorOfNamed;
import de.uka.ilkd.key.logic.Named;

/**
 * Instances of this class are algorithms that iterates 
 * through all nodes many times, updating datas, until
 * a fix point is reached; otherwise, loop.
 *
 * Instances of this class must overwrite the 
 * method {@link #doVertexWork} that can invoke
 * the method {@link #noFixPoint} do make the computation
 * continue.
 */
public abstract class Stabilization {

    protected DependancyGraph graph;
    private boolean fixPoint;

    public Stabilization(DependancyGraph graph) {
	assert graph!=null:"The DependancyGraph may not be null";
	this.graph = graph;
	this.fixPoint = false;
    }


    public void compute() {
	noFixPoint();
	while(!isFixPoint()) {
	    setToFixPoint();
	    IteratorOfNamed it = graph.vertices();
	    while (it.hasNext()) {
		doVertexWork(it.next());
	    }
	}
    }

    protected abstract void doVertexWork(Named vertex);

    protected boolean isFixPoint() {
	return fixPoint;
    }
    
    protected void noFixPoint() {
	fixPoint = false;
    }

    private void setToFixPoint() {
	fixPoint = true;
    }

}
