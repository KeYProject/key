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

import de.uka.ilkd.asmkey.util.TestUtil.Item;

public class GraphUtil {

    static SedgewickGraph getSedgewickGraph() throws GraphException, CycleException {
	int MAX=13;
	
	SedgewickGraph sed = new SedgewickGraph();
	sed.graph = new DependancyGraph();
	sed.items = new Item[MAX];
	sed.closure = new boolean[MAX][MAX];
	sed.orders = new int[MAX];

	for(int i=0; i<MAX; i++) {
	    sed.items[i] = new Item("I" + i);
	    sed.graph.add(sed.items[i]);
	}
	for(int i=0; i<MAX; i++) {
	    for(int j=0; j<MAX; j++) {
		sed.closure[i][j] = false;
	    }
	}
	Item[] it = sed.items;
	DependancyGraph graph = sed.graph;
	boolean[][] cl = sed.closure;
	graph.addEdge(it[0], it[1]); cl[0][1] = true;
	graph.addEdge(it[0], it[5]); cl[0][5] = true;
	graph.addEdge(it[0], it[6]); cl[0][6] = true;
	sed.orders[0]=3;
	sed.orders[1]=0;
	graph.addEdge(it[2], it[0]); cl[2][0] = true;
	sed.orders[2]=1;
	graph.addEdge(it[3], it[5]); cl[3][5] = true;
	sed.orders[3]=1;
	graph.addEdge(it[4], it[3]); cl[4][3] = true;
	sed.orders[4]=1;
	graph.addEdge(it[5], it[4]); cl[5][4] = true;
	sed.orders[5]=1;
	graph.addEdge(it[6], it[2]); cl[6][2] = true;
	graph.addEdge(it[6], it[4]); cl[6][4] = true;
	graph.addEdge(it[6], it[9]); cl[6][9] = true;
	sed.orders[6]=3;
	graph.addEdge(it[7], it[6]); cl[7][6] = true;
	graph.addEdge(it[7], it[8]); cl[7][8] = true;
	sed.orders[7]=2;
	graph.addEdge(it[8], it[7]); cl[8][7] = true;
	sed.orders[8]=1;
	graph.addEdge(it[9], it[10]); cl[9][10] = true;
	graph.addEdge(it[9], it[11]); cl[9][11] = true;
	graph.addEdge(it[9], it[12]); cl[9][12] = true;
	sed.orders[9]=3;
	sed.orders[10]=0;
	graph.addEdge(it[11], it[6]); cl[11][6] = true;	    
	graph.addEdge(it[11], it[12]); cl[11][12] = true;
	sed.orders[11]=2;
	graph.addEdge(it[12], it[11]); cl[12][11] = true;
	sed.orders[12]=1;

	/* we compute the transitive closure using
	 * the warshall algorithm. sedgewick.
	 */
	for (int y=0; y<MAX; y++) {
	    for(int x=0; x<MAX; x++) {
		if (cl[x][y]) {
		    for(int j = 0; j<MAX; j++) {
			if (cl[y][j]) {cl[x][j] = true;}
		    }
		}
	    }
	}

	return sed;
				     
    }

    static class SedgewickGraph {
	public DependancyGraph graph;
	public Item[] items;
	public boolean[][] closure;
	public int[] orders;
    }


    static void populateItemsAndGraph(Item[] items, DependancyGraph graph) throws GraphException {
	for(int i=0; i<items.length; i++) {
	    items[i] = new Item("I" + i);
	    graph.add(items[i]);
	}
    }
}

