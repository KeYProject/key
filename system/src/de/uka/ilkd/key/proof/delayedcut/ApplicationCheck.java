// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.proof.delayedcut;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Node.NodeIterator;


public interface ApplicationCheck {

	String check(Node cutNode, Term cutFormula);




	public static class NoNewSymbolsCheck implements ApplicationCheck{
		private Node node;
		private Set<String> names = new TreeSet<String>();

		private static final String INFORMATION1 =
				"The formula contains a symbol that has been introduced below Node ";
		private static final String INFORMATION2 =
				"The formula contains symbols that have been introduced below Node ";
		private static final String ADD_INFORMATION =
				"The formula that you specify at this point will be introduced at the inner node %i\n" +
				"of the proof tree " +
				"by using a cut. Afterwards, the sub-trees of that node will be replayed.\n" +
				"In order to sustain the correctness of the proof, the formula must therefore not contain symbols\n" +
				"that have " +
				"been introduced in the sub-trees of Node %i. In particular this restriction ensures\n" +
				"that symbols that are introduced " +
				"within the subtrees of Node %i are actually new symbols\nas required by the corresponding rule definitions.";


		@Override
		public String check(Node cutNode, Term cutFormula) {
			if(cutNode == null){
				throw new IllegalArgumentException("cutNode is null");
			}
			if(node != cutNode){
				node = cutNode;
				clearCaches();
				buildCaches(node);
			}

			return checkFormula(cutFormula);
		}


		private void clearCaches(){
			names.clear();
			node.clearNameCache();
		}

		private void buildCaches(Node cutNode){
			LinkedList<Node> queue = new LinkedList<Node>();
			queue.add(cutNode);
			while(!queue.isEmpty()){
				Node next = queue.pollFirst();
				if(next.getNameRecorder() != null){
					for(Name name : next.getNameRecorder().getProposals()){
						names.add(name.toString());
					}
				}

				for(NodeIterator it = next.childrenIterator(); it.hasNext();){
					queue.add(it.next());
				}
			}
		}

		private String checkFormula(Term formula){
			final List<String> newSymbols = new LinkedList<String>();
			formula.execPreOrder(new DefaultVisitor() {

				@Override
				public void visit(Term visited) {
					String name = visited.op().name().toString();
					if(names.contains(name)){
						newSymbols.add(name);
					}
				}
			});
			if(newSymbols.isEmpty()){
				return null;
			}

			StringBuffer buf = new StringBuffer(newSymbols.size()==1 ?INFORMATION1 : INFORMATION2);
			buf.append(node.serialNr()+": ");
			for(String name : newSymbols){
				buf.append(name);
				buf.append(", ");
			}
			buf.replace(buf.length()-2, buf.length(), ". (For more information click on this message)");
			buf.append("#");

			buf.append(ADD_INFORMATION.replaceAll("%i",Integer.toString(node.serialNr())));
			return buf.toString();
		}


		@Override
		public String toString() {
			return "NoNewSymbolsCheck [node=" + node.serialNr() + ", names=" + names + "]";
		}





	}
}