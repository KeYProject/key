// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.smt.hierarchy;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Represents the hierarchy of the Java reference types known to KeY.
 * @author mihai
 *
 */

public class TypeHierarchy {


	/**
	 * Maps each sort to its SortNode. 
	 * The SortNode contains the parents and children of the sort.
	 */
	private HashMap<Sort,SortNode> sortmap; 
	/**
	 * List of known java reference sorts.
	 */
	private List<Sort> sortList;
	/**
	 * List of known array sorts.
	 */
	private List<Sort> arraySortList;
	/**
	 * The KeY services.
	 */
	private Services services;
	
	public TypeHierarchy(Services services){
		this.services = services;
		sortmap = new HashMap<Sort,SortNode>();
		sortList = new LinkedList<Sort>();
		arraySortList = new LinkedList<Sort>();
		
		//Find all sorts
		for(Named n : services.getNamespaces().sorts().allElements()){
			if(n instanceof Sort){
				Sort sort = (Sort) n;
				//don't add the null sort
				if(!sort.equals(services.getTypeConverter().getHeapLDT().getNull().sort())){
					addSort(sort);
					sortList.add(sort);
					
					if(sort.name().toString().endsWith("[]")){
						arraySortList.add(sort);
					}					
				}
			}
		}
		
		//For all found sorts find their parents and children.
		for(Entry<Sort, SortNode> e : sortmap.entrySet() ){
			Sort s = e.getKey();
			SortNode n = e.getValue();

			for(Sort p : s.extendsSorts(services)){
				//get parent node
				SortNode pn = sortmap.get(p);
				if(pn == null){
					//System.err.println(p+" has no parent node");
					continue;
				}
				n.addParent(pn);
				pn.addChild(n);
			}
		}
	}
	/**
	 * 
	 * @return The list of sorts in the type hierarchy.
	 */
	public List<Sort> getSortList() {
		return sortList;
	}
	/**
	 * 
	 * @return The list of array sorts in the type hierarchy.
	 */
	public List<Sort> getArraySortList() {
		return arraySortList;
	}

	private void addSort(Sort s){
		SortNode node = new SortNode(s);
		sortmap.put(s, node);
	}
	/**
	 * Returns the children of a sort s.
	 * @param s A sort s.
	 * @return The SortNodes containing the children of s.
	 */
	public Set<SortNode> getChildren(Sort s){

		if(sortmap.get(s) == null){
			//System.out.println(s.name() + " not found" );
			return new HashSet<SortNode>();
		}
		return sortmap.get(s).getChildren();
	}
	/**
	 * Returns the parents of a sort s.
	 * @param s A sort s.
	 * @return The SortNodes containing the parents of s.
	 */
	public Set<SortNode> getParents(Sort s){
		return sortmap.get(s).getParents();
	}
	/**
	 * Removes all interface sorts from the type hierarchy.
	 * All sorts without non-interface parents become children of java.lang.Object.
	 * All other sorts are left unchanged.
	 */
	public void removeInterfaceNodes(){
		
		JavaInfo info = services.getJavaInfo();
		
		//find all interface sorts and contract them
		Set<Sort> interfaceSorts = new HashSet<Sort>();
		for(Sort s : sortmap.keySet()){
			
			KeYJavaType kjt = info.getKeYJavaType(s);
			if(kjt!=null){
				Type jt = kjt.getJavaType();
				if(jt instanceof InterfaceDeclaration){
					//contract interface sort
					contractNode(s);
					interfaceSorts.add(s);
				}
			}
			
			
		}
		//remove the found interface sorts from the map
		for (Sort sort : interfaceSorts) {
			sortmap.remove(sort);
		}
		/*
		 * Some sorts may end up with two parents, one of which is java.lang.Object. 
		 * In those cases we remove java.lang.Object as parent.
		 */
		for(Sort s : sortmap.keySet()){
			SortNode node = sortmap.get(s);
			if(node.getParents().size() > 1){
				Set<SortNode> toRemove = new HashSet<SortNode>();
				for(SortNode p : node.getParents()){
					if(p.getSort().toString().equals("java.lang.Object")){
						p.removeChild(node);
						toRemove.add(p);
					}
				}
				for(SortNode p : toRemove){
					node.removeParent(p);
				}

			}
		}



	}
	/**
	 * Contracts a sort s. Removes s as child of its parents and parent of its children.
	 * The children of s become the children of all parents of s and vice-versa. 
	 * @param s The sort to be contracted.
	 */
	private void contractNode(Sort s){
		SortNode node = sortmap.get(s);
		Set<SortNode> parents = node.getParents();
		Set<SortNode> children = node.getChildren();
		
		
		//add children as children of parent
		for(SortNode p : parents){
			p.removeChild(node);
			for(SortNode c : children){
				p.addChild(c);
			}
		}
		//add parents as parents of children
		for(SortNode c : children){
			c.removeParent(node);
			for(SortNode p : parents){
				c.addParent(p);
			}
		}

		//sortmap.remove(s);

	}
	
	

	public void print(){
		for(Entry<Sort, SortNode> e : sortmap.entrySet() ){
			Sort s = e.getKey();
			SortNode n = e.getValue();

			String sorttype = s.isAbstract()? "abstract" : "concrete";
			System.err.println(sorttype + " "+ s);
			System.err.println("Parents: "+ n.getParents() );
			System.err.println("Children: "+n.getChildren());
			System.err.println("-------------------------");

		}
	}

}