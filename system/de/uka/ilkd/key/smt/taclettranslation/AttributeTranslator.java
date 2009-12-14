// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.smt.taclettranslation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.AttributeOp;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.ClassInstanceSort;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.metaconstruct.MetaCreated;

/**
 *
 */
interface AttributeTranslator {

    public final AttributeTranslator DEFAULT = new DefaultAttributeTranslator();
    
    /** TODO: write comment
     * @param t
     * @param attributeTerms
     * @return
     */
    public Term translate(Taclet t, Term term, ImmutableSet<Term> attributeTerms, Services services);
    
    
}


final class DefaultAttributeTranslator implements AttributeTranslator{

    
    
    public Term translate(Taclet t, Term term, ImmutableSet<Term> attributeTerms, Services services) {
	ImmutableSet<Term> result = DefaultImmutableSet.nil();
	/*System.out.println("\t\t\tDest-Term:");
	analyzeTerm(term,0,-1);
	System.out.println("\t\t\tSrc-Term:");
	
	*/for(Term src : attributeTerms){
	  //System.out.println(src);
	    //analyzeTerm(src,0,0,services); 
	}
	
	
	Collection<InstantiationContainer> containers = 
	    createPossibleInstantiations(attributeTerms,services);

	
	for(InstantiationContainer container : containers){
	     
	     Term res = instantiateAttributes(container.essential, term, services);
	     // only when at least one term of the essential container was used continue.
	     if(res == null) continue;
	     Term res2 = instantiateAttributes(container.possible,res,services);
	     if(res2 != null){
		 res = res2;
	     }
		
	     if(res != null && checkForNotInstantiatedAttributes(res))
		result = result.add(res);
	    
	}
	
	if(!result.isEmpty()){
	    Term [] array = new Term[result.size()];
	    result.toArray(array);
	    term = TermBuilder.DF.and(array);
	}
	

	/*
	HashMap<Term,ImmutableSet<Term>> container = new HashMap<Term,ImmutableSet<Term>>(); 
	
	for(Term src : attributeTerms){
	   Term temp =  getObject(src);
	   ImmutableSet<Term> set = container.get(temp);
	   if(set== null){
	       set  = DefaultImmutableSet.nil();
	       
	   }
	   set = set.add(src);
	   container.put(temp, set);
	}

	
	
	
	for(ImmutableSet<Term> set : container.values()){
		System.out.println("set: " + set);
		Term last = term; 
		boolean change = false;
		for(Term src : set){
		    Term tmp;
		    //analyzeTerm(src,0,-1);
		    tmp = instantiateAttributes(src,last,services);
		    if(tmp == null){
			//tmp = term;
			//break;
		    }else{
			last = tmp;
			change = true;
			System.out.println("adas");
		    }
		}
		System.out.println(last);
		if(change && checkForNotInstantiatedAttributes(last))
		result = result.add(last);
	
	}
	if(!result.isEmpty()){
	    Term [] array = new Term[result.size()];
	    result.toArray(array);
	    term = TermBuilder.DF.and(array);
	}
*/
	
	return term;
    }
   
    private boolean checkForNotInstantiatedAttributes(Term term){
	if(term.op() instanceof MetaCreated){
	    return false;
	}
	if(term.op() instanceof AttributeOp){
	    AttributeOp op = (AttributeOp) term.op();
	    if(op.sort().equals(ProgramSVSort.IMPLICITCREATED)||
		    op.sort().equals(ProgramSVSort.VARIABLE)){
		return false;
	    }

	}

	for (int i = 0; i < term.arity(); i++) {
	    if(!checkForNotInstantiatedAttributes(term.sub(i)))
		return false;

	}


	return true;
    }
    
    
   private Term getObject(Term src){
       while(src.depth() != 0){
	   src = src.sub(0);
       }
       return src;
   }
   
    private Term instantiateAttributes(Collection<Term> attributes, Term dest, Services services){
	Term res = dest; 
	boolean used = false;
	for(Term src : attributes){
	    Term tmp;
	    
	    //analyzeTerm(src,0,-1);
	    tmp = instantiateAttributes(src,res,services);
	    if(tmp != null){
		res = tmp;
		used = true;

	    }
	}
	if(!used) return null;
	return res;
    }

    /** TODO: write comment
     * @param src
     * @param dest the term to replace by <code>src</code>
     * @return
     */
    private Term instantiateAttributes(Term src, Term dest,Services services) {
	//System.out.println("src: "+ dest);
	
	// Do the work:
	if(match(src,dest,services)){
	    //System.out.println("match: "+src+" and "+dest) ;
	   return src; 	    
	}
	
	
	if(isCreatedTerm(dest,services) || dest.op()instanceof AttributeOp) return null;
	
	// Split the term
	ImmutableArray<QuantifiableVariable> variables[] = new ImmutableArray[dest
                                                                    .arity()];
	boolean change = false;
	Term[] subTerms = new Term[dest.arity()];
	for (int i = 0; i < dest.arity(); i++) {
	    variables[i] = dest.varsBoundHere(i);//subTerms[i].varsBoundHere(i);
	    Term tmp = instantiateAttributes(src,dest.sub(i),services);
	    subTerms[i] = (tmp == null ? dest.sub(i) : tmp);
	    change = (tmp == null ? change : true);
	}	
	dest = TermFactory.DEFAULT.createTerm(dest.op(), subTerms, variables,
		JavaBlock.EMPTY_JAVABLOCK);
	
	if(change){
	    return dest;
	}
	
	return null;
    }
    
    
    private boolean match(Term src, Term dest, Services services){
	
	
	if( (!(dest.op() instanceof AttributeOp) &&
              !(dest.op() instanceof MetaCreated) &&
              !(dest.op() instanceof LogicVariable)) 
              ||
              dest.arity() != src.arity()) //||
        //      dest.depth() != src.depth())
	{
	    return false;
	}
	
	
	/*if(   (dest.sort() instanceof GenericSort &&
		   AbstractTacletTranslator.isReferenceSort(src.sort()))	){
	    return true;
	}*/
		
	if((dest.sort().equals(ProgramSVSort.VARIABLE) &&
		    src.op() instanceof AttributeOp   &&
		    ((AttributeOp)src.op()).sort() instanceof ClassInstanceSort) 
		    ||
	   (dest.sort() instanceof GenericSort &&
		   AbstractTacletTranslator.isReferenceSort(src.sort()))	   
		   ||
            (isCreatedTerm(dest,services) && isCreatedTerm(src,services))
	   ){
	    for(int i=0; i < src.arity(); i++){
		if(!match(src.sub(i),dest.sub(i),services)){
		    return false;
		}
	    }
	    
	    return true;
	    
	    
	}
	
	
	
	return false;

    }
    
    private  Collection<InstantiationContainer> createPossibleInstantiations
            (ImmutableSet<Term> attributeTerms, Services services){
	TreeNode root = new TreeNode(null,null);
	

	
	for(Term content : attributeTerms){
	    root.addContent(content);
	}
	System.out.println(root);
	LinkedList<TreeNode> list = new LinkedList<TreeNode>();
	root.getLeafsAndCrotches(list);
	
	LinkedList<InstantiationContainer> containers 
		= new LinkedList<InstantiationContainer>();
	for(TreeNode node : list){
	   InstantiationContainer container 
	   = new InstantiationContainer();
	   boolean essential = true;
	   boolean start = true;
	   TreeNode last = null;
	   while(!node.isRoot()){
	       
	       if(node.isCrotch()&& !start){essential = false;}
	       if(essential){
		   container.essential.add(node.getContent());
	       }
	       else{
		   
		   if(node.isAttributeTerm()){
		        container.possible.add(node.getContent());
		       }
		   if(last!=null && !isCreatedTerm(last.getContent(), services)){
		       for(TreeNode node2 : node.getChildren()){
			   if(isCreatedTerm(node2.getContent(), services)){
			       container.possible.add(node2.getContent());
			   }
		   }
	       }
		   
		 
		
	       }
	       last = node;
	       node = node.getParent();
	       start = false;
	   }
	   containers.add(container);

	}
	
	//System.out.println(node.getContent());
	
	
	
	
	
	return containers;
    }
    
    private TreeNode getChildWithCreatedTerm(TreeNode node,Services services){
	for(TreeNode node2 : node.getChildren()){
	    if(isCreatedTerm(node2.getContent(), services)) return node2;
	}
	return null;
    }
    
    private boolean containsAttributeTerm(TreeNode node){
	       return node.getContent().op() instanceof AttributeOp;  
	   }
    
    
    private void analyzeTerm(Term term, int depth, int max_depth, Services services){
	

	
	System.out.println("##"+depth+"##");
	System.out.println("Term: " + term);
	System.out.println("Term-Class: " + term.getClass());
	System.out.println("Depth: " + term.depth());
	System.out.println("Sort: " + term.sort());
	System.out.println("Op: " + term.op());
	System.out.println("Op-Class: "+ term.op().getClass());
	
	if(term.op() instanceof AttributeOp){
	    AttributeOp op = (AttributeOp) term.op();
	    System.out.println("is AttributeOp:");
	    System.out.println("\tAttribute: "+op.attribute());
	    System.out.println("\tClass: "+op.attribute().getClass());
	    System.out.println("\tSort: "+op.attribute().sort());
	    System.out.println("\tSort: "+op.sort().getClass());
	    System.out.println("\tJavaType: "+op.attribute().getKeYJavaType());
	    
	
	    
	}
	  if( isCreatedTerm(term,services)){
		System.out.println("\tconains: <created>");
		
	    }
	
	System.out.println("#####");
        
	if(depth == max_depth) return;
	depth++;
	for (int i = 0; i < term.arity(); i++) {
	     analyzeTerm(term.sub(i),depth,max_depth,services);
	    
	}
    }
    
    
    private boolean isCreatedTerm(Term term, Services services){
	if(term.op() instanceof MetaCreated){
	    return true;
	}
	if(term.op() instanceof AttributeOp){
	    AttributeOp op = (AttributeOp) term.op();
	    if(op.sort().equals(ProgramSVSort.IMPLICITCREATED)){
		return true;
	    }
	    final KeYJavaType objectKJT = services.getJavaInfo().getJavaLangObject();
	    if(op.attribute().equals(
		    services.getJavaInfo().
		    getAttribute(ImplicitFieldAdder.IMPLICIT_CREATED, objectKJT))){
		return true;
	    }
		
	}
	return false;
    }
    
}

/**
 * Every instance of <code>InstantiationContainer</code> is used for one 
 * instantiation of the taclet.
 */

class InstantiationContainer{
    /**At least one of this terms must be used for the instantiation of the taclet.*/
    public HashSet<Term> essential = new HashSet<Term>(); 
    /**It is not necessary to use one of this terms for instantiation.*/
    public HashSet<Term> possible = new HashSet<Term>();
    
    
}


class TreeNode{
   private TreeNode parent;
   
   private HashMap<Term,TreeNode> children = new HashMap<Term,TreeNode>();
   private Term content;
   public TreeNode(TreeNode parent, Term content){
       this.parent = parent;
       this.content = content;
   }
   
   private void addNodes(LinkedList<Term> terms){
       if(terms.size() == 0) return;
       Term term = terms.getLast();
       terms.removeLast();
       TreeNode next;
       if(!children.containsKey(term)){
	   next = new TreeNode(this,term);
	   children.put(term,next);
       }else{
	   next = children.get(term);
       }
       
       next.addNodes(terms);
       
   }
   
   public void addContent(Term t){
       LinkedList<Term> terms = new LinkedList<Term>();
       terms.add(t);
       while(t.arity() == 1){
	   terms.add(t.sub(0));
	   t = t.sub(0);
       }
       
       
       addNodes(terms);

   }
   
   public void getLeafsAndCrotches(Collection<TreeNode> list){
       
       if((this.isCrotch() || this.isLeaf())&& !this.isRoot() &&
	       isAttributeTerm()){
	   list.add(this);
       }
       for(TreeNode child: children.values()){
	   child.getLeafsAndCrotches(list);
       }
       
       
   }
   
   public boolean isAttributeTerm(){
       return content.op() instanceof AttributeOp;  
   }
   
   public void addChild(TreeNode child){
       
       children.put(child.content,child);
   }

   public TreeNode getParent() {
       return parent;
   }	

   public Collection<TreeNode> getChildren() {
       return children.values();
   }

   public Term getContent() {
       return content;
   }
   
   
   public boolean equals(Object node){
       return !(node instanceof TreeNode) || node==null ? false
	       : this.content.equals(((TreeNode)node).content);
   }
   
   public String toString(){
       return toString("");
   }
   
   
   
   public String toString(String tab){
       String s = (content == null ? "root" : content.toString())+ "\n";
       tab +="  +";
       for(TreeNode child : children.values()){
	   s+=tab + child.toString(tab);
	   //s+=child.toString(depth)+ (i==children.size() ? ")":",");
	   
       }
       return s;
       
       
   }
   

   
   public boolean isRoot(){
       return parent == null;
   }
   
   public boolean isLeaf(){
       return children.isEmpty();
   }
   
   public boolean isCrotch(){
       return children.size() >= 2;
   }
   
   
}



















