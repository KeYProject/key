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
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.ArrayOp;
import de.uka.ilkd.key.logic.op.AttributeOp;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.ArraySortImpl;
import de.uka.ilkd.key.logic.sort.ClassInstanceSort;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
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
    public ImmutableSet<Term> translate(Taclet t, Term term, ImmutableSet<Term> attributeTerms, Services services
	    ,TacletConditions cond);
    
    
}


final class DefaultAttributeTranslator implements AttributeTranslator{

    
    
    public ImmutableSet<Term> translate(Taclet t, Term term, 
	    ImmutableSet<Term> attributeTerms, Services services,TacletConditions cond) {
	ImmutableSet<Term> result = DefaultImmutableSet.nil();
	
	
	Collection<Term> attributes=  createPossibleInstantiations(attributeTerms,services);
	Collection<Term> arrayTerms = createPossibleInstantiationsForArrays(attributeTerms,services);


	// find the term to replace.
	Term toReplace = analyzeTaclet(term, services);
	if(toReplace == null) return result;
	
	if(toReplace.op() instanceof ArrayOp || 
	   (toReplace.op() instanceof AttributeOp && 
            ((AttributeOp)toReplace.op()).sort().equals(ProgramSVSort.ARRAYLENGTH))){
	    toReplace = toReplace.sub(0);
	    for(Term src : arrayTerms){
		
		Term tmp = instantiateArray(src,term,services,toReplace);
		if(tmp != null){
		   result = result.add(tmp);
		}
	    }
	 
	    
	}else{
	  // instantiate all attributes that match the term 'toReplace'
	 for(Term src : attributes){
	    Term tmp=null;
		   //if(!isArray(src,cond) && !isArray(src,cond)){//Check this Line!!!!
			
		    tmp = instantiateAttributes(src, term, services, toReplace); 
		    //}
	            if(tmp != null){
			result = result.add(tmp);
		    }
	        }
		
	    
	}


	
	
	
	return result;
    }
    
    
    /**
     * @param attributeTerms
     * @param services
     * @return
     */
    private Collection<Term> createPossibleInstantiationsForArrays(
            ImmutableSet<Term> attributeTerms, Services services) {
	HashSet<Term> terms = new HashSet<Term>();
	for(Term term: attributeTerms){
	    
	    do{
		if(term.sort() instanceof ArraySort){
		    terms.add(term);
		}
		if(term.arity() > 0){
		    term = term.sub(0);
		}else{
		    term=null;
		}
	    }while(term != null);
	}
	return terms;
    }


    private boolean isArray(Term term, TacletConditions cond){
	if(term.sort() instanceof ArraySort || term.op() instanceof ArrayOp
           || cond.containsIsReferenceArray(term)){
	    return true;
	}
	//if(term.)
	//ArrayOp op = ArrayOp.getArrayOp(term.op().);

	//cond.containsIsReferenceArray(term);
	return false;
    }
    

    
   /**
     * @param src
     * @param term
     * @param services
     * @param toReplace
     * @return
     */
    private Term instantiateArray(Term array, Term dest, Services services,
            Term toReplace) {
	ImmutableArray<QuantifiableVariable> variables[] = new ImmutableArray[dest.arity()];
	
	if(dest.equals(toReplace)){
	    return array;
	}
	
	
	             
	Term[] subTerms = new Term[dest.arity()];
	for (int i = 0; i < dest.arity(); i++) {
	    
	    variables[i] = dest.varsBoundHere(i);
	    subTerms[i] = instantiateArray(array,dest.sub(i),services,toReplace);

	} 
	if(dest.op() instanceof ArrayOp && ((ArrayOp)dest.op()).getSortDependingOn()  instanceof GenericSort){
	    
	    dest = TermFactory.DEFAULT.createArrayTerm(ArrayOp.getArrayOp(subTerms[0].sort()),subTerms);
	}else
	if(AbstractTacletTranslator.isCreatedTerm(dest, services)){
	    dest = AbstractTacletTranslator.createCreatedTerm(subTerms[0], services);
	}else if(dest.op() instanceof AttributeOp && ((AttributeOp)dest.op()).sort().equals(ProgramSVSort.ARRAYLENGTH)){
	  dest = createLengthTerm(subTerms[0], services);  
	}	
	else{
	     dest = TermFactory.DEFAULT.createTerm(dest.op(), subTerms, variables,
			JavaBlock.EMPTY_JAVABLOCK);    
	}
	
	return dest;
	
    }



/**
    * Analyzes recursively the taclet term to find out which term 
    * must be replaced.
    * @param taclet the term to analyze
    * @param services 
    * @return returns the first term of the sort <code>ProgramSVSort.VARIABLE</code>.
    * If the given term does not contain a term of sort <code>ProgramSVSort.VARIABLE</code> the
    * method returns <code>null</code>. 
    */
   private Term analyzeTaclet(Term taclet, Services services){
       
       
       
       if(taclet.op() instanceof AttributeOp &&
	  !AbstractTacletTranslator.isCreatedTerm(taclet, services)){
	   AttributeOp op = (AttributeOp)taclet.op();
	   if(op.sort().equals(ProgramSVSort.VARIABLE)){
	       return taclet;    
	   }
	   if(op.sort().equals(ProgramSVSort.ARRAYLENGTH)){
	       return taclet;
	   }
	   
	   
       }
       
       if(taclet.op() instanceof ArrayOp){
	   return taclet;
       }
       
       for (int i = 0; i < taclet.arity(); i++) {
	    Term tmp = analyzeTaclet(taclet.sub(i),services);
	    if(tmp!= null) return tmp;
	}       
       return null;
   }
   
     
    /**
     * Instantiates all attributes in <code>dest</code> that match <code>toReplace</code>.
     * In case of matching <code>dest</code> is instantiated by <code>attribute</code>.
     * There are two types of matching.<br>
     * First: The attribute matches <code>dest</code>. Example:<br>
     * A.attribute  matches obj.#a<br>
     * Second: The object belonging to the attribut match <code>dest</code>. Example: <br>
     * A matches obj. 
     * @param attribute the substitution. 
     * @param dest term to be scanned.
     * @param services 
     * @param toReplace term to replace.
     * @return returns the instantiated term.
     */
    private Term instantiateAttributes(Term attribute, Term dest, Services services, Term toReplace){
	ImmutableArray<QuantifiableVariable> variables[] = new ImmutableArray[dest.arity()];
	Term object = null;
	if(attribute.arity() >= 1){
	    object = attribute.sub(0);   
	}
	 
	
	if(dest.equals(toReplace)){
	    return attribute;
	}
	
	if(object!=null&&dest.equals(toReplace.sub(0))){
	    return object;
	}
	
	             
	Term[] subTerms = new Term[dest.arity()];
	for (int i = 0; i < dest.arity(); i++) {
	    
	    variables[i] = dest.varsBoundHere(i);
	    subTerms[i] = instantiateAttributes(attribute,dest.sub(i),services,toReplace);

	} 
	
	if(AbstractTacletTranslator.isCreatedTerm(dest, services)){
	    dest = AbstractTacletTranslator.createCreatedTerm(subTerms[0], services);
	}else{
	    dest = TermFactory.DEFAULT.createTerm(dest.op(), subTerms, variables,
			JavaBlock.EMPTY_JAVABLOCK);    
	}
	
	return dest;

    }


    private Term createLengthTerm(Term objectTerm, Services services){
	 JavaInfo javaInfo = services.getJavaInfo();
	 
	 return TermBuilder.DF.dot(objectTerm, javaInfo.getArrayLength());
    }
    

    

    
    
      
    private  Collection<Term> createPossibleInstantiations
            (ImmutableSet<Term> attributeTerms, Services services){
	TreeNode root = new TreeNode(null,null);
	

	
	for(Term content : attributeTerms){
	    
	    root.addContent(content);
	}
	LinkedList<TreeNode> list = new LinkedList<TreeNode>();
	root.getLeafsAndCrotches(list);
	
	
	LinkedList<Term> container = new LinkedList<Term>();
	
	for(TreeNode node : list){
	   
	   boolean essential = true;
	   boolean start = true;
	   TreeNode last = null;
	   while(!node.isRoot()){
	       
	       if((node.isCrotch()&& !start)){essential = false;}
	       if(essential){
		   if(!AbstractTacletTranslator.isCreatedTerm(node.getContent(),services)&&
		      !(node.getContent().sort() instanceof PrimitiveSort))
		   container.add(node.getContent());
	       }else{
		   break;
		   /*if(node.getContent().sort() instanceof ArraySort){
		      container.add(node.getContent()); 
		   }*/
	       }
	       last = node;
	       node = node.getParent();
	       start = false;
	   }
	}
	

	
	
	
	
	return container;
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
	  if( AbstractTacletTranslator.isCreatedTerm(term,services)){
		System.out.println("\tconains: <created>");
		
	    }
	
	System.out.println("#####");
        
	if(depth == max_depth) return;
	depth++;
	for (int i = 0; i < term.arity(); i++) {
	     analyzeTerm(term.sub(i),depth,max_depth,services);
	    
	}
    }
    
    

    
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
       
       if(t.arity() == 0) return;
       do{
	  if(!(t.op() instanceof ArrayOp)){
	      terms.add(t); 
	  }
	  if(t.arity() > 0){
	      t = t.sub(0);
	  }else    t = null;
       
	  
       }while(t != null);
          
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



















