// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.proof;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.SynchronizedBlock;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

/**
 * manages all applicable Taclets (more precisely: Taclets with
 * instantiations but without position information, the ???NoPosTacletApp???s) 
 * at one node. It is a persistent
 * implementation. Taclets can be added because the Taclets allow to
 * introduce new rules during runtime. It offers selective get methods
 * for different kinds of rules.
 */
public class TacletIndex  {

    /** @link aggregation 
     * @label known rules
     * @supplierCardinality **/
    /*#Taclet lnkTaclet;*/
    
    /** contains rewrite Taclets */
    public HashMap<Object, ImmutableList<NoPosTacletApp>> rwList 
	= new HashMap<Object, ImmutableList<NoPosTacletApp>>();

    /** contains antecedent Taclets */
    private HashMap<Object, ImmutableList<NoPosTacletApp>> antecList
	= new HashMap<Object, ImmutableList<NoPosTacletApp>>();

    /** contains succedent Taclets */
    private HashMap<Object, ImmutableList<NoPosTacletApp>> succList
	= new HashMap<Object, ImmutableList<NoPosTacletApp>>();

    /** contains NoFind-Taclets */
    private ImmutableList<NoPosTacletApp> noFindList
	= ImmutableSLList.<NoPosTacletApp>nil();

    /**
     * keeps track of no pos taclet apps with partial 
     * instantiations 
     */
    private HashSet<NoPosTacletApp> partialInstantiatedRuleApps = 
        new HashSet<NoPosTacletApp>(); 

    // reused object to store prefix occurrences when retrieving
    // taclets with java blocks.
    private PrefixOccurrences prefixOccurrences=new PrefixOccurrences();


    /** constructs empty rule index */
    public TacletIndex() {
    }

    /**
     * creates a new TacletIndex with the given Taclets as initial contents.
     */
    public TacletIndex(ImmutableSet<Taclet> tacletSet) {
	setTaclets(toNoPosTacletApp(tacletSet));
    }

    private TacletIndex(HashMap<Object, ImmutableList<NoPosTacletApp>> rwList, 
			HashMap<Object, ImmutableList<NoPosTacletApp>> antecList,
			HashMap<Object, ImmutableList<NoPosTacletApp>> succList, 
			ImmutableList<NoPosTacletApp> noFindList,
                        HashSet<NoPosTacletApp> partialInstantiatedRuleApps) { 
	this.rwList=rwList;
	this.antecList=antecList;
	this.succList=succList;
	this.noFindList = noFindList;
	this.partialInstantiatedRuleApps = partialInstantiatedRuleApps;
    }

    private Object getIndexObj(FindTaclet tac) {
	Object indexObj;
	final Term indexTerm = tac.find();	
	if (!indexTerm.javaBlock().isEmpty()) {
	    final JavaProgramElement prg = indexTerm.javaBlock().program();
	    indexObj = ((StatementBlock)prg).getStatementAt(0);                
            if (!(indexObj instanceof SchemaVariable)) {
		indexObj=indexObj.getClass();       
	    } 
	} else {
	    indexObj = indexTerm.op();
	    if (indexObj instanceof AnonymousUpdate) {
	    //indexed independent of arity
		indexObj=AnonymousUpdate.class;
	    }
	    if (indexObj instanceof QuanUpdateOperator) {
	        //indexed independent of arity
	        indexObj=QuanUpdateOperator.class;
            }
	    if (indexObj instanceof SortDependingSymbol) {
		// indexed independent of sort
		indexObj=((SortDependingSymbol)indexObj).getKind ();
	    }
	    if (indexObj instanceof NRFunctionWithExplicitDependencies) {
		// indexed independent of dependencies
		indexObj=NRFunctionWithExplicitDependencies.class;
	    } 
	    if (indexObj instanceof AccessOp) {
	        indexObj = AccessOp.class;
	    }
	}
	if (indexObj instanceof SchemaVariable) {
	    if (((SchemaVariable)indexObj).isTermSV() 
		|| ((SchemaVariable)indexObj).isFormulaSV()) {
		indexObj=((SortedSchemaVariable)indexObj).sort();
		if ( indexObj instanceof GenericSort )
		    indexObj = GenericSort.class;
	    } else if (((SchemaVariable)indexObj).isProgramSV()) {
		indexObj=SchemaOp.PROGSVOP;
	    } else {
		indexObj=SchemaOp.DEFAULTSVOP;
	    }
	}
	return indexObj;
    }


    private void insertToMap(NoPosTacletApp tacletApp,
			     HashMap<Object, ImmutableList<NoPosTacletApp>> map
			    ) {
	Object indexObj=getIndexObj((FindTaclet)tacletApp.taclet());
	ImmutableList<NoPosTacletApp> opList = map.get(indexObj);	
	if (opList == null) {
	    opList = ImmutableSLList.<NoPosTacletApp>nil().prepend(tacletApp);
	} else {
	    opList = opList.prepend(tacletApp);
	}
	map.put(indexObj, opList);
    }


    private void removeFromMap(NoPosTacletApp tacletApp,
			       HashMap<Object, ImmutableList<NoPosTacletApp>> map) {
	Object op = getIndexObj((FindTaclet)tacletApp.taclet());
	ImmutableList<NoPosTacletApp> opList = map.get(op);	
	if (opList != null) {
	    opList = opList.removeAll(tacletApp);
	    if (opList.isEmpty()) {
		map.remove(op);
	    } else {
		map.put(op, opList);
	    }	
	}
    }


    /**
     * sets the Taclets with instantiation info 
     * in this index and removes the old ones
     * @param tacletAppList the new NoPosTacletApps for this index
     */
    public void setTaclets(ImmutableSet<NoPosTacletApp> tacletAppList) {
	rwList    = new HashMap<Object, ImmutableList<NoPosTacletApp>>();
	antecList = new HashMap<Object, ImmutableList<NoPosTacletApp>>();	
	succList  = new HashMap<Object, ImmutableList<NoPosTacletApp>>();
	noFindList= ImmutableSLList.<NoPosTacletApp>nil();
	addTaclets(tacletAppList);
    }


    /**
     * adds a set of NoPosTacletApp to this index
     * @param tacletAppList the NoPosTacletApps to be added
     */
    public void addTaclets(ImmutableSet<NoPosTacletApp> tacletAppList) {
	Iterator<NoPosTacletApp> it = tacletAppList.iterator();		
	while (it.hasNext()) {
	    add(it.next());
	}
    }

    public static ImmutableSet<NoPosTacletApp> toNoPosTacletApp(ImmutableSet<Taclet> rule) {
	ImmutableSet<NoPosTacletApp> result = DefaultImmutableSet.<NoPosTacletApp>nil();
	for (Taclet t : rule) {
	    result = result.add(NoPosTacletApp.createNoPosTacletApp(t));
	}
	return result;
    }

    /** adds a new Taclet with instantiation information to this index. 
     * If rule instance is not known rule is not added
     * @param taclet the Taclet and its instantiation info to be added
     */
    public void add(Taclet taclet) {
	add(NoPosTacletApp.createNoPosTacletApp(taclet));
    }
    
    /** adds a new Taclet with instantiation information to this index. 
     * If rule instance is not known rule is not added
     * @param tacletApp the Taclet and its instantiation info to be added
     */
    public void add(NoPosTacletApp tacletApp) {
	Taclet rule=tacletApp.taclet();
	if (rule instanceof RewriteTaclet) {
	    insertToMap(tacletApp, rwList);
	} else if (rule instanceof AntecTaclet) {
	    insertToMap(tacletApp, antecList);
	} else if (rule instanceof SuccTaclet) {
	    insertToMap(tacletApp, succList);
	} else if (rule instanceof NoFindTaclet) {
	    noFindList=noFindList.prepend(tacletApp);
	} else {	
	    // should never be reached
	    Debug.fail("Tried to add an unknown type of Taclet");
	}
		
	if (tacletApp.instantiations() != 
	    SVInstantiations.EMPTY_SVINSTANTIATIONS) {
	    partialInstantiatedRuleApps.add(tacletApp);
	}
    }

    /**
     * removes the given NoPosTacletApps from this index
     * @param tacletAppList the NoPosTacletApps to be removed
     */
    public void removeTaclets(ImmutableSet<NoPosTacletApp> tacletAppList) {
	Iterator<NoPosTacletApp> it = tacletAppList.iterator();
	while (it.hasNext()) {
	    remove(it.next());
	}
    }


    /** removes a Taclet with the given instantiation information from this index. 
     * @param tacletApp the Taclet and its instantiation info to be removed
     */
    public void remove(NoPosTacletApp tacletApp) {
	Taclet rule=tacletApp.taclet();
	if (rule instanceof RewriteTaclet) {
	    removeFromMap(tacletApp, rwList);
	} else if (rule instanceof AntecTaclet) {
	    removeFromMap(tacletApp, antecList);
	} else if (rule instanceof SuccTaclet) {
	    removeFromMap(tacletApp, succList);
	} else if (rule instanceof NoFindTaclet) {
	    noFindList=noFindList.removeAll(tacletApp);
	} else {	
	    // should never be reached
	    Debug.fail("Tried to remove an unknown type of Taclet");
	}
	
	if (tacletApp.instantiations() != 
        SVInstantiations.EMPTY_SVINSTANTIATIONS) {
        // Debug.assertTrue(partialInstantiatedRuleApps.contains(tacletApp));
        partialInstantiatedRuleApps.remove(tacletApp);
    }
    }

    /** copies the index */
    public TacletIndex copy() {
	return new TacletIndex((HashMap<Object, ImmutableList<NoPosTacletApp>>)rwList.clone(), 
			     (HashMap<Object, ImmutableList<NoPosTacletApp>>)antecList.clone(), 
			     (HashMap<Object, ImmutableList<NoPosTacletApp>>)succList.clone(), 
			     noFindList, (HashSet<NoPosTacletApp>)partialInstantiatedRuleApps.clone());
    }

    /** clones the index */
    public Object clone() {
	return this.copy();
    }
    
    private ImmutableSet<NoPosTacletApp> addToSet(ImmutableList<NoPosTacletApp> list,
				       ImmutableSet<NoPosTacletApp> set) {	
	Iterator<NoPosTacletApp> it = list.iterator();
	while (it.hasNext()) {
	    set = set.add(it.next());
	}
	return set;
    }

	

    public ImmutableSet<NoPosTacletApp> allNoPosTacletApps() {
	ImmutableSet<NoPosTacletApp> tacletAppSet = DefaultImmutableSet.<NoPosTacletApp>nil();
	Iterator<ImmutableList<NoPosTacletApp>> it0 = rwList.values().iterator();
	while (it0.hasNext()) {
	    tacletAppSet = addToSet(it0.next(), tacletAppSet);
	}
	Iterator<ImmutableList<NoPosTacletApp>> it1 = antecList.values().iterator();
	while (it1.hasNext()) {
	    tacletAppSet = addToSet(it1.next(), tacletAppSet);
	}
	Iterator<ImmutableList<NoPosTacletApp>> it2 = succList.values().iterator();
	while (it2.hasNext()) {
	    tacletAppSet = addToSet(it2.next(), tacletAppSet);
	}
	Iterator<NoPosTacletApp> it3 = noFindList.iterator();
	while (it3.hasNext()) {
	    tacletAppSet = tacletAppSet.add(it3.next());
	}
	return tacletAppSet;
    }

    /** returns a list of Taclets and instantiations from the given list of 
     * taclets with
     * respect to term and the filter object.
     * @param services the Services object encapsulating information
     * about the java datastructures like (static)types etc.
     */
    private ImmutableList<NoPosTacletApp> getFindTaclet(ImmutableList<NoPosTacletApp> taclets,
					       RuleFilter           filter,
					       PosInOccurrence      pos,
					       Constraint           termConstraint,
					       Services             services,
					       Constraint           userConstraint) { 
	return matchTaclets ( taclets,
			      filter,
			      pos,
			      termConstraint,
			      services,
			      userConstraint );
    }

    /**
     * Filter the given list of taclet apps, and match their find
     * parts at the given position of the sequent
     */
    private ImmutableList<NoPosTacletApp> matchTaclets(ImmutableList<NoPosTacletApp> taclets,
					      RuleFilter           p_filter,
					      PosInOccurrence      pos,
					      Constraint           termConstraint,
					      Services             services,
					      Constraint           userConstraint) { 
	
        ImmutableList<NoPosTacletApp> result = ImmutableSLList.<NoPosTacletApp>nil();
	if (taclets == null) {
	    return result;
	}
        
	final Iterator<NoPosTacletApp> it = taclets.iterator();
	while (it.hasNext()) {
	    final NoPosTacletApp tacletApp = it.next();
	    
	    if ( !p_filter.filter(tacletApp.taclet()) ) {
	        continue;
	    }
	    
	    final NoPosTacletApp newTacletApp =
	        tacletApp.matchFind(pos, termConstraint, services, userConstraint);

	    if (newTacletApp != null) {
		result = result.prepend(newTacletApp);
	    }
	}
	return result;
    }

    /**
     * returns a selection from the given map with NoPosTacletApps relevant for
     * the given program element. Occurring prefix elements are tracked and
     * taclet applications for them are added.
     * @param map the map to select the NoPosTacletApps from
     * @param pe the program element that is used to retrieve the taclets
     * @param prefixOcc the PrefixOccurrence object used to keep track of the
     * occuring prefix elements
     */
    private ImmutableList<NoPosTacletApp> getJavaTacletList
	(HashMap<Object, ImmutableList<NoPosTacletApp>> map,
	 ProgramElement pe,
	 PrefixOccurrences prefixOcc) {
	ImmutableList<NoPosTacletApp> result=ImmutableSLList.<NoPosTacletApp>nil();
	if (pe instanceof ProgramPrefix) {
 	    int next=prefixOcc.occurred(pe);
 	    NonTerminalProgramElement nt=(NonTerminalProgramElement)pe;
 	    if (next<nt.getChildCount()) {
 		return getJavaTacletList(map, nt.getChildAt(next), prefixOcc);
 	    }
	} else {
	    result=map.get(pe.getClass());	
	    if (result==null) {
		result=ImmutableSLList.<NoPosTacletApp>nil();
	    }
	}
	return result.prepend(prefixOccurrences.getList(map));
    }

    
    private ImmutableList<NoPosTacletApp> getListHelp
	(HashMap<Object, ImmutableList<NoPosTacletApp>> map, Term term) {
	ImmutableList<NoPosTacletApp> result = ImmutableSLList.<NoPosTacletApp>nil();

	if ( term.op () instanceof Metavariable ) {
	    //%% HACK: just take any term operators
	    final Iterator<Object> it = map.keySet().iterator();
	    while ( it.hasNext () ) {
	        final Object o = it.next ();
	        if ( o instanceof Operator )
	            result = result.prepend ( map.get ( o ) );
            }
	}
    
	if (term.op() instanceof IUpdateOperator) {
	    result = getListHelp ( map,
                                   ( (IUpdateOperator)term.op () ).target ( term ) );
	    return result;
	}		
    
	if (!term.javaBlock().isEmpty()) {
	    prefixOccurrences.reset();
	    StatementBlock sb=(StatementBlock)term.javaBlock().program();
	    result = getJavaTacletList(map, sb.getStatementAt(0),
				       prefixOccurrences);
	} 

	if ( !term.javaBlock().isEmpty() ||
	     term.op () instanceof ProgramVariable ) {
	    ImmutableList<NoPosTacletApp> schemaList=map.get(SchemaOp.PROGSVOP);
	    if (schemaList!=null) {
		result=result.prepend(schemaList);
	    }
	}

	ImmutableList<NoPosTacletApp> inMap;

	if (term.op() instanceof NRFunctionWithExplicitDependencies)
	    inMap = map.get(NRFunctionWithExplicitDependencies.class);	
	else if (term.op () instanceof SortDependingSymbol)
	    inMap = map.get(((SortDependingSymbol)term.op()).getKind ());
	else if (term.op() instanceof AccessOp) {
	    inMap = map.get(AccessOp.class);
	} else {
	    inMap = map.get(term.op());
	}
	if (inMap != null) {
	    result = result.prepend(inMap);
	}
	ImmutableList<NoPosTacletApp> schemaList = ImmutableSLList.<NoPosTacletApp>nil();
	ImmutableList<NoPosTacletApp> schemaList0 = map.get(term.sort());
	if (schemaList0!=null) {
	    schemaList=schemaList0;
	}

	schemaList0 = map.get(SchemaOp.DEFAULTSVOP);
	if (schemaList0!=null) {
	    schemaList = schemaList.prepend(schemaList0); 
	}

	schemaList0 = map.get(GenericSort.class);
	if (schemaList0!=null) {
	    schemaList = schemaList.prepend(schemaList0); 
	}

	result=result.prepend(schemaList);
	return result;
    }
    

    /**
     * creates and returns a selection from the given map of NoPosTacletApps
     * that are compatible with the given term. It is assumed that the map
     * (key -> value mapping)
     * (1) contains keys with the top operator of its value, if no java
     * block is involved on top level of the value and no update is on top level
     * (2) contains keys with the class of its top Java operator of its
     * value's java block, if a java block is involved on the top level
     * (3) contains keys with the special 'operators' PROGSVOP and
     * DEFAULTSVOP if the top Java operator or top operator (resp.) of the
     * value is a program (or variable, resp.) schema variable.
     * (4) contains keys with the sort of the value if this is an other
     * schema variable.
     * If updates are on top level, they are ignored; and indexing starts on
     * the first level beneath updates.
     * @param map the map from where to select the taclets
     * @param term the term that is used to find the selection
     */
    private ImmutableList<NoPosTacletApp> getList
	(HashMap<Object, ImmutableList<NoPosTacletApp>> map, Term term) {
	if (term.op() instanceof AnonymousUpdate) {
	    ImmutableList<NoPosTacletApp> l = map.get(AnonymousUpdate.class);
	    if ( l != null ) return getListHelp ( map, term ).append ( l );
	}
	if (term.op() instanceof QuanUpdateOperator) {
	    ImmutableList<NoPosTacletApp> l = map.get(QuanUpdateOperator.class);
	    if ( l != null ) return getListHelp ( map, term ).append ( l );
	}
	return getListHelp(map, term);
    }

   /** get all Taclets for the antecedent.
    * @param filter Only return taclets the filter selects
    * @param pos the PosOfOccurrence describing the formula for which to look 
    * for top level taclets    
    * @param services the Services object encapsulating information
    * about the java datastructures like (static)types etc.
    * @return IList<NoPosTacletApp> containing all applicable rules
    * and the corresponding instantiations to get the rule fit.
    */
    public ImmutableList<NoPosTacletApp> getAntecedentTaclet(PosInOccurrence pos,						    
						    RuleFilter filter,
						    Services   services,
						    Constraint userConstraint) {                        
        return getTopLevelTaclets(antecList,
				  filter,
				  pos,
				  services,
				  userConstraint);
    }

  /** get all Taclets for the succedent.
    * @param filter Only return taclets the filter selects
    * @param pos the PosOfOccurrence describing the formula for which to look 
    * for top level taclets 
    * @param services the Services object encapsulating information
    * about the java datastructures like (static)types etc.
    * @return IList<NoPosTacletApp> containing all applicable rules
    * and the corresponding instantiations to get the rule fit.
    */
    public ImmutableList<NoPosTacletApp> getSuccedentTaclet(PosInOccurrence pos,						  
						   RuleFilter filter,
						   Services   services,
						   Constraint userConstraint) {       
           
        return getTopLevelTaclets(succList,
				  filter,
				  pos,				  
				  services,
				  userConstraint);
    }

    private ImmutableList<NoPosTacletApp>
	getTopLevelTaclets(HashMap<Object, ImmutableList<NoPosTacletApp>> findTaclets,
			   RuleFilter filter,
			   PosInOccurrence pos,			   
			   Services services,
			   Constraint userConstraint) {
      
        //TODO: afer KeY 1.0 replace the if statement with assert pos.isTopLevel
        // but currently I don't want to change the methods behaviour
        if (!pos.isTopLevel()) 
            return ImmutableSLList.<NoPosTacletApp>nil();
        
        final Constraint termConstraint = 
            pos.constrainedFormula().constraint();
        return
	    getFindTaclet(getList(rwList, pos.subTerm()), 
			  filter,
			  pos,
			  termConstraint,
			  services,
			  userConstraint)
            .prepend(getFindTaclet(getList(findTaclets, pos.subTerm()),
        			   filter,
        			   pos,
        			   termConstraint,
        			   services,
        			   userConstraint));
    }


  /** get all Rewrite-Taclets.
    * @param filter Only return taclets the filter selects
    * @param services the Services object encapsulating information
    * about the java datastructures like (static)types etc.
    * @return IList<NoPosTacletApp> containing all applicable rules
    * and the corresponding instantiations to get the rule fit.
    */
    public ImmutableList<NoPosTacletApp> getRewriteTaclet(PosInOccurrence pos,
						 Constraint      termConstraint,
						 RuleFilter      filter,
						 Services        services,
						 Constraint      userConstraint) { 
	return matchTaclets(getList(rwList, pos.subTerm()),
			    filter,
			    pos,
			    termConstraint,
			    services,
			    userConstraint);
    }


    /** get all Taclets having no find expression.
     * @param filter Only return taclets the filter selects
     * @param services the Services object encapsulating information
     * about the java datastructures like (static)types etc.
     * @return IList<NoPosTacletApp> containing all applicable
     * rules and an empty part for the instantiations because no
     * instantiations are necessary.
     */
    public ImmutableList<NoPosTacletApp> getNoFindTaclet(RuleFilter filter,
	                                        Services   services,
						Constraint userConstraint) {   
	return matchTaclets ( noFindList,
			      filter,
			      null,
			      Constraint.BOTTOM,
			      services,
			      userConstraint );
    }


    /**
     * returns a NoPosTacletApp whose Taclet has a name that equals the given
     * name. If more Taclets have the same name an arbitrary Taclet with that
     * name is returned.
     * @param name the name to lookup
     * @return the found NoPosTacletApp or null if no matching Taclet is there
     */
    public NoPosTacletApp lookup(Name name) {
	Iterator<NoPosTacletApp> it=allNoPosTacletApps().iterator();
	while (it.hasNext()) {
	    NoPosTacletApp tacletApp=it.next();
	    if (tacletApp.taclet().name().equals(name)) {
		return tacletApp;
	    }
	}
	return null;
    }


    /**
     * returns a NoPosTacletApp whose Taclet has a name that equals the given
     * name. If more Taclets have the same name an arbitrary Taclet with that
     * name is returned.
     * @param name the name to lookup
     * @return the found NoPosTacletApp or null if no matching Taclet is there
     */
    public NoPosTacletApp lookup(String name) {
	return lookup(new Name(name));
    }

    /**
     * returns a list with all partial instantiated no pos taclet apps
     * @return list with all partial instantiated NoPosTacletApps
     */
    public ImmutableList<NoPosTacletApp> getPartialInstantiatedApps() {
        ImmutableList<NoPosTacletApp> result = 
            ImmutableSLList.<NoPosTacletApp>nil(); 
        final Iterator<NoPosTacletApp> it = partialInstantiatedRuleApps.iterator();
        while (it.hasNext()) {
            result = result.prepend(it.next());
        }
        return result;
    }

    /** toString */
    public String toString() {
	StringBuffer sb=new StringBuffer();
	sb.append("TacletIndex with applicable rules: ");
	sb.append("ANTEC\n "+antecList);
	sb.append("\nSUCC\n "+succList);
	sb.append("\nREWRITE\n "+rwList);
	sb.append("\nNOFIND\n "+noFindList);
	return sb.toString();
    }

    private static class SchemaOp implements Operator {

	static SchemaOp DEFAULTSVOP = new SchemaOp(); 
	static SchemaOp PROGSVOP = new SchemaOp(); 
	
	private static final Name name = new Name("SVOp");
	private static final Sort svOpSort = 
	    new PrimitiveSort(new Name("SVOp"));

	private SchemaOp() {
	}

	public Name name() {
	    return name;
	}

	/**
	 * checks whether the top level structure of the given @link Term
	 * is syntactically valid, given the assumption that the top level
	 * operator of the term is the same as this Operator. The
	 * assumption that the top level operator and the term are equal
	 * is NOT checked.  
	 * @return true iff the top level structure of
	 * the @link Term is valid.
	 */
	public boolean validTopLevel(Term term) {
	    return true;
	}

	/**
	 * determines the sort of a @link Term with this Operator as top
	 * operator. The assumption that this Operator and the top level
	 * operator are equal is NOT checked.  
	 * @return the sort of the
	 * given Term assumed the top level operator correspnds to this
	 * operator.
	 */
	public Sort sort(Term[] term) {
	    return svOpSort;
	}

	/** @return arity of the Operator as int */
	public int arity() {
	    return 0;
	}

	/**
	 * @return true if the value of "term" having this operator as
	 * top-level operator and may not be changed by modalities
	 */
	public boolean isRigid (Term term) {
	    return false;
	}
	
	/**
	 * These operators will not be used for matching and so always return null.
	 */
	public MatchConditions match(SVSubstitute subst, MatchConditions mc,
	        Services services) {
	    return null;	    
	}
		  
    }


    /**
     * Inner class to track the occurrences of prefix elements in java blocks
     */
    private static class PrefixOccurrences {

	/**
	 * the classes that represent prefix elements of a java block
	 */
	static final Class[] prefixClasses = new Class[]{
	    StatementBlock.class,
	    LabeledStatement.class,
	    Try.class,	    
	    MethodFrame.class,
	    SynchronizedBlock.class};

	/**
	 * number of prefix types
	 */
	static final int PREFIXTYPES=prefixClasses.length;

	/**
	 * field that marks iff the prefix elements have already occurred
	 */
	private boolean[] occurred = new boolean[PREFIXTYPES];
	
	/**
	 * fields to indicate the position of the next relevant child (the next
	 * possible prefix element or real statement
	 */
	static final int[] nextChild = new int[]{0,1,0,1,1};



	PrefixOccurrences() {
	    reset();
	}
	
	/**
	 * resets the occurred field to 'nothing has occurred'
	 */
	public void reset() {
	    for (int i=0; i<PREFIXTYPES; i++) {
		occurred[i]=false;
	    }
	}

	/**
	 * notification that the given program element has occurred. The occurred
	 * fields are subsequently set.
	 * @param pe the occurred program element
	 * @return the number of the next possible prefix element
	 */
	public int occurred(ProgramElement pe) {
	    for (int i=0; i<PREFIXTYPES; i++) {
		if (prefixClasses[i].isInstance(pe)) {
		    occurred[i]=true;
		    if (pe instanceof MethodFrame) {
			return (((MethodFrame)pe).getProgramVariable()
				==null) ?  1 : 2;
		    } else {
			return nextChild[i];
		    }
		}
	    }
	    return -1;
	}

	/**
	 * creates a selection of the given NoPosTacletApp map that comply with the
	 * occurred prefix elements
	 * @param map a map to select from
	 */
	public ImmutableList<NoPosTacletApp> getList
	    (HashMap<Object, ImmutableList<NoPosTacletApp>> map) {
	    ImmutableList<NoPosTacletApp> result=ImmutableSLList.<NoPosTacletApp>nil();
	    for (int i=0; i<PREFIXTYPES; i++) {
		if (occurred[i]) {
		    ImmutableList<NoPosTacletApp> inMap=map.get(prefixClasses[i]);
		    if (inMap!=null) {
			result=result.prepend(inMap);
		    }
		}
	    }
	    return result;
	}

    }


}
 
