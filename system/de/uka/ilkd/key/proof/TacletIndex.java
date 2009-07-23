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

import java.util.HashSet;
import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.SynchronizedBlock;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

/**
 * manages all applicable Taclets (more precisely: Taclets with
 * instantiations but without position information, the NoPosTacletApps) 
 * at one node. It is a persistent
 * implementation. Taclets can be added because the Taclets allow to
 * introduce new rules during runtime. It offers selective get methods
 * for different kinds of rules.
 */
public final class TacletIndex  {
    
    private static final Object DEFAULT_SV_KEY = new Object(); 
    private static final Object DEFAULT_PROGSV_KEY = new Object(); 
   
    /** contains rewrite Taclets */
    private HashMap<Object, ListOfNoPosTacletApp> rwList 
	= new HashMap<Object, ListOfNoPosTacletApp>();

    /** contains antecedent Taclets */
    private HashMap<Object, ListOfNoPosTacletApp> antecList
	= new HashMap<Object, ListOfNoPosTacletApp>();

    /** contains succedent Taclets */
    private HashMap<Object, ListOfNoPosTacletApp> succList
	= new HashMap<Object, ListOfNoPosTacletApp>();

    /** contains NoFind-Taclets */
    private ListOfNoPosTacletApp noFindList
	= SLListOfNoPosTacletApp.EMPTY_LIST;

    /**
     * keeps track of no pos taclet apps with partial 
     * instantiations 
     */
    private HashSet<NoPosTacletApp> partialInstantiatedRuleApps = 
        new HashSet<NoPosTacletApp>(); 

    // reused object to store prefix occurrences when retrieving
    // taclets with java blocks.
    private PrefixOccurrences prefixOccurrences = new PrefixOccurrences();


    /** constructs empty rule index */
    public TacletIndex() {
    }

    /**
     * creates a new TacletIndex with the given Taclets as initial contents.
     */
    public TacletIndex(SetOfTaclet tacletSet) {
	setTaclets(tacletSet);
    }

    private TacletIndex(HashMap<Object, ListOfNoPosTacletApp> rwList, 
			HashMap<Object, ListOfNoPosTacletApp> antecList,
			HashMap<Object, ListOfNoPosTacletApp> succList, 
			ListOfNoPosTacletApp noFindList,
                        HashSet<NoPosTacletApp> partialInstantiatedRuleApps) { 
	this.rwList=rwList;
	this.antecList=antecList;
	this.succList=succList;
	this.noFindList = noFindList;
	this.partialInstantiatedRuleApps = partialInstantiatedRuleApps;
    }

    
    private static Object getIndexObj(FindTaclet tac) {
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
	    if(indexObj instanceof SortDependingSymbol) {
		// indexed independently of sort
		indexObj=((SortDependingSymbol)indexObj).getKind ();
	    }
	}
	
	if(indexObj instanceof SchemaVariable) {
	    if((indexObj instanceof TermSV && ((TermSV)indexObj).isStrict())
		|| indexObj instanceof FormulaSV
		|| indexObj instanceof UpdateSV) {
		indexObj = ((SchemaVariable)indexObj).sort();
		if(indexObj instanceof GenericSort) {
		    indexObj = GenericSort.class;
		}
	    } else if (indexObj instanceof ProgramSV) {
		indexObj = DEFAULT_PROGSV_KEY;
	    } else {
		indexObj = DEFAULT_SV_KEY;
	    }
	}
	return indexObj;
    }


    private void insertToMap(NoPosTacletApp tacletApp,
			     HashMap<Object, ListOfNoPosTacletApp> map) {
	Object indexObj=getIndexObj((FindTaclet)tacletApp.taclet());
	ListOfNoPosTacletApp opList = map.get(indexObj);	
	if (opList == null) {
	    opList = SLListOfNoPosTacletApp.EMPTY_LIST.prepend(tacletApp);
	} else {
	    opList = opList.prepend(tacletApp);
	}
	map.put(indexObj, opList);
    }


    private void removeFromMap(NoPosTacletApp tacletApp,
			       HashMap<Object, ListOfNoPosTacletApp> map) {
	Object op = getIndexObj((FindTaclet)tacletApp.taclet());
	ListOfNoPosTacletApp opList = map.get(op);	
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
     * sets the Taclets in this index and removes the old ones
     * @param tacletList the new taclets for this index
     */
    public void setTaclets(SetOfTaclet tacletList) {
	rwList = new HashMap<Object, ListOfNoPosTacletApp>();
	antecList = new HashMap<Object, ListOfNoPosTacletApp>();	
	succList = new HashMap<Object, ListOfNoPosTacletApp>();
	noFindList = SLListOfNoPosTacletApp.EMPTY_LIST;
	addTaclets(tacletList);
    }

    /**
     * sets the Taclets with instantiation info 
     * in this index and removes the old ones
     * @param tacletAppList the new NoPosTacletApps for this index
     */
    public void setTaclets(SetOfNoPosTacletApp tacletAppList) {
	rwList    = new HashMap<Object, ListOfNoPosTacletApp>();
	antecList = new HashMap<Object, ListOfNoPosTacletApp>();	
	succList  = new HashMap<Object, ListOfNoPosTacletApp>();
	noFindList= SLListOfNoPosTacletApp.EMPTY_LIST;
	addTaclets(tacletAppList);
    }


    /**
     * adds a set of Taclets to this index
     * @param tacletList the taclets to be added
     */
    public void addTaclets(SetOfTaclet tacletList) {
	for(Taclet taclet : tacletList) {
	    add(taclet);
	}
    }

    /**
     * adds a set of NoPosTacletApp to this index
     * @param tacletAppList the NoPosTacletApps to be added
     */
    public void addTaclets(SetOfNoPosTacletApp tacletAppList) {
	for(NoPosTacletApp tacletApp : tacletAppList) {
	    add(tacletApp);
	}
    }

    /** 
     * adds a new Taclet to this index. 
     * If rule instance is not known rule is not added
     * @param rule the Taclet to be added
     */
    public void add(Taclet rule) {
	// always added. There no way the creation of the TacletApp fails because
	// there are no instantiations
	add(NoPosTacletApp.createNoPosTacletApp(rule));
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
	    noFindList = noFindList.prepend(tacletApp);
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
    public void removeTaclets(SetOfNoPosTacletApp tacletAppList) {
	for(NoPosTacletApp tacletApp : tacletAppList) {
	    remove(tacletApp);
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
	return new TacletIndex((HashMap<Object, ListOfNoPosTacletApp>)rwList.clone(), 
			     (HashMap<Object, ListOfNoPosTacletApp>)antecList.clone(), 
			     (HashMap<Object, ListOfNoPosTacletApp>)succList.clone(), 
			     noFindList, (HashSet<NoPosTacletApp>)partialInstantiatedRuleApps.clone());
    }

    /** clones the index */
    public Object clone() {
	return this.copy();
    }
    
    
    private SetOfNoPosTacletApp addToSet(ListOfNoPosTacletApp list,
				         SetOfNoPosTacletApp set) {
	for(NoPosTacletApp tacletApp : list) {
	    set = set.add(tacletApp);
	}
	return set;
    }

	

    public SetOfNoPosTacletApp allNoPosTacletApps() {
	SetOfNoPosTacletApp result = SetAsListOfNoPosTacletApp.EMPTY_SET;
	
	for(ListOfNoPosTacletApp tacletApps : rwList.values()) {
	    result = addToSet(tacletApps, result);
	}
	
	for(ListOfNoPosTacletApp tacletApps : antecList.values()) {
	    result = addToSet(tacletApps, result);
	}
	
	for(ListOfNoPosTacletApp tacletApps : succList.values()) {
	    result = addToSet(tacletApps, result);
	}
	
	result = addToSet(noFindList, result);

	return result;
    }

    /** returns a list of Taclets and instantiations from the given list of 
     * taclets with
     * respect to term and the filter object.
     * @param services the Services object encapsulating information
     * about the java datastructures like (static)types etc.
     */
    private ListOfNoPosTacletApp getFindTaclet(ListOfNoPosTacletApp taclets,
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
    private ListOfNoPosTacletApp matchTaclets(ListOfNoPosTacletApp tacletApps,
					      RuleFilter           p_filter,
					      PosInOccurrence      pos,
					      Constraint           termConstraint,
					      Services             services,
					      Constraint           userConstraint) { 
	
        ListOfNoPosTacletApp result = SLListOfNoPosTacletApp.EMPTY_LIST;
	if (tacletApps == null) {
	    return result;
	}
	
	for(NoPosTacletApp tacletApp : tacletApps) {	    
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
    private ListOfNoPosTacletApp getJavaTacletList
	(HashMap<Object, ListOfNoPosTacletApp> map,
	 ProgramElement pe,
	 PrefixOccurrences prefixOcc) {
	ListOfNoPosTacletApp result=SLListOfNoPosTacletApp.EMPTY_LIST;
	if (pe instanceof ProgramPrefix) {
 	    int next=prefixOcc.occurred(pe);
 	    NonTerminalProgramElement nt=(NonTerminalProgramElement)pe;
 	    if (next<nt.getChildCount()) {
 		return getJavaTacletList(map, nt.getChildAt(next), prefixOcc);
 	    }
	} else {
	    result=map.get(pe.getClass());	
	    if (result==null) {
		result=SLListOfNoPosTacletApp.EMPTY_LIST;
	    }
	}
	return result.prepend(prefixOccurrences.getList(map));
    }

    
    private ListOfNoPosTacletApp getListHelp(
	    	HashMap<Object, ListOfNoPosTacletApp> map, 
	    	Term term,
	    	boolean ignoreUpdates) {
	ListOfNoPosTacletApp result = SLListOfNoPosTacletApp.EMPTY_LIST;
		
	assert !(term.op() instanceof Metavariable) : "metavariables are disabled";

	if (!term.javaBlock().isEmpty()) {
	    prefixOccurrences.reset();
	    StatementBlock sb=(StatementBlock)term.javaBlock().program();
	    result = getJavaTacletList(map, sb.getStatementAt(0),
				       prefixOccurrences);
	} 

	if ( !term.javaBlock().isEmpty() ||
	     term.op () instanceof ProgramVariable ) {
	    ListOfNoPosTacletApp schemaList=map.get(DEFAULT_PROGSV_KEY);
	    if (schemaList!=null) {
		result=result.prepend(schemaList);
	    }
	}

	final ListOfNoPosTacletApp inMap;

	if (term.op () instanceof SortDependingSymbol)
	    inMap = map.get(((SortDependingSymbol)term.op()).getKind ());
	else {
	    inMap = map.get(term.op());
	}
	if (inMap != null) {
	    result = result.prepend(inMap);
	}
	ListOfNoPosTacletApp schemaList = SLListOfNoPosTacletApp.EMPTY_LIST;
	ListOfNoPosTacletApp schemaList0 = map.get(term.sort());
	if (schemaList0!=null) {
	    schemaList=schemaList0;
	}

	schemaList0 = map.get(DEFAULT_SV_KEY);
	if (schemaList0!=null) {
	    schemaList = schemaList.prepend(schemaList0); 
	}

	schemaList0 = map.get(GenericSort.class);
	if (schemaList0!=null) {
	    schemaList = schemaList.prepend(schemaList0); 
	}

	result=result.prepend(schemaList);
	
	if(ignoreUpdates && term.op() instanceof UpdateApplication) {
	    result = result.prepend(getListHelp(map, UpdateApplication.getTarget(term), false));
	}	
	
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
    private ListOfNoPosTacletApp getList(HashMap<Object, ListOfNoPosTacletApp> map, 
	    				 Term term,
	    				 boolean ignoreUpdates) {
	return getListHelp(map, term, ignoreUpdates);
    }

   /** get all Taclets for the antecedent.
    * @param filter Only return taclets the filter selects
    * @param pos the PosOfOccurrence describing the formula for which to look 
    * for top level taclets    
    * @param services the Services object encapsulating information
    * about the java datastructures like (static)types etc.
    * @return ListOfNoPosTacletApp containing all applicable rules
    * and the corresponding instantiations to get the rule fit.
    */
    public ListOfNoPosTacletApp getAntecedentTaclet(PosInOccurrence pos,						    
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
    * @return ListOfNoPosTacletApp containing all applicable rules
    * and the corresponding instantiations to get the rule fit.
    */
    public ListOfNoPosTacletApp getSuccedentTaclet(PosInOccurrence pos,						  
						   RuleFilter filter,
						   Services   services,
						   Constraint userConstraint) {       
           
        return getTopLevelTaclets(succList,
				  filter,
				  pos,				  
				  services,
				  userConstraint);
    }

    private ListOfNoPosTacletApp
	getTopLevelTaclets(HashMap<Object, ListOfNoPosTacletApp> findTaclets,
			   RuleFilter filter,
			   PosInOccurrence pos,			   
			   Services services,
			   Constraint userConstraint) {
      
        assert pos.isTopLevel();
        
        final Constraint termConstraint = 
            pos.constrainedFormula().constraint();
        return
	    getFindTaclet(getList(rwList, pos.subTerm(), true), 
			  filter,
			  pos,
			  termConstraint,
			  services,
			  userConstraint)
            .prepend(getFindTaclet(getList(findTaclets, pos.subTerm(), true),
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
    * @return ListOfNoPosTacletApp containing all applicable rules
    * and the corresponding instantiations to get the rule fit.
    */
    public ListOfNoPosTacletApp getRewriteTaclet(PosInOccurrence pos,
						 Constraint      termConstraint,
						 RuleFilter      filter,
						 Services        services,
						 Constraint      userConstraint) { 
	ListOfNoPosTacletApp result = matchTaclets(getList(rwList, pos.subTerm(), false),
			    filter,
			    pos,
			    termConstraint,
			    services,
			    userConstraint);
	return result;
    }


    /** get all Taclets having no find expression.
     * @param filter Only return taclets the filter selects
     * @param services the Services object encapsulating information
     * about the java datastructures like (static)types etc.
     * @return ListOfNoPosTacletApp containing all applicable
     * rules and an empty part for the instantiations because no
     * instantiations are necessary.
     */
    public ListOfNoPosTacletApp getNoFindTaclet(RuleFilter filter,
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
	IteratorOfNoPosTacletApp it=allNoPosTacletApps().iterator();
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
    public ListOfNoPosTacletApp getPartialInstantiatedApps() {
        ListOfNoPosTacletApp result = 
            SLListOfNoPosTacletApp.EMPTY_LIST; 
        final Iterator<NoPosTacletApp> it = partialInstantiatedRuleApps.iterator();
        while (it.hasNext()) {
            result = result.prepend(it.next());
        }
        return result;
    }


    @Override
    public String toString() {
	StringBuffer sb=new StringBuffer();
	sb.append("TacletIndex with applicable rules: ");
	sb.append("ANTEC\n "+antecList);
	sb.append("\nSUCC\n "+succList);
	sb.append("\nREWRITE\n "+rwList);
	sb.append("\nNOFIND\n "+noFindList);
	return sb.toString();
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
	public ListOfNoPosTacletApp getList
	    (HashMap<Object, ListOfNoPosTacletApp> map) {
	    ListOfNoPosTacletApp result=SLListOfNoPosTacletApp.EMPTY_LIST;
	    for (int i=0; i<PREFIXTYPES; i++) {
		if (occurred[i]) {
		    ListOfNoPosTacletApp inMap=map.get(prefixClasses[i]);
		    if (inMap!=null) {
			result=result.prepend(inMap);
		    }
		}
	    }
	    return result;
	}
    }
}
 