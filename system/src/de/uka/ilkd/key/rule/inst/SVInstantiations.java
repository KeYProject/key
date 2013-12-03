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


package de.uka.ilkd.key.rule.inst;

import java.util.Iterator;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Debug;

/**
 * This class wraps a ImmMap<SchemaVariable,InstantiationEntry> and is used to
 * store instantiations of schemavariables. The class is immutable, this means
 * changing its content will result in creating a new object.
 */
public class SVInstantiations {
    /** the empty instantiation */
    public static final SVInstantiations EMPTY_SVINSTANTIATIONS = new SVInstantiations();
    
    /**
     * the context itself is not realised as a schemavariable, therefore we need
     * here a dummy SV for a more unified handling (key in map)
     */
    private static final SchemaVariable CONTEXTSV = SchemaVariableFactory
            .createProgramSV(new ProgramElementName("Context"),
                    new ProgramSVSort(new Name("ContextStatementBlock")) {
                        public boolean canStandFor(ProgramElement pe,
                                Services services) {
                            return true;
                        }
                    },
                    false); // just a dummy SV for context


    /** the map with the instantiations to logic terms */
    private final ImmutableMap<SchemaVariable,InstantiationEntry> map;

    /**
     * just a list of "interesting" instantiations: these instantiations are not
     * 100% predetermined and worth saving in a proof
     */
    private final ImmutableMap<SchemaVariable,InstantiationEntry> interesting;
    
    /**
     * updates may be ignored when matching, therefore they need to be added
     * after the application around the added/replaced parts. These are stored
     * in this list
     */
    private final ImmutableList<UpdateLabelPair> updateContext;

    /** instantiations of generic sorts */
    private GenericSortInstantiations genericSortInstantiations 
    	= GenericSortInstantiations.EMPTY_INSTANTIATIONS;

    /** additional conditions for the generic sorts */
    private final ImmutableList<GenericSortCondition> genericSortConditions;

    /** integer to cache the hashcode */
    private int hashcode = 0;

    /** creates a new SVInstantions object with an empty map */
    private SVInstantiations() {
	genericSortConditions = ImmutableSLList.<GenericSortCondition>nil();
	updateContext = ImmutableSLList.<UpdateLabelPair>nil();
        map = DefaultImmutableMap.<SchemaVariable,InstantiationEntry>nilMap();
	interesting = DefaultImmutableMap.<SchemaVariable,InstantiationEntry>nilMap();
    }

    /**
     * creates a new SVInstantions object using the given map
     * 
     * @param map
     *            the ImmMap<SchemaVariable,InstantiationEntry> with the
     *            instantiations
     */
    private SVInstantiations(ImmutableMap<SchemaVariable,InstantiationEntry> map,
            ImmutableMap<SchemaVariable,InstantiationEntry> interesting,
            ImmutableList<UpdateLabelPair> updateContext,
            ImmutableList<GenericSortCondition> genericSortConditions) {
        this(map,
             interesting, 
             updateContext,
             GenericSortInstantiations.EMPTY_INSTANTIATIONS,
             genericSortConditions);
    }

    
    private SVInstantiations(ImmutableMap<SchemaVariable,InstantiationEntry> map,
            ImmutableMap<SchemaVariable,InstantiationEntry> interesting,
            ImmutableList<UpdateLabelPair> updateContext,
            GenericSortInstantiations genericSortInstantiations,
            ImmutableList<GenericSortCondition> genericSortConditions) {
        this.map = map;
        this.interesting = interesting;
        this.updateContext = updateContext;
        this.genericSortInstantiations = genericSortInstantiations;
        this.genericSortConditions = genericSortConditions;  
    }

    
    public GenericSortInstantiations getGenericSortInstantiations() {
        return genericSortInstantiations;
    }

    
    public ImmutableList<GenericSortCondition> getGenericSortConditions() {
        return genericSortConditions;
    }

    /**
     * adds the given pair to the instantiations. If the given SchemaVariable
     * has been instantiated already, the new pair is taken without a warning.
     * 
     * @param sv
     *            the SchemaVariable to be instantiated
     * @param subst
     *            the Term the SchemaVariable is instantiated with
     * @return SVInstantiations the new SVInstantiations containing the given
     *         pair
     */
    public SVInstantiations add(SchemaVariable sv, 
	    			Term subst, 
	    			Services services) {
        return add(sv, new TermInstantiation(sv, subst), services);
    }


    public SVInstantiations add(ModalOperatorSV sv,
            			Operator op,
            			Services services) {
        return add(sv, new OperatorInstantiation(sv, op), services);
    }


    public SVInstantiations addInteresting(SchemaVariable sv,
	    				   Term subst,
	    				   Services services) {
        return addInteresting(sv,
        		      new TermInstantiation(sv, subst),
        		      services);
    }


    public SVInstantiations add(SchemaVariable sv,
			        ProgramList pes,
	    		        Services services) {
        return add(sv,
                   new ProgramListInstantiation(sv, pes.getList()),
                   services);
    }

    public SVInstantiations add(SchemaVariable sv, 
            ImmutableArray<TermLabel> labels,
            Services services) {
        return add(sv, 
                new TermLabelInstantiationEntry(sv, labels), 
                services);
    }


    public SVInstantiations addList(SchemaVariable sv,
	    		            Object[] list,
	    		            Services services) {
        return add(sv,
        	   new ListInstantiation(
                           sv,
        		   ImmutableSLList.<Object>nil().prepend(list)),
                   services);
    }



    /** adds the given pair to the instantiations. If the given
     * SchemaVariable has been instantiated already, the new pair is
     * taken without a warning.
     * @param sv the SchemaVariable to be instantiated
     * @param pe the ProgramElement the SchemaVariable is instantiated with
     * @return SVInstantiations the new SVInstantiations containing
     * the given pair
     */
    public SVInstantiations add(SchemaVariable sv,
	    			ProgramElement pe,
	    			Services services) {
	return add(sv, new ProgramInstantiation(sv, pe), services);
    }


    public SVInstantiations addInteresting(SchemaVariable sv,
	    				   ProgramElement pe,
	    				   Services services) {
	return addInteresting(sv, new ProgramInstantiation(sv, pe), services);
    }

    public SVInstantiations addInterestingList(SchemaVariable sv,
					       Object[] list,
	    				       Services services) {
        return addInteresting(
                sv,
                new ListInstantiation(sv, ImmutableSLList.<Object>nil().prepend(list)),
                services);
    }



    /**
     * adds the given pair to the instantiations for the context.If the context
     * has been instantiated already, the new pair is taken without a warning.
     *
     * @param prefix
     *            the PosInProgram describing the prefix
     * @param postfix
     *            the PosInProgram describing the postfix
     * @param activeStatementContext
     *            the ExecutionContext of the first active statement
     * @param pe
     *            the ProgramElement the context positions are related to
     * @return SVInstantiations the new SVInstantiations containing the given
     *         pair
     */
    public SVInstantiations add(PosInProgram prefix,
	    			PosInProgram postfix,
				ExecutionContext activeStatementContext,
	    			ProgramElement pe,
	    			Services services) {
        return add(CONTEXTSV,
                   new ContextInstantiationEntry(CONTEXTSV,
                                                 prefix,
                                                 postfix,
                                                 activeStatementContext,
                                                 pe),
                   services);
    }


    // the following two exceptions are created statically for performance
    private static final SortException INCOMPATIBLE_INSTANTIATION_EXCEPTION = new SortException(
            "Sort of SV " + "is not compatible with its "
                    + "instantiation's sort\n"
                    + "(This exception object is static)");

    private static final IllegalInstantiationException CONVERT_INSTANTIATION_EXCEPTION = new SortException(
            "Instantiation of SV " + "cannot be converted to logic\n"
                    + "(This exception object is static)");

    private static final SortException UNSOLVABLE_SORT_CONDITIONS_EXCEPTION = new SortException(
            "Conditions for sorts" + " cannot be satisfied\n"
                    + "(This exception object is static)");

    private SVInstantiations checkSorts(InstantiationEntry p_entry,
            				boolean p_forceRebuild,
            				Services services) {
        Boolean b = getGenericSortInstantiations().checkSorts(p_entry);

        if (b == null) {
            return rebuildSorts(services);
        } else if (!b.booleanValue()) {
            throw INCOMPATIBLE_INSTANTIATION_EXCEPTION;
        }
        if (p_forceRebuild) {
            return rebuildSorts(services);
        }
        return this;
    }

    private SVInstantiations checkCondition(GenericSortCondition p_c,
            				    boolean p_forceRebuild,
            				    Services services) {
        Boolean b = getGenericSortInstantiations().checkCondition(p_c);

        if (b == null)
            return rebuildSorts(services);
        else if (!b.booleanValue())
            throw UNSOLVABLE_SORT_CONDITIONS_EXCEPTION;
        if (p_forceRebuild)
            return rebuildSorts(services);
        return this;
    }

    private SVInstantiations rebuildSorts(Services services) {
        genericSortInstantiations 
        	= GenericSortInstantiations.create(map.entryIterator(), 
        					   getGenericSortConditions(),
        					   services);
        return this;
    }

    /**
     * adds the given pair to the instantiations. If the given SchemaVariable
     * has been instantiated already, the new pair is taken without a warning.
     * 
     * @param sv
     *            the SchemaVariable to be instantiated
     * @param entry
     *            the InstantiationEntry
     * @return SVInstantiations the new SVInstantiations containing the given
     *         pair
     */
    public SVInstantiations add(SchemaVariable sv, 
	    			InstantiationEntry entry,
	    			Services services) {
        return new SVInstantiations(map.put(sv, entry), 
        			    interesting(),
                		    getUpdateContext(), 
                		    getGenericSortInstantiations(),
                		    getGenericSortConditions())
        	.checkSorts(entry, false, services);
    }

    public SVInstantiations addInteresting(SchemaVariable sv,
            				   InstantiationEntry entry,
            				   Services services) {
        return new SVInstantiations(map.put(sv, entry), 
        			    interesting().put(sv, entry), 
        			    getUpdateContext(), 
        			    getGenericSortInstantiations(),
        			    getGenericSortConditions())
        	.checkSorts(entry, false, services);
    }

    
    public SVInstantiations addInteresting(SchemaVariable sv, 
            				   Name name,
            				   Services services) {
        SchemaVariable existingSV = lookupVar(sv.name());
        Name oldValue = (Name) getInstantiation(existingSV);
        if(name.equals(oldValue)) {
            return this; // already have it
        } else if(oldValue != null) {
            throw new IllegalStateException(
                "Trying to add a second name proposal for " + sv +
                ": " + oldValue + "->" + name);
        } else {
            // otherwise (nothing here yet) add it    
            return addInteresting(sv, 
        			  new NameInstantiationEntry(sv, name),
        			  services);
        }
    }
    
    
    /**
     * replaces the given pair in the instantiations. If the given
     * SchemaVariable has been instantiated already, the new pair is taken
     * without a warning.
     * 
     * @param sv
     *            the SchemaVariable to be instantiated
     * @param entry
     *            the InstantiationEntry the SchemaVariable is instantiated with
     */
    public SVInstantiations replace(SchemaVariable sv, 
	    			    InstantiationEntry entry,
	    			    Services services) {
        return new SVInstantiations(map.remove(sv).put(sv, entry),
                		    interesting(), 
                		    getUpdateContext(), 
                		    getGenericSortConditions())
                      .checkSorts(entry, true, services);
    }

    /**
     * adds the schemvariable to the set of interesting ones
     * @throws IllegalInstantiationException, if sv has not yet been instantiated
     */
    public SVInstantiations makeInteresting(SchemaVariable sv, 
	    				    Services services) {
        final InstantiationEntry entry = getInstantiationEntry(sv);
        
        if (entry == null) {
            throw new IllegalInstantiationException(sv + 
                    " cannot be made interesting. As it is not yet in the map.");
        }
        
        return new SVInstantiations(map,
                interesting().put(sv, entry), getUpdateContext(), 
                getGenericSortConditions()).checkSorts(entry, true, services);
                
    }

    
    /**
     * replaces the given pair in the instantiations. If the given
     * SchemaVariable has been instantiated already, the new pair is taken
     * without a warning.
     * 
     * @param sv
     *            the SchemaVariable to be instantiated
     * @param term
     *            the Term the SchemaVariable is instantiated with
     */
    public SVInstantiations replace(SchemaVariable sv, 
	    			    Term term, 
	    			    Services services) {
        return replace(sv, new TermInstantiation(sv, term), services);
    }

    /**
     * replaces the given pair in the instantiations. If the given
     * SchemaVariable has been instantiated already, the new pair is taken
     * without a warning.
     * 
     * @param sv
     *            the SchemaVariable to be instantiated
     * @param pe
     *            the ProgramElement the SchemaVariable is instantiated with
     */
    public SVInstantiations replace(SchemaVariable sv, 
	    			    ProgramElement pe,
	    			    Services services) {
        return replace(sv, new ProgramInstantiation(sv, pe), services);
    }

    /**
     * replaces the given pair in the instantiations. If the given
     * SchemaVariable has been instantiated already, the new pair is taken
     * without a warning.
     * 
     * @param sv
     *            the SchemaVariable to be instantiated
     * @param pes
     *            the ArrayOf<t> the SchemaVariable is instantiated
     *            with
     */
    public SVInstantiations replace(SchemaVariable sv, 
	    			    ImmutableArray<ProgramElement> pes,
	    			    Services services) {
        return replace(sv, new ProgramListInstantiation(sv, pes), services);
    }

    /**
     * replaces the given pair in the instantiations. If the context has been
     * instantiated already, the new pair is taken without a warning.
     * 
     * @param prefix
     *            the PosInProgram describing the position of the first
     *            statement after the prefix
     * @param postfix
     *            the PosInProgram describing the position of the statement just
     *            before the postfix
     * @param activeStatementContext
     *            the ExecutionContext of the first active statement
     * @param pe
     *            the ProgramElement the context positions are related to
     */
    public SVInstantiations replace(PosInProgram prefix, 
	    			    PosInProgram postfix,
	    			    ExecutionContext activeStatementContext, 
	    			    ProgramElement pe,
	    			    Services services) {
        return replace(CONTEXTSV, 
        	       new ContextInstantiationEntry(CONTEXTSV,
        		                             prefix, 
        		                             postfix, 
        		                             activeStatementContext, 
        		                             pe),
        	       services);
    }
    

    /**
     * returns true iff the sv has been instantiated already
     * 
     * @return true iff the sv has been instantiated already
     */
    public boolean isInstantiated(SchemaVariable sv) {
        return map.containsKey(sv);
    }

    /**
     * returns the instantiation of the given SchemaVariable
     * 
     * @return the InstantiationEntry the SchemaVariable will be instantiated
     *         with, null if no instantiation is stored
     */
    public InstantiationEntry getInstantiationEntry(SchemaVariable sv) {
        return map.get(sv);
    }

    /**
     * returns the instantiation of the given SchemaVariable
     * 
     * @return the Object the SchemaVariable will be instantiated with, null if
     *         no instantiation is stored
     */
    public Object getInstantiation(SchemaVariable sv) {
        final InstantiationEntry entry = getInstantiationEntry(sv);
        return entry == null ? null : entry.getInstantiation();
    }

    /**
     * returns the instantiation of the given SchemaVariable as Term. If the
     * instantiation is a program element it is tried to convert it to a term
     * otherwise an exception is thrown
     * 
     * @return the Object the SchemaVariable will be instantiated with, null if
     *         no instantiation is stored
     */
    public Term getTermInstantiation(SchemaVariable sv, 
	    			     ExecutionContext ec,
	    			     Services services) {
        final Object inst = getInstantiation(sv);
        if (inst == null) {
            return null;
        } else if (inst instanceof Term) {
            return (Term) inst;
        } else if (inst instanceof ProgramElement) {
            return services.getTypeConverter().convertToLogicElement(
                    (ProgramElement) inst, ec);
        } else {
            throw CONVERT_INSTANTIATION_EXCEPTION;
        }
    }

    /** adds an update to the update context 
    * @param updateApplicationlabels the ITermLabels attached to the application operator term 
    */
    public SVInstantiations addUpdate(Term update, ImmutableArray<TermLabel> updateApplicationlabels) {
	assert update.sort() == Sort.UPDATE;
        return new SVInstantiations(map, interesting(), updateContext
                .append(new UpdateLabelPair(update, updateApplicationlabels)),
                getGenericSortInstantiations(), getGenericSortConditions());
    }
    
    public static class UpdateLabelPair {
       private Term update;
       
       private ImmutableArray<TermLabel> updateApplicationlabels;

      public UpdateLabelPair(Term update, ImmutableArray<TermLabel> updateApplicationlabels) {
         this.update = update;
         this.updateApplicationlabels = updateApplicationlabels;
      }

      public Term getUpdate() {
         return update;
      }

      public ImmutableArray<TermLabel> getUpdateApplicationlabels() {
         return updateApplicationlabels;
      }

      @Override
      public int hashCode() {
         return update.hashCode() + 
                updateApplicationlabels.hashCode() * 7;
      }

      @Override
      public boolean equals(Object obj) {
         if (obj instanceof UpdateLabelPair) {
            return update.equals(((UpdateLabelPair) obj).getUpdate()) &&
                   updateApplicationlabels.equals(((UpdateLabelPair) obj).getUpdateApplicationlabels());
         }
         else {
            return false;
         }
      }
    }
    
    public SVInstantiations addUpdateList(ImmutableList<UpdateLabelPair> updates) {
       return new SVInstantiations(map, interesting(), updates,
               getGenericSortInstantiations(), getGenericSortConditions());
   }


    public SVInstantiations clearUpdateContext() {
        return new SVInstantiations(map, interesting(),
                ImmutableSLList.<UpdateLabelPair>nil(), getGenericSortInstantiations(),
                getGenericSortConditions());
    }

    /**
     * returns the instantiation entry for the context "schema variable" or null
     * if non such exists
     */
    public ContextInstantiationEntry getContextInstantiation() {
        final InstantiationEntry entry = getInstantiationEntry(CONTEXTSV);
        return (ContextInstantiationEntry) entry;
    }

    /**
     * returns iterator of the SchemaVariables that have an instantiation
     * 
     * @return the Iterator<SchemaVariable>
     */
    public Iterator<SchemaVariable> svIterator() {
        return map.keyIterator();
    }

    /**
     * returns iterator of the mapped pair (SchemaVariables, InstantiationEntry)
     * 
     * @return the Iterator<IEntry><SchemaVariable,InstantiationEntry>
     */
    public Iterator<ImmutableMapEntry<SchemaVariable,InstantiationEntry>> pairIterator() {
        return map.entryIterator();
    }

    /**
     * returns the number of SchemaVariables of which an instantiation is known
     * 
     * @return int that is the number of SchemaVariables of which an
     *         instantiation is known
     */
    public int size() {
        return map.size();
    }

    /**
     * returns true iff no instantiation of SchemaVariables are known
     */
    public boolean isEmpty() {
        return map.isEmpty();
    }

    /**
     * returns the update context
     * 
     * @return the update context
     */
    public ImmutableList<UpdateLabelPair> getUpdateContext() {
        return updateContext;
    }

    /**
     * returns true if the given object and this one have the same mappings
     * 
     * @return true if the given object and this one have the same mappings
     */
    public boolean equals(Object obj) {
        final SVInstantiations cmp;
        if (!(obj instanceof SVInstantiations)) {
            return false;
        } else {
            cmp = (SVInstantiations) obj;
        }
        if (size() != cmp.size() || 
                !getUpdateContext().equals(cmp.getUpdateContext())) {
            return false;
        }
      
        final Iterator<ImmutableMapEntry<SchemaVariable,InstantiationEntry>> it = pairIterator();
        while (it.hasNext()) {
            final ImmutableMapEntry<SchemaVariable,InstantiationEntry> e = it.next();
            final Object inst = e.value().getInstantiation();
            assert inst != null : "Illegal null instantiation.";
            if (!inst.equals(cmp.getInstantiation(e.key()))) {
                return false;
            }
        }
        return true;
        
    }

    public int hashCode() {
        if (hashcode == 0) {
            int result = 37 * getUpdateContext().hashCode() + size();
            final Iterator<ImmutableMapEntry<SchemaVariable,InstantiationEntry>> it = 
                pairIterator();
            while (it.hasNext()) {
                final ImmutableMapEntry<SchemaVariable,InstantiationEntry> e = it.next(); 
                result = 37 * result + e.value().getInstantiation().hashCode() + 
                  e.key().hashCode();
            }
            hashcode = result == 0 ? 1 : result;
        }
        return hashcode;
    }

    public SVInstantiations union(SVInstantiations other, Services services) {
        ImmutableMap<SchemaVariable,InstantiationEntry> result = map;

        final Iterator<ImmutableMapEntry<SchemaVariable,InstantiationEntry>> 
	    it = other.map.entryIterator();
        
        while (it.hasNext()) {
            final ImmutableMapEntry<SchemaVariable,InstantiationEntry> entry = it.next();
            result = result.put(entry.key(), entry.value());
        }
        
        ImmutableList<UpdateLabelPair> updates = ImmutableSLList.<UpdateLabelPair>nil();
        
        if (other.getUpdateContext().isEmpty()) {
            updates = getUpdateContext();
        } else if (getUpdateContext().isEmpty()) {
            updates = other.getUpdateContext();
        } else if (!getUpdateContext().equals(other.getUpdateContext())) {
            Debug.fail("The update context of one of"
                    + " the instantiations has to be empty or equal.");
        } else {
            updates = other.getUpdateContext();
        }
        return new SVInstantiations(result, interesting(), updates,
                getGenericSortConditions()).rebuildSorts(services);
    }

    public ImmutableMap<SchemaVariable,InstantiationEntry> interesting() {
        return interesting;
    }


    @Override
    public String toString() {
        StringBuffer result = new StringBuffer("SV Instantiations: ");
        return (result.append(map.toString())).toString();
    }

    /**
     * Add the given additional condition for the generic sort instantiations
     */
    public SVInstantiations add(GenericSortCondition p_c, 
	    		        Services services) throws SortException {
        return new SVInstantiations(map, interesting(), getUpdateContext(),
                getGenericSortInstantiations(), getGenericSortConditions()
                        .prepend(p_c)).checkCondition(p_c, false, services);
    }

    public ExecutionContext getExecutionContext() {
	final ContextInstantiationEntry cte = getContextInstantiation();	
	if (cte != null) {
	    return cte.activeStatementContext();
	} else {
	    return null;
	}
    }
    
    public ImmutableMapEntry<SchemaVariable,InstantiationEntry> lookupEntryForSV(Name name) {
        final Iterator<ImmutableMapEntry<SchemaVariable,InstantiationEntry>> it = 
            map.entryIterator();
        while (it.hasNext()) {
            final ImmutableMapEntry<SchemaVariable,InstantiationEntry> e = it.next();
            if (e.key().name().equals(name)) return e;
        }
        return null; // handle this better!
    }
    
    public SchemaVariable lookupVar(Name name) {
	final ImmutableMapEntry<SchemaVariable,InstantiationEntry> e = 
            lookupEntryForSV(name);
	return e == null ? null : e.key(); // handle this better!
    }
    
    public Object lookupValue(Name name) {
        final ImmutableMapEntry<SchemaVariable,InstantiationEntry> e = 
            lookupEntryForSV(name);
        return e == null ? null : e.value().getInstantiation(); 
    }
}
