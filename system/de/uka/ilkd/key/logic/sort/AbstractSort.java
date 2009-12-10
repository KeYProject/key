// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.sort;

import java.util.Iterator;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.util.Debug;

public abstract class AbstractSort implements Sort, SortDefiningSymbols {

    public static final Name OBJECT_REPOSITORY_NAME = new Name("<get>");

    /** name of the Sort */
    protected Name name;

    /**
     * equality symbol for this sort
     */
    protected final Equality equality = Op.EQUALS;

    /**
     * cast symbol casting any sort to <em>this</em> one  
     */
    private CastFunctionSymbol castSymbol;
            
    
    protected ImmutableMap<Name,SortDependingSymbol> definedSymbols = 
        DefaultImmutableMap.<Name,SortDependingSymbol>nilMap();

    protected boolean symbolsCreated = false;

    /** creates a Sort (with a new equality symbol for this sort) */
    public AbstractSort(Name name) {
        this.name = name;
    }

    /**
     * @return the sorts of the successors of this sort
     */
    public abstract ImmutableSet<Sort> extendsSorts();

    /**
     * returns true iff given sort is a part of the transitive closure of the
     * supersorts of this sort. One might optimize by hashing %%
     */
    public boolean extendsTrans(Sort sort) {
        if (sort == this || sort == Sort.ANY) {
            return true;
        }
        
        if (!(sort instanceof ObjectSort)) {
            return false;
        }
                             
       if (sort instanceof IntersectionSort) {            
           final IntersectionSort intersect = (IntersectionSort)sort;
           for (int i = 0, sz = intersect.memberCount(); i<sz; i++) {
               final Sort s = intersect.getComponent(i);
               Debug.assertTrue(s!=null);
               if ( !this.extendsTrans(s) ) {
                   return false;
               }
           }
           return true;
       } else {
           for (Sort sort1 : extendsSorts()) {
               final Sort s = sort1;
               assert s != null;
               if (s == sort || s.extendsTrans(sort)) {
                   return true;
               }
           }
       }
       return false;
    }

    /** @return name of the Sort as String */
    public Name name() {
        return name;
    }

    /** @return equality symbol of this sort */
    public Equality getEqualitySymbol() {
        return (this == Sort.FORMULA ? Op.EQV : equality);
    }    

    /**
     * returns the cast symbol of this Sort
     * 
     * @return the cast function of this sort
     * @throws IllegalStateException
     *             if the symbols have not been created yet
     */
    public CastFunctionSymbol getCastSymbol() {
        if (castSymbol == null) {
            throw new IllegalStateException(this+":"+
                    "Symbols have to be created before "
                            + "trying to access a sort depending function.");
        }
        return castSymbol;
    }
    
    /**
     * This method returns a cast into this sort.
     */
    private SortDependingSymbol createCastSymbol() {
        Debug.assertTrue(castSymbol == null);
        castSymbol = new CastFunctionSymbol(Sort.ANY, this);
        return castSymbol;
    }
    
    
    /**
     * Creates the functions depening on this sort and adds them to the functions
     * namespace. If the functions have been already created nothing is done.   
     */
    protected void createSymbols(Namespace p_func_ns, Namespace sort_ns) {
        if (!symbolsCreated) {
            final Sort booleanSort = (Sort)sort_ns.lookup(new Name("boolean"));
            final Sort intSort     = (Sort)sort_ns.lookup(new Name("int"));
            if ( booleanSort == null || intSort == null ) {              
                return; //create symbols later
            }
            ImmutableList<SortDependingSymbol> l0 = 
                ImmutableSLList.<SortDependingSymbol>nil();
            l0 = l0.prepend(createCastSymbol()).prepend 
            ( new InstanceofSymbol (this, booleanSort)).prepend
            ( new ExactInstanceSymbol (this, booleanSort)).prepend
            ( new InstanceofSymbol(new Name("contains"), this));
            
            
            /**
             * this is a hack. Solution: Create a class Signature which is repsobsible to
             * build the required sort depending functions after all sorts have been read.
             */
            if (!(this instanceof NullSort) && 
                    (this instanceof ArraySort || 
                            this instanceof GenericSort ||             
                    (this instanceof ClassInstanceSortImpl &&                            
                            !((ClassInstanceSort)this).
                            representAbstractClassOrInterface()))) {
                l0 = l0.prepend(createInstanceRepository(intSort));
            } 
            
            addSymbols(l0);
            symbolsCreated = true;
        }
    }

    private SortDependingFunction createInstanceRepository(Sort integerSort) {
        return new SortDependingFunction
        (new Name(this.name.toString() + "::" + OBJECT_REPOSITORY_NAME.toString()), 
                this, new Sort[]{integerSort}, OBJECT_REPOSITORY_NAME, this);
    }

    /**
     * Lookup the symbol of kind "p_name", which is a sort independent
     * identifier for this symbol
     * 
     * @return Symbol with (kind) name "p_name"
     *         ("ret.getKind().equals(p_name)"), null if no such object exists
     */
    public SortDependingSymbol lookupSymbol(Name p_name) {
        return definedSymbols.get(p_name);
    }

    
    protected void addSymbols(ImmutableList<SortDependingSymbol> p) {
        for (SortDependingSymbol aP : p) {
            final SortDependingSymbol s = aP;
            definedSymbols = definedSymbols.put(s.getKind(), s);
        }
    }

    /** 
     * Adds the sort depending functions to the given function namespace if
     * possible. Functions are created if not already done 
     */
    public void addDefinedSymbols(Namespace functions, Namespace sorts) {
        if (!symbolsCreated) {
            createSymbols(functions, sorts);            
        } 
        final Iterator<SortDependingSymbol> it = 
            definedSymbols.valueIterator();        
        while (it.hasNext()) {                  
            final SortDependingSymbol sds = it.next();
            //if (functions.lookup(sds.name()) == null) {
                functions.add(sds);
            //}
        }
    }
    
    public String toString() {
        return name().toString();
    }    
}
