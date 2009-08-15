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

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Op;

public interface Sort extends Named {
    
    Sort FORMULA  = new PrimitiveSort(new Name("Formula"));
    Sort NULL     = new NullSortImpl(new Name("Null"));
    /** this sort is the mother of all sorts for java dl 
     *  TODO: should OCLSorts extendTrans this sort too?
     */
    Sort ANY      = new AbstractNonCollectionSort(new Name("any")) {

        public ImmutableSet<Sort> extendsSorts() {            
            return DefaultImmutableSet.<Sort>nil();
        }

        public boolean extendsTrans(Sort s) {        
            return s == this;
        }

        public Equality getEqualitySymbol() {            
            return Op.EQUALS;
        }
        
    };
    
    /** @return name of the Sort */
    Name name();
    
    /**
     * For finding out whether a certain sort is super- or subsort of another
     * sort or not, please use <code>extendsTrans</code>. 
     * Using <code>extendsSorts()</code> for this purpose may lead to 
     * undesired results when dealing with array- and intersection sorts!
     * @return the sorts of the predecessors of this sort
     */
    ImmutableSet<Sort> extendsSorts();

    /**
     * returns true iff the given sort is a transitive supersort of this sort
     * or it is the same.
     */
    boolean extendsTrans(Sort s);

    /** @return equality symbol of this sort */
    Equality getEqualitySymbol();
    
}
