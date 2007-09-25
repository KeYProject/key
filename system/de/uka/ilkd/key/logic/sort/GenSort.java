// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.logic.sort;

import java.util.Vector;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.ConstructorFunction;

/**
 * GenSort extends the class <code>Sort</code> with features 
 * needed for the counterexample package. A vector of constructors is 
 * added and a couple of functions to add, return and print
 * the constructors. At the moment there is no equality for generated sorts.
 *
 * To get a useful GenSort object you initialize it via 
 * <code>new GenSort(name)</code> and then add the constructors with 
 * <code>addConstructor(...)</code>
 *
 * @author Sonja Pieper
 * @version 0.1, 07/08/01
 **/

public class GenSort extends de.uka.ilkd.key.logic.sort.PrimitiveSort {

    private Vector constructors;

    /**
     * creates a new GenSort with a Name and no constructors.
     *
     * @param name the name of the new sort
     */
    public GenSort(Name name){
	super(name);
	constructors = new Vector();
    }

    /**
     * With this method you can add a constructor to any <code>GenSort</code>. 
     * This is where the actual constructor objects are generated.
     *
     * @param name the name of the new constructor
     * @param aos the sorts of the parameters
     */
    public void addConstructor(Name name, ArrayOfGenSort aos){
	ConstructorFunction c = new ConstructorFunction(name,this,aos);
	constructors.addElement(c);
    }

    public void addConstructor(ConstructorFunction cf){
	constructors.addElement(cf);
    }

    
    // the rest is just candy:


    /**
     * This function comes in useful if you need to do something with
     * the constructors of the sort you are working on.
     *
     * @return The constructors of the generated sort as a vector.
     */
    public Vector getConstructors(){
	return constructors;
    }

    /**
     * Prints the sort together with its constructors.
     * The toString() functions is inherited from sort,
     * so if you want to printout the sort with its
     * constructors (for whatever reason) use this function.
     * 
     * @return something like "sortname genby { con1 con2 }"
     */
    public String toString(){
	String s = new String(this.name()+" genby { ");
	for(int i=0;i<constructors.size();i++){
	    s = s + constructors.elementAt(i);
	}
	s = s + "}";
	return s;
    }

}

