// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.ldt;
import java.util.Vector;

import de.uka.ilkd.key.logic.Axiom;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.sort.GenSort;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * This class represents an Abstract Data Type as needed for the 
 * generation of counterexamples. It consists of a name, 'freely' 
 * (simply assumed they are) generated sorts and axioms.
 */

public class ADT implements Named{

    private Vector sorts; //contains objects of type GenSort
    private Vector axioms;//contains objects of type Axiom

    private Name name;

    /**
     * creates a new empty ADT which is not yet useful, you will 
     * need to add sorts and axioms.
     * @param n the Name of the constructor, can be anything it is 
     *          simply needed as a kind of identifier
     */
    public ADT(Name n) {
        name = n;
        sorts = new Vector();
        axioms = new Vector();
    }

    /**
     * creates a new ADT complete with sorts and axioms.
     * @param n the name of the constructor
     * @param s the vector with the generated sorts for this adt,
     *          all objects in this vector are supposed to be of Type GenSort
     * @param a the vector with the axioms for this adt all objects in 
     *          this vector are supposed to be of Type Axiom
     */
    public ADT(Name n, Vector s, Vector a) {
        name = n;
        sorts = new Vector(s);
        axioms = new Vector(a);
    }

    public Name name() {
        return name;
    }

    public void addSort(GenSort gs) {
        sorts.addElement(gs);
    }

    public void addSort(Sort s) {
        sorts.addElement(s);
    }

    public void addAxiom(Axiom a) {
        axioms.addElement(a);
    }

    public String toString() {
        String s = new String();
        return s;
    }

    public Vector getSorts(){
	return sorts;
    }

    public Vector getAxioms(){
	return axioms;
    }

}
