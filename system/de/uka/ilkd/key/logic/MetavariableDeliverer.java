// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/*
 * This class is used to create new metavariables, which are also
 * added to the variable namespace.
 */

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.Metavariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Counter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.VariableNameProposer;

public class MetavariableDeliverer {

  
    private Proof    proof;


    public MetavariableDeliverer ( Proof p_proof ) {
	proof = p_proof;
    }


    /**
     * Check whether p_sort allows metavariables
     * This is currently hard-coded and only forbidden for the
     * "numbers"-sort
     * @return true iff p_sort allows metavariables
     */
    private static boolean checkSort ( Sort p_sort, Services services ) {
	return services.getTypeConverter()
		       .getIntegerLDT()
		       .getNumberSymbol()
		       .argSort ( 0 ) != p_sort;
    }


    /**
     * Construct a unique identifier by adding a number to the base
     * name
     */
    public static int mv_Counter(String base, Goal g) {
        Counter c = g.proof().getServices().getCounter("metavar_"+base);
        return c.getCountPlusPlusWithParent(g.node());
    }


    /**
     * Create new metavariable and add it to the namespace var_ns of
     * the mediator.
     * @param name name of the variable
     * @param p_sort Sort of the variable
     * @return New metavariable, or null iff p_sort allows no
     * metavariables
     */
    public Metavariable createNewVariable ( String name,
					    Sort   p_sort ) {
	if ( !checkSort ( p_sort, proof.getServices() ) ) return null;
	final Name newName = VariableNameProposer.DEFAULT.getNewName(proof
                .getServices(), new Name(name));
        Metavariable var = new Metavariable(newName, p_sort);
	proof.getNamespaces ().variables ().add ( var );
	proof.addNameProposal(var.name());
	return var;
    }


    /**
     * Create new variable for instantiation of unknown schema
     * variables when applying taclets.
     * @param p_sort Sort of the variable
     * @return New metavariable, or null iff p_sort allows no
     * metavariables
     */
    public static Metavariable createNewMatchVariable ( String p_basename,
							Sort   p_sort,
							Services services) {
	if ( !checkSort ( p_sort, services ) ) return null;

	return Metavariable.createTemporaryVariable ( new Name ( p_basename ),
                                                      p_sort );
    }
}
