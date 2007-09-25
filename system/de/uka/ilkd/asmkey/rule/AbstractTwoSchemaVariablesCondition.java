// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.rule;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.inst.TermInstantiation;


/** 
 * Taclet condition that checks if two terms have the same top level
 * operator. 
 *
 * @author Hubert Schmid
 * @author Stanislas Nanchen
 */
abstract public class AbstractTwoSchemaVariablesCondition 
    extends VariableConditionAdapter {

    /** Returns the corresponding term for the given schema variable
     * from the instantiations. */
    protected static Term getInstantiation(SVInstantiations instantiations, 
					 SchemaVariable v) {
        InstantiationEntry entry = instantiations.getInstantiationEntry(v);
        if (entry == null) {
            return null;
        } else if (entry instanceof TermInstantiation) {
            return ((TermInstantiation) entry).getTerm();
        } else {
            throw new RuntimeException("instantiation for " + v + " is not valid. (" + entry + ")");
        }
    }


    /** this condition returns 'true' iff (the top level operators
     * equals iff 'equal') */
    protected final boolean equal;

    /** first schema variable that is checked */
    protected final SchemaVariable x;

    /** second schema variable that is checked */
    protected final SchemaVariable y;


    /** Creates condition for the given schema variables. If 'equal ==
     * true', the operators must match, else the operators must
     * differ. */
    public AbstractTwoSchemaVariablesCondition(boolean equal, SchemaVariable x, SchemaVariable y) {
        this.equal = equal;
        this.x = x;
        this.y = y;
    }


    /** Check the condition */
    public abstract boolean check(SchemaVariable var, SVSubstitute subst, 
				  SVInstantiations svInst, Services services);

}
