//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2008 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.unittest;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * Class is needed to be able to distinguish NonRigidFunctionLocations while
 * working on TestGeneration
 * 
 * @author mbender
 * 
 */
public class NRFLIdentifier {
    private final Name name;

    private final int arity;

    public NRFLIdentifier(Operator op) {
        this.name = op.name();
        this.arity = op.arity();
    }

    public boolean equals(Object o) {
        if (o instanceof NRFLIdentifier) {
            return ((NRFLIdentifier) o).arity == arity
                    && ((NRFLIdentifier) o).name.toString().equals(
                            name.toString());
        } else {
            return false;
        }
    }

    public String toString() {
        return arity + ", " + name;
    }

    public int hashCode() {
        return name.hashCode() * 17 + arity * 17 * 17;
    }
}
