// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.inst;


/**
 * This is an abstract class that encapsulates an instantiation of a SchemaVariable.
 * It is needed because SchemaVariables can be instantiated as ProgramElements and as
 * Terms according to their type. But we have to put the pair (SchemaVariable,
 * term/program-element) in one map. Therefore a map from
 * SchemaVariable to InstantiationEntry is used
 * TODO: Simplify subclasses further or remove them completely as possible.
 */
public abstract class InstantiationEntry<E>  {

    private final E instantiation;
    
    /**
     * creates a new instantiation entry for the instantiation to be stored
     * @param instantiation the instantiation to be stored
     */
    InstantiationEntry(E instantiation) {
        assert instantiation != null : "An instantiation for a schemavariable cannot be null.";
        this.instantiation = instantiation;
    }

    /** returns the instantiation of the SchemaVariable
     * @return  the instantiation of the SchemaVariable
    */
    public E getInstantiation() {
        return instantiation;
    }

    @SuppressWarnings("unchecked")
    @Override
    public boolean equals(Object o) {
        if (o.getClass() == getClass()) {
            return (instantiation.equals(((InstantiationEntry<E>)o).instantiation));
        }
        return false;
    }

    @Override
    public int hashCode() {
        return instantiation.hashCode() * 37;
    }

    @Override
    public String toString() {
        return "[" + getInstantiation() + "]";
    }
}