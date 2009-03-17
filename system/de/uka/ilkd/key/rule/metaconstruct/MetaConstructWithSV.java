// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.logic.op.ListOfSchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * This interface can be used to indicate that a program meta construct needs
 * the instantiation of certain schema variables. These are then taken into
 * consideration by the ProgramSVCollector.
 * 
 * @author MU
 * 
 */
public interface MetaConstructWithSV {

    /**
     * get a list of schema variables that are needed by this entity when
     * working given a SV instantiation set.
     * 
     * @param svInst
     *            the instatiations of SV so far.
     * @return a list of schema variables relevant for this entity;
     */
    public ListOfSchemaVariable neededInstantiations(SVInstantiations svInst);
}
