// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.soundness;

import de.uka.ilkd.key.java.Services;


public class SVPartitioningBuilder extends AbstractSkolemBuilder {

    private RawProgramVariablePrefixes rpvp;

    public SVPartitioningBuilder( SkolemSet                  p_oriSkolemSet,
				  RawProgramVariablePrefixes p_rpvp,
				  Services                   p_services ) {
        super(p_oriSkolemSet, p_services);
	rpvp = p_rpvp;
    }

    public IteratorOfSkolemSet build () {
	ListOfSkolemSet res = SLListOfSkolemSet.EMPTY_LIST;

	SVPartitioning[] partitionings = SVPartitioning.findPartitionings
	    ( rpvp.getFreeSchemaVariables (),
	      rpvp.getBoundSchemaVariables (),
	      ExpressionSkolemBuilder.findExpressionSVs ( getOriginalSkolemSet() ) );

	int i;
	for ( i = 0; i != partitionings.length; ++i )
	    res = res.prepend ( getOriginalSkolemSet()
				.setSVPartitioning(partitionings[i]) );

	return res.iterator ();
    }

}
