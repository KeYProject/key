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

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.util.ExtList;


/**
 * Class holding a complete partitioning of all PV- and expression
 * schema variables in disjoint, non-empty classes (expression SV are
 * treated like PVSV at this point to make type handling easier). This
 * is used to cover all possible combinations of variables
 * instantiated equally.  This class is immutable.
 */
public class SVPartitioning {
    // Arrays of the partitions this object holds
    private final SVPartition[] boundSVs;       // Bound PVSV
    private final SVPartition[] freeSVs;        // Free PVSV
    private final SVPartition[] expressionSVs;  // Expression SV

    public static SVPartitioning[]
        findPartitionings ( ListOfSchemaVariable p_freeSVs,
	  		    ListOfSchemaVariable p_boundSVs,
			    ListOfSchemaVariable p_expressionSVs ) {
	return new SVPartitioner ( p_freeSVs,
				   p_boundSVs,
				   p_expressionSVs  ).findPartitionings ();
    }

    private SVPartitioning ( SVPartition[] p_freeSVs,
    	                     SVPartition[] p_boundSVs,
    	                     SVPartition[] p_expressionSVs ) {
	boundSVs      = p_boundSVs;
    	freeSVs       = p_freeSVs;
	expressionSVs = p_expressionSVs;
    }

    SVPartitioning ( SVPartition[] p_boundSVs,
    	             SVPartition[] p_expressionSVs ) {
    	this ( null,
    	       cloneArray ( p_boundSVs ),
    	       cloneArray ( p_expressionSVs ) );
    }

    SVPartitioning setFreeSVPartitioning ( SVPartition[] p_freeSVs ) {
	return new SVPartitioning ( cloneArray ( p_freeSVs ),
	                            boundSVs,
				    expressionSVs );
    }    

    /**
     * @return the number of partitions
     */
    public int size () {
	return boundSVs.length + expressionSVs.length + freeSVs.length;
    }

    /**
     * @return true iff partition <code>p</code> does only exist of
     * expression schema variables
     */
    public boolean isExpressionSV ( int p ) {
	SchemaVariable sv = getPartition ( p ).head ();
	return sv.isProgramSV () &&
	    ((SortedSchemaVariable)sv).sort () == ProgramSVSort.EXPRESSION;
    }

    public boolean isNative ( int p ) {
    	return getPartitionHelp(p).isNative();
    }

    /**
     * @return the type of an arbitrary element of partition
     * <code>p</code> for which the type is known; <code>null</code>
     * if the type is unknown for all elements of partition
     * <code>p</code>
     */
    public KeYJavaType getType ( int p, SVTypeInfos p_svTypeInfos ) {
	return getType ( getPartition ( p ), p_svTypeInfos );
    }

    private KeYJavaType getType ( ListOfSchemaVariable p_svs,
                                  SVTypeInfos          p_svTypeInfos ) {
	IteratorOfSchemaVariable it  = p_svs.iterator ();
	SVTypeInfo               res;
	while ( it.hasNext () ) {
	    res = p_svTypeInfos.getInfo ( it.next () );
	    if ( res != null )
		return res.getType ();
	}
	return null;
    }

    /**
     * @return partition <code>p</code> as a list
     */
    public ListOfSchemaVariable getPartition ( int p ) {
	return getPartitionHelp(p).getVariables();
    }

    private SVPartition getPartitionHelp ( int p ) {
	if ( p < boundSVs.length )
	    return boundSVs[p];
	p -= boundSVs.length;
	if ( p < freeSVs.length )
	    return freeSVs[p];
	p -= freeSVs.length;
	return expressionSVs[p];
    }

    private static SVPartition[] cloneArray ( SVPartition[] p ) {
	SVPartition[] res = new SVPartition [ p.length ];
    	System.arraycopy ( p, 0, res, 0, p.length );
    	return res;
    }
}


class SVPartition {
    private final ListOfSchemaVariable variables;
    private final boolean              nativePV;
    
    SVPartition ( ListOfSchemaVariable p_variables,
    	          boolean              p_nativePV ) {
	variables = p_variables;
	nativePV  = p_nativePV;
    }

    public ListOfSchemaVariable getVariables() {
        return variables;
    }

    public boolean isNative() {
        return nativePV;
    }
}


/**
 * <p>Construct all possible partitionings for a given set of schema
 * variables, and all possibilities to instantiate each partition
 * either with a new or a native program variable.</p>
 *
 * <p>Possible optimization: Test whether native program variables
 * exist at all.</p>
 */
class SVPartitioner {

    private final SchemaVariable[] freeSVs;
    private final SVPartitioning   emptyPart;
    private final ExtList          res        = new ExtList (); 

    // Array that contains one entry for each element of
    // <code>freeSVs</code>, and that tells to which partition each
    // schema variable belongs
    private final int[]            partTable;
    
    SVPartitioner ( ListOfSchemaVariable p_freeSVs, 
		    ListOfSchemaVariable p_boundSVs,
		    ListOfSchemaVariable p_expressionSVs  ) {
    	freeSVs   = toArray ( p_freeSVs );
        emptyPart =
            new SVPartitioning ( toSingletonPartitionArray ( p_boundSVs ),
				 toSingletonPartitionArray ( p_expressionSVs ) );
        partTable = new int [ freeSVs.length ];

	// initially <code>partTable</code> does only contain
	// <code>0</code>
    }

    SVPartitioning[] findPartitionings () {
	findPartitioningsHelp ( 1 );

	return (SVPartitioning[])res.collect ( SVPartitioning.class );
    }

    /**
     * Recursive method; each call creates a further partition of
     * schema variables in all possible ways
     */
    private void findPartitioningsHelp ( int p_depth ) {
	if ( init ( p_depth ) ) {
	    do {
		findPartitioningsHelp ( p_depth + 1 );
	    } while ( step ( p_depth ) );
	} else {
	    // all schema variables belong to exactly one partition
	    createPartitioning ( p_depth - 1 );
	}
    }

    private void createPartitioning ( int p_partCount ) {
	SVPartition[] partitions = new SVPartition [ p_partCount ];
	createPartitioningHelp(p_partCount, partitions);
    }

    private void createPartitioningHelp ( int           p_code,
                                          SVPartition[] p_partitions ) {
    	if ( p_code == 0 ) {
    	    res.add ( emptyPart.setFreeSVPartitioning ( p_partitions ) );
	    return;
    	}

	final int                  index     = p_code - 1;
	final ListOfSchemaVariable variables = collectVariables ( p_code );

	// For each partition the chosen program variable
	// can be native or new
	    
	p_partitions[index] = new SVPartition ( variables, false );
	createPartitioningHelp(index, p_partitions);
	    
	p_partitions[index] = new SVPartition ( variables, true );
	createPartitioningHelp(index, p_partitions);
    }

    private ListOfSchemaVariable collectVariables ( int p_code ) {
	ListOfSchemaVariable variables = SLListOfSchemaVariable.EMPTY_LIST;
	
	for ( int j = 0; j != partTable.length; ++j ) {
	    if ( partTable[j] == p_code )
		variables = variables.prepend ( freeSVs[j] );
	}

	return variables;	
    }

    /**
     * Set the first entry of <code>partTable</code> with value
     * <code>0</code> to <code>p_code</code>
     * @return true iff a zero-entry did exist
     */
    private boolean init ( int p_code ) {
	int i;
	for ( i = 0; i != partTable.length; ++i ) {
	    if ( partTable[i] == 0 ) {
		partTable[i] = p_code;
		return true;
	    }
	}

	return false;
    }

    /**
     * Iterate through all possible configurations of
     * <code>partTable</code> that can be reached by assigning the
     * values <code>0</code> and <code>p_code</code>; thereby entries
     * having other values than <code>0</code> or <code>p_code</code>,
     * as well as the first entry with value <code>p_code</code> are
     * not modified
     * @return false iff no further configuration exists, in this case
     * <code>0</code> is assigned to all entries with value
     * <code>p_code</code>
     */
    private boolean step ( int p_code ) {
	int     i;
	boolean delay = true;
	for ( i = 0; i != partTable.length; ++i ) {
	    if ( partTable[i] == p_code ) {
		if ( delay )
		    delay = false;
		else
		    partTable[i] = 0;
	    } else if ( partTable[i] == 0 ) {
		partTable[i] = p_code;
		return true;
	    }
	}

	for ( i = 0; i != partTable.length; ++i ) {
	    if ( partTable[i] == p_code )
		partTable[i] = 0;
	}

	return false;
    }    

    private SchemaVariable[] toArray ( ListOfSchemaVariable p_list ) {
	SchemaVariable[] result = new SchemaVariable [ p_list.size () ];
	
	IteratorOfSchemaVariable it = p_list.iterator ();
	int                      i  = 0;
	while ( it.hasNext () )
	    result[i++] = it.next ();
	    
	return result; 	
    }

    private static SVPartition[]
        toSingletonPartitionArray ( ListOfSchemaVariable p_svs ) {

	SVPartition[]            result = new SVPartition [ p_svs.size () ];
	
	IteratorOfSchemaVariable it  = p_svs.iterator ();
	int                      i   = 0;
	while ( it.hasNext () ) {
	    final ListOfSchemaVariable singletonList =
	        SLListOfSchemaVariable.EMPTY_LIST.prepend ( it.next () );
            result[i++] = new SVPartition ( singletonList, false );
	}
	
	return result;
    }

}
