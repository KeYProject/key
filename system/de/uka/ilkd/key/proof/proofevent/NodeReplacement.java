// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.proofevent;


import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.Node;


/** Information about a node replacing its parent after a rule
 * application, currently giving information about added and removed
 * formulas */
public class NodeReplacement {

    Node                    node;
    Node                    parent;
    ListOfSequentChangeInfo rawChanges;
    ListOfNodeChange        changes    = null;

    /**
     * @param p_node the node this object reports about
     * @param p_parent the parent node
     * @param p_changes the complete list of changes made to the
     * original node, with the most recent change being the first
     * element of the list
     */
    public NodeReplacement ( Node                    p_node,
			     Node                    p_parent,
			     ListOfSequentChangeInfo p_changes ) {
	node       = p_node;
	parent     = p_parent;
	rawChanges = p_changes;
    }

    private void addNodeChanges () {
	if ( rawChanges != SLListOfSequentChangeInfo.EMPTY_LIST ) {
	    SequentChangeInfo sci = rawChanges.head ();
	    rawChanges            = rawChanges.tail ();

	    addNodeChanges ();
            

	    addNodeChange ( sci );
	}
    }

    private void addNodeChange ( SequentChangeInfo p_sci ) {
        IteratorOfConstrainedFormula it;
        IteratorOfFormulaChangeInfo  it2;
     
        //---
        it = p_sci.removedFormulas ( true ).iterator ();
        while ( it.hasNext () )
            addRemovedChange ( it.next (), true );

        it = p_sci.removedFormulas ( false ).iterator ();
        while ( it.hasNext () )
            addRemovedChange ( it.next (), false );

        // Information about modified formulas is currently not used
        it2 = p_sci.modifiedFormulas ( true ).iterator ();
        while ( it2.hasNext () )
            addRemovedChange ( it2.next ().getPositionOfModification ()
                    .constrainedFormula (),
                    true );

        // Information about modified formulas is currently not used
        it2 = p_sci.modifiedFormulas ( false ).iterator ();
        while ( it2.hasNext () )
            addRemovedChange ( it2.next ().getPositionOfModification ()
                    .constrainedFormula (),
                    false );

        it = p_sci.addedFormulas ( true ).iterator ();
        while ( it.hasNext () )
            addAddedChange ( it.next (), true );

        it = p_sci.addedFormulas ( false ).iterator ();
        while ( it.hasNext () )
            addAddedChange ( it.next (), false );

        // Information about modified formulas is currently not used
        it2 = p_sci.modifiedFormulas ( true ).iterator ();
        while ( it2.hasNext () )
            addAddedChange ( it2.next ().getNewFormula (), true );

        // Information about modified formulas is currently not used
        it2 = p_sci.modifiedFormulas ( false ).iterator ();
        while ( it2.hasNext () )
            addAddedChange ( it2.next ().getNewFormula (), false );

        // Information about formulas that have not been added as equal or more general 
        // formulas are already on the sequent
        it = p_sci.rejectedFormulas(true).iterator ();
        while ( it.hasNext () )
            addAddedRedundantChange ( it.next (), true );

            
        it = p_sci.rejectedFormulas(false).iterator ();
        while ( it.hasNext () )
            addAddedRedundantChange ( it.next (), false );

    
    }

    private void addAddedChange   ( ConstrainedFormula p_cf,
				    boolean            p_inAntec ) {
	Sequent     oldS  = parent.sequent ();
	Semisequent oldSS = ( p_inAntec          ?
			      oldS.antecedent () :
			      oldS.succedent  () );
	Sequent     newS  = node.sequent ();
	Semisequent newSS = ( p_inAntec          ?
			      newS.antecedent () :
			      newS.succedent  () );

	removeNodeChanges ( p_cf, p_inAntec );
	
	if ( !oldSS.contains ( p_cf ) &&
	     newSS.contains ( p_cf ) ) {
	    PosInOccurrence pio = new PosInOccurrence ( p_cf,
							PosInTerm.TOP_LEVEL,
							p_inAntec );
	    addNodeChange ( new NodeChangeAddFormula ( pio ) );
	}
    }
    
    
    /** TODO comment
     * 
     * @param p_cf
     * @param p_inAntec
     */
    private void addAddedRedundantChange(ConstrainedFormula p_cf,
            boolean p_inAntec) {

        final PosInOccurrence pio = new PosInOccurrence(p_cf, PosInTerm.TOP_LEVEL,
                p_inAntec);
        addNodeChange(new NodeRedundantAddChange(pio));

    }

    
    

    private void addRemovedChange ( ConstrainedFormula p_cf,
				    boolean            p_inAntec ) {
	Sequent     oldS  = parent.sequent ();
	Semisequent oldSS = ( p_inAntec          ?
			      oldS.antecedent () :
			      oldS.succedent  () );

	removeNodeChanges ( p_cf, p_inAntec );
	
	if ( oldSS.contains ( p_cf ) ) {
	    PosInOccurrence pio = new PosInOccurrence ( p_cf,
							PosInTerm.TOP_LEVEL,
							p_inAntec );
	    addNodeChange ( new NodeChangeRemoveFormula ( pio ) );
	}
    }

    private void addNodeChange ( NodeChange p_nc ) {
	changes = changes.prepend ( p_nc );
    }

    private void removeNodeChanges ( ConstrainedFormula p_cf,
				     boolean            p_inAntec ) {
	IteratorOfNodeChange it     = changes.iterator ();
	changes                     = SLListOfNodeChange.EMPTY_LIST;
	NodeChange           oldNC;
	PosInOccurrence      oldPio;

	while ( it.hasNext () ) {
	    oldNC = it.next ();

	    if ( oldNC instanceof NodeChangeARFormula ) {
		oldPio = ((NodeChangeARFormula)oldNC).getPos ();
		if ( oldPio.isInAntec () == p_inAntec &&
		     oldPio.constrainedFormula ().equals ( p_cf ) )
		    continue;
	    }
	    
	    addNodeChange ( oldNC );
	}
    }

    public Node                 getNode        () {
	return node;
    }

    /**
     * @return Modifications that have been made to node
     */
    public IteratorOfNodeChange getNodeChanges () {
	if ( changes == null ) {
	    changes = SLListOfNodeChange.EMPTY_LIST;
	    addNodeChanges ();
	}
	return changes.iterator ();
    }

    public String toString () {
	getNodeChanges ();
	return "Changes: " + changes;
    }
}
