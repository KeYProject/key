// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.proof;

import java.util.Iterator;
import java.util.Vector;

import javax.swing.table.AbstractTableModel;

import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.incclosure.BranchRestricter;
import de.uka.ilkd.key.proof.incclosure.Sink;


/** Table model storing a raw constraint as a vector of equalities
 * (term pairs) */

public class ConstraintTableModel extends AbstractTableModel {

    /** Vector of term pairs representing equalities */
    protected Vector      entries           = new Vector ();

    /** This constraint normalized */
    protected Constraint  currentConstraint = Constraint.BOTTOM;

    public ConstraintTableModel () {}

    public Constraint getConstraint () {
	return currentConstraint;
    }

    /**
     * @return true iff p_node should be displayed as a closed
     * goal/node (i.e. it is really closed or it is part of a subtree
     * that should be displayed as closed regarding the current user
     * constraint)
     */
    public boolean displayClosed ( Node p_node ) {
	if ( p_node.isClosed () )
	    return true;
	
	
	Sink sink = p_node.getBranchSink ();
	return
	    ( sink instanceof BranchRestricter ) &&
            getConstraint ().isSatisfiable () &&
	    ( ((BranchRestricter)sink).getPathConstraint ().isAsWeakAs
	      ( getConstraint () ) );
    }

    /** Methods from AbstractTableModel */

    public int getRowCount () {
	return entries.size ();
    }

    public int getColumnCount () {
	return 2;
    }

    public Object getValueAt ( int p_row, int p_column ) {
	if ( p_column == 0 )
	    return ((PairOfTerm)entries.get ( p_row )).left;
	else
	    return ((PairOfTerm)entries.get ( p_row )).right;
    }

    public Class getColumnClass (int arg0) {
        return Term.class;
    }

    public String getColumnName ( int p_column ) {
	if ( p_column == 0 )
	    return "Left";
	else
	    return "Right";
    }

    /** Add a new equality to this constraint, consisting of a pair of
     * terms (not of Sort.FORMULA)
     * @param p_left left side of the equality
     * @param p_right right side of the equality
     */
    public void addEquality (Term p_left, Term p_right) {
        addEquality ( p_left, p_right, entries.size () );
    }

    /** 
     * Add a new equality to this constraint, consisting of a pair of
     * terms (not of Sort.FORMULA). The new pair is inserted at position
     *  <code>p_index</code>
     * @param p_left left side of the equality
     * @param p_right right side of the equality
     * @param p_index row number at which the new pair will turn up
     * @throws ArrayIndexOutOfBoundsException iff the value of
     * <code>p_index</code> is invalid, i.e. not within [0..getRowCount()]
     */
    public void addEquality (Term p_left, Term p_right, int p_index) {
        // this throws an exception for invalid <code>p_index</code>
        entries.add ( p_index, new PairOfTerm ( p_left, p_right ) );
        currentConstraint = currentConstraint.unify ( p_left, p_right, null );
        fireTableRowsInserted ( p_index, p_index );
        fireConstraintChanged ( new ConstraintTableEvent ( this ) );
    }

    /**
     * Delete one equality
     * 
     * @param p_row
     *            number of the equality, has to be within [0..getRowCount())
     */
    public void deleteRow ( int p_row ) {
	entries.remove       ( p_row );

	currentConstraint = Constraint.BOTTOM;
	Iterator   it     = entries.iterator ();
	PairOfTerm p;

	while ( it.hasNext () ) {
	    p                 = (PairOfTerm)it.next ();
	    currentConstraint = currentConstraint.unify ( p.left, p.right, null );
	}

	fireTableRowsDeleted  ( p_row, p_row );
	fireConstraintChanged ( new ConstraintTableEvent ( this ) );
    }


    /**
     * Remove the contents of the table, creating the BOTTOM
     * constraint
     */
    public void reset () {
	entries.clear         ();
	currentConstraint = Constraint.BOTTOM;
	fireTableDataChanged  ();
	fireConstraintChanged ( new ConstraintTableEvent ( this ) );
    }


    /** handle listeners */
    public synchronized void addConstraintTableListener ( ConstraintTableListener p_l ) {
	listenerList.add ( ConstraintTableListener.class, p_l );
    }

    public synchronized void removeConstraintTableListener ( ConstraintTableListener p_l ) {
	listenerList.remove ( ConstraintTableListener.class, p_l );
    }

    protected synchronized void fireConstraintChanged(ConstraintTableEvent e) {
	Object[] listeners = listenerList.getListenerList();
	for (int i = listeners.length-2; i>=0; i-=2) {
	    if (listeners[i] == ConstraintTableListener.class) {
		((ConstraintTableListener)listeners[i+1]).constraintChanged(e);
	    }
	}
    }


    /** The attribute (vector) "entries" contains objects of this class */
    private static class PairOfTerm {
	public PairOfTerm () {}

	public PairOfTerm ( Term p_left, Term p_right ) {
	    left  = p_left;
	    right = p_right;
	}
	
	public Term left;
	public Term right;
    }

}
