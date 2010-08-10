// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;
import java.io.StringReader;

import javax.swing.*;
import javax.swing.border.BevelBorder;
import javax.swing.border.CompoundBorder;
import javax.swing.border.EmptyBorder;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;
import javax.swing.event.TableModelEvent;
import javax.swing.event.TableModelListener;
import javax.swing.table.DefaultTableCellRenderer;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.parser.SimpleTermParser;
import de.uka.ilkd.key.parser.TermParserFactory;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.ConstraintTableModel;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.Debug;


public class UserConstraintView extends JPanel {
    private static final ConstraintTableModel NULL_TABLE_MODEL
            = new ConstraintTableModel();

    /** Text fields for new equalities */
    private JTextField  newEqLeftText, newEqRightText;
    private JButton     newEqAddButton, newEqReplaceButton, delEqButton;

    /**
     * true iff the controls of the pane are activated (a proof is loaded, no
     * modal dialog in visible)
     */
    private boolean controlsActive;
    
    /** Status messages */
    private JLabel      statusLabel;
    private JLabel      constraintSatLabel;

    /** Constraint to be edited */
    private ConstraintTableModel    constraintTableModel    = null;
    private ConstraintTableListener constraintTableListener = new ConstraintTableListener ();
    private JTable                  constraintTable;

    private KeYMediator mediator                      = null;

    /** Listener for proof changes */
    private SelectionListener selectionListener       = new SelectionListener ();

    /** Listener for GUI changes */
    private ConstraintViewGUIListener guiListener     = new ConstraintViewGUIListener ();

    public UserConstraintView () {

	layoutPane();
	setVisible ( true );

	setControlsActive ( true );
	printSatisfiability ();
    }


    public void setMediator ( KeYMediator p_mediator ) {
	if ( mediator != null )
	    unregisterAtMediator ();
	
	mediator = p_mediator;
	registerAtMediator ();

	setConstraintTableModel ( mediator.getUserConstraint () );
    }


    private void setConstraintTableModel ( ConstraintTableModel p_model ) {
	if ( constraintTableModel != null )
	    unregisterAtModel ();

	constraintTableModel = p_model;

	if ( constraintTableModel != null ) {
	    constraintTable.setModel ( constraintTableModel );
	    registerAtModel ();
	} else {
	    constraintTable.setModel(NULL_TABLE_MODEL);
	}

        setControlsActive ( constraintTableModel != null );
        updateTextFields ();
	printSatisfiability ();
    }


    private void registerAtMediator () {
	mediator.addKeYSelectionListener              ( selectionListener );
	mediator.addGUIListener                       ( guiListener );
    }


    private void unregisterAtMediator () {
	mediator.removeGUIListener                    ( guiListener );
	mediator.removeKeYSelectionListener           ( selectionListener );
    }


    private void registerAtModel () {
	constraintTableModel.addTableModelListener    ( constraintTableListener );
    }


    private void unregisterAtModel () {
	constraintTableModel.removeTableModelListener ( constraintTableListener );
    }


    private void setControlsActive ( boolean p ) {
        controlsActive = p;
        
	constraintTable.setEnabled ( controlsAreActive () );
	newEqLeftText  .setEnabled ( controlsAreActive () );
	newEqRightText .setEnabled ( controlsAreActive () );
    
	updateButtons ();
    }


    /**
     * @return true iff controls of the pane should be painted enabled in
     *         principal
     */
    private boolean controlsAreActive () {
        return controlsActive && constraintTableModel != null;
    }


    /** Build everything */    
    private void layoutPane() {
	setLayout ( new GridBagLayout () );
	GridBagConstraints c = new GridBagConstraints ();
	
	c.fill       = GridBagConstraints.BOTH;
	c.gridx      = 0;
	c.gridy      = 0;
	c.gridwidth  = 1;
	c.gridheight = 1;
	c.weightx    = 1;
	c.weighty    = 1;
	add ( createConstraintPanel(), c );

	c.fill       = GridBagConstraints.BOTH;
	c.gridx      = 0;
	c.gridy      = 1;
	c.gridwidth  = 1;
	c.gridheight = 1;
	c.weightx    = 1;
	c.weighty    = 0;
	c.insets     = new Insets ( 2, 0, 0, 0 );
	add ( createStatusPanel(), c);
    }


    private JPanel createStatusPanel() {
	statusLabel=new JLabel(" ");	
	JPanel statusLine = new JPanel( new BorderLayout () );

	statusLine.add ( statusLabel,   BorderLayout.CENTER );
	statusLabel.setBorder ( new BevelBorder(BevelBorder.LOWERED) );

	return statusLine;
    }

    
    private void updateButtons () {
        final ListSelectionModel lsm = constraintTable.getSelectionModel ();
        delEqButton.setEnabled ( controlsAreActive ()
                                 && !lsm.isSelectionEmpty () );
        newEqAddButton.setEnabled ( controlsAreActive () );
        newEqReplaceButton.setEnabled ( controlsAreActive ()
                                        && !lsm.isSelectionEmpty () );
    }

    /**
     * Determine the first selected row of the table, and copy the values
     * of this row to the text fields for entering new constraints
     */
    private void updateTextFields () {
        final ListSelectionModel lsm = constraintTable.getSelectionModel ();
        if ( constraintTableModel == null || lsm.isSelectionEmpty () ) {
            newEqLeftText.setText ( "" );
            newEqRightText.setText ( "" );
        } else {
            final int row = lsm.getMinSelectionIndex ();
            newEqLeftText.setText
                ( prettyPrint ( (Term)constraintTableModel.getValueAt ( row, 0 ) ) );
            newEqRightText.setText
                ( prettyPrint ( (Term)constraintTableModel.getValueAt ( row, 1 ) ) );
        }
    }
    
    /**
     * @return the position at which a row should be inserted in the table upon
     *         executing the replace action. This is the first not selected row
     *         after a selected one.
     */
    private int replaceRowInsertionPosition () {
        final ListSelectionModel lsm = constraintTable.getSelectionModel ();
        Debug.assertFalse ( lsm.isSelectionEmpty () );
        
        int row = lsm.getMinSelectionIndex ();
        do
            ++row;
        while ( row <= lsm.getMaxSelectionIndex ()
                && lsm.isSelectedIndex ( row ) );
        
        return row;
    }
    
    /** Main area with table, text fields and buttons for adding/removing constraints */
    private JPanel createConstraintPanel() {
	JPanel             constraintPanel = new JPanel ( new GridBagLayout () );
	GridBagConstraints c               = new GridBagConstraints ();
	
	constraintTable              = new JTable ( constraintTableModel );
	constraintTable.setDefaultRenderer ( Term.class, new CellRenderer () );
        constraintTable.setPreferredScrollableViewportSize(new Dimension(300, 300));
	JScrollPane pane = new JScrollPane ( constraintTable );

	constraintTable.getSelectionModel ()
	    .addListSelectionListener ( new ListSelectionListener () {
		    public void valueChanged(ListSelectionEvent p_e) {
		        updateTextFields ();
		        updateButtons ();
		    } } );
	constraintTable.setSelectionMode ( ListSelectionModel.SINGLE_INTERVAL_SELECTION );

	newEqLeftText  = new JTextField ();
	newEqRightText = new JTextField ();

	newEqAddButton = new JButton ( "Add" );
	newEqReplaceButton = new JButton ( "Replace" );
	delEqButton    = new JButton ( "Del" );

	newEqAddButton.addActionListener ( new ActionListener () {
	    public void actionPerformed ( ActionEvent p_e ) {
	        addRow ( newEqLeftText .getText (),
	                 newEqRightText.getText (),
	                 "Added",
	                 constraintTableModel.getRowCount () );
	    } } );

	newEqReplaceButton.addActionListener ( new ActionListener () {
            public void actionPerformed (ActionEvent p_e) {
                final int index =
                    constraintTable.getSelectionModel ().getMinSelectionIndex ();
                if ( addRow ( newEqLeftText.getText (),
                              newEqRightText.getText (),
                              "Replaced",
                              replaceRowInsertionPosition () ) ) {
                    removeSelectedRows ();
                    constraintTable.changeSelection ( index, index, false, false );
                }
            } } );

	delEqButton.setEnabled ( false );
	delEqButton.addActionListener ( new ActionListener () {
		public void actionPerformed ( ActionEvent p_e ) {
		    removeSelectedRows ();
		} } );

	JLabel addLabel    = new JLabel ( "Add new Equality:" );
	
	constraintSatLabel = new JLabel ( "", SwingConstants.RIGHT );

	c.fill       = GridBagConstraints.BOTH;
	c.gridx      = 0;
	c.gridy      = 0;
	c.gridwidth  = 2;
	c.gridheight = 1;
	c.weightx    = 1;
	c.weighty    = 1;
	c.insets     = new Insets ( 0, 0, 3, 0 );
	constraintPanel.add ( pane, c );

	c.fill       = GridBagConstraints.HORIZONTAL;
	c.gridx      = 0;
	c.gridy      = 1;
	c.gridwidth  = 2;
	c.gridheight = 1;
	c.weightx    = 1;
	c.weighty    = 0;
	c.insets     = new Insets ( 0, 0, 0, 0 );
	constraintPanel.add ( constraintSatLabel, c );

	c.fill       = GridBagConstraints.NONE;
	c.anchor     = GridBagConstraints.WEST;
	c.gridx      = 0;
	c.gridy      = 2;
	c.gridwidth  = 2;
	c.gridheight = 1;
	c.weightx    = 1;
	c.weighty    = 0;
	c.insets     = new Insets ( 2, 0, 0, 0 );
	constraintPanel.add ( addLabel, c );

	c.anchor     = GridBagConstraints.CENTER;

	final JPanel textPanel = new JPanel ( new GridLayout ( 1, 2, 8, 8 ) );

	textPanel.add ( newEqLeftText );
	textPanel.add ( newEqRightText );

	c.fill       = GridBagConstraints.HORIZONTAL;
        c.gridx      = 0;
        c.gridy      = 3;
        c.gridwidth  = 2;
        c.gridheight = 1;
        c.weightx    = 1;
        c.weighty    = 0;
        c.insets     = new Insets ( 4, 0, 0, 0 );
        constraintPanel.add ( textPanel, c );
    
	final JPanel buttonPanel = new JPanel ( new GridLayout ( 1, 3, 8, 8 ) );

	buttonPanel.add ( newEqAddButton );
        buttonPanel.add ( newEqReplaceButton );
        buttonPanel.add ( delEqButton );
    
	c.fill       = GridBagConstraints.HORIZONTAL;
	c.gridx      = 0;
	c.gridy      = 4;
	c.gridwidth  = 2;
	c.gridheight = 1;
	c.weightx    = 1;
	c.weighty    = 0;
	c.insets     = new Insets ( 8, 0, 0, 0 );
	constraintPanel.add ( buttonPanel, c );


	constraintPanel.setBorder( new CompoundBorder (
		   new TitledBorder("Constraint Equalities"),
		   new EmptyBorder ( 2, 2, 2, 2 ) ) );
	
	return constraintPanel;
    }


    /**
     * Will be called when this dialog will be closed
     */
    protected void closeDlg(){
	//	mediator.freeModalAccess(this); 	
    }

    /**
     * Redraw the table, which is necessary after notational modifications.
     * %%% TODO: Somehow call this method when abbreviation settings change.
     */
    void updateTableDisplay () {
        if ( constraintTableModel != null )
            constraintTableModel.fireTableDataChanged();
    }

    
    private void printStatus ( String p_status ) {
	statusLabel.setText ( p_status );
    }


    private synchronized void printSatisfiability () {
	if ( constraintTableModel != null ) {
	    if ( constraintTableModel.getConstraint ().isSatisfiable () ) {
		constraintSatLabel.setText ( "Constraint is satisfiable" );
		constraintSatLabel.setForeground
		    ( UIManager.getColor ( "Label.foreground" ) );
	    } else {
		constraintSatLabel.setText ( "Constraint is not satisfiable" );
		constraintSatLabel.setForeground ( Color.red );
	    }
	} else
	    constraintSatLabel.setText ( "" );	    
    }


    /**
     * creates a new Termparser that parses the given string using
     * namespaces and services from the mediator
     * @param s the String to parse 
     */
    public Term parseTerm (String s) throws ParserException {        
        final SimpleTermParser parser = TermParserFactory.createInstance ();
        return parser.parse ( new StringReader ( s ),
                              null,
                              mediator.getServices (),
                              mediator.namespaces (),
                              mediator.getNotationInfo ().getAbbrevMap ());
    }

    
    /**
     * Add a new equality as a pair of strings to the model
     * 
     * @param p_performedAction
     *            a string that is used to render the status message
     * @param p_index
     *            row number at which the new equation is supposed to turn up
     * @return true iff the strings have been parsed successfully
     */
    public boolean addRow (String p_left,
                           String p_right,
                           String p_performedAction,
                           int p_index) {
	Term left, right;
        try {
            left = parseTerm ( p_left );
        } catch ( ParserException e ) {
            setErrorStatus ( e, "left" );
            Logger.getLogger ( UserConstraintView.class.getName () ).info ( e );
            displayError ( e, newEqLeftText );
            return false;
        }

	try {
            right = parseTerm ( p_right );
	} catch ( ParserException e ) {
            setErrorStatus ( e, "right" );
            Logger.getLogger ( UserConstraintView.class.getName () ).info ( e );
            displayError ( e, newEqRightText );
            return false;
        }

	// This is only valid for sort hierarchies that are trees
	if ( !( left .sort ().extendsTrans ( right.sort () ) ||
		right.sort ().extendsTrans ( left .sort () ) ) ) {
	    printStatus ( "Sorts are incompatible" );
	    return false;
	}
	
	if ( !Constraint.BOTTOM.unify ( left, right, null ).isSatisfiable () ) {
	    printStatus ( "Terms are not unifiable" );
	    return false;
	}
	
	constraintTableModel.addEquality ( left, right, p_index );

	printStatus ( p_performedAction + " Constraint" );

	return true;
    }    


    private void setErrorStatus (ParserException p_e, String p_leftRight) {
        printStatus ( "<html>Syntax error in " + p_leftRight + " term:<pre>"
                      + p_e.getMessage () + "</pre></html>" );
    }


    /**
     * Make one of the text fields react to a syntax error that occurred when
     * parsing the displayed string
     */
    private static void displayError (ParserException p_ex,
                                      JTextField p_textarea) {
        p_textarea.requestFocus ();
        if ( p_ex.getLocation () != null )
            p_textarea.setCaretPosition ( Math.min ( p_ex.getLocation ().getColumn (),
                                                     p_textarea.getColumns () ) );
    }


    private String prettyPrint (Term value) {
        Debug.assertFalse ( mediator == null );

        LogicPrinter sp = new LogicPrinter ( new ProgramPrinter ( null ),
                                             mediator.getNotationInfo (),
                                             mediator.getServices(),
                                             true );
        try {
            sp.printTerm ( value );
            return sp.toString ();
        } catch ( IOException e ) {
            throw new RuntimeException ( "IO Exception in pretty printer:\n"
                                         + e );
        }
    }


    private void removeSelectedRows () {
        int i;
        while ( ( i = constraintTable.getSelectedRow () ) != -1 )
            constraintTableModel.deleteRow ( i );
    }


    private class SelectionListener implements KeYSelectionListener {

	/** focused node has changed */
	public void selectedNodeChanged(KeYSelectionEvent e) {
	}

	/** the selected proof has changed (e.g. a new proof has been
	 * loaded) */ 
	public void selectedProofChanged(KeYSelectionEvent e) {
	    final Proof selectedProof = e.getSource().getSelectedProof();
            Runnable action = new Runnable () {
		public void run () {
                    if (selectedProof != null) {
		        setConstraintTableModel(
                            selectedProof.getUserConstraint());
                    } else {
                        setConstraintTableModel ( null );
                    }
		}
	    };
        
	    if (SwingUtilities.isEventDispatchThread())  
                action.run();
            else  SwingUtilities.invokeLater(action);
	}
	
    }


    private class ConstraintTableListener implements TableModelListener {

	public void tableChanged ( TableModelEvent p_e ) {
            Runnable action = new Runnable () {
		public void run () {
		    printSatisfiability ();
		}
	    };
	    if (SwingUtilities.isEventDispatchThread())  
                action.run();
            else  SwingUtilities.invokeLater(action);
	}

    }


    private class ConstraintViewGUIListener implements GUIListener {
	/** invoked if a frame that wants modal access is opened */
	public void modalDialogOpened(GUIEvent e) {
	    setControlsActive ( false );
	}

	/** invoked if a frame that wants modal access is closed */
	public void modalDialogClosed(GUIEvent e) {
	    setControlsActive ( true );
	}

	public void shutDown(GUIEvent e) {

	}	
    }

    private class CellRenderer extends DefaultTableCellRenderer {
        
        public Component getTableCellRendererComponent (JTable table,
                                                        Object value,
                                                        boolean isSelected,
                                                        boolean hasFocus,
                                                        int row,
                                                        int col) {
            Debug.assertTrue ( value instanceof Term );
            return super.getTableCellRendererComponent ( table,
                                                         prettyPrint ( (Term)value ),
                                                         isSelected,
                                                         hasFocus,
                                                         row,
                                                         col );
        }
}
}
