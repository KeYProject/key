package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.LoopInvariantImpl;

import java.awt.Component;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.HashMap;

import javax.swing.BorderFactory;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollBar;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.JTextArea;
import javax.swing.ScrollPaneLayout;
import javax.swing.border.TitledBorder;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.BadLocationException;
import javax.swing.text.Document;

/**
 * @author Dreiner This class creates a Dialog to input a loop Invariant,
 *         Variant and Modifies.
 */
public class InvariantConfigurator {

    // Data
    private static InvariantConfigurator configurator = null;
    private ArrayList<String[]> invariants = null;
    private HashMap<LoopStatement, ArrayList<String[]>> mapLoopsToInvariants = null;
    private int index = 0;
    private LoopInvariant newInvariant = null;

    // Methods

    /**
     * Singleton
     */
    private InvariantConfigurator() {
	invariants = new ArrayList<String[]>();
	mapLoopsToInvariants = new HashMap<LoopStatement, ArrayList<String[]>>();
    }

    /**
     * Returns the single Instance of this class
     */
    public static InvariantConfigurator getInstance() {
	if (configurator == null) {
	    configurator = new InvariantConfigurator();
	}
	return configurator;
    }

    /**
     * Creates a Dialog. User can enter Invariant, Variant and Modifies clause.
     * The Input is parsed and a new LoopInvariant is returned. In Case of a
     * parser Exception an error-message is shown.
     * 
     * @param loopInv
     * @param services
     * @return LoopInvariant
     */
    public LoopInvariant getLoopInvariant(final LoopInvariant loopInv,
	    final Services services, final boolean requiresVariant) {
	// Check if there is a LoopInvariant
	if (loopInv == null) {
	    return null;
	}

	index = 0;
	/**
	 * The given LoopInvariant is put into the List and then handed to the
	 * Dialog.
	 */

	String[] loopInvStr = new String[3];
	if (loopInv.getInvariant(loopInv.getInternalSelfTerm(), loopInv
	        .getInternalHeapAtPre(), null) == null) {
	    loopInvStr[0] = "";
	} else {
	    loopInvStr[0] = loopInv.getInvariant(loopInv.getInternalSelfTerm(),
		    loopInv.getInternalHeapAtPre(), null).toString();
	}

	if (loopInv.getVariant(loopInv.getInternalSelfTerm(), loopInv
	        .getInternalHeapAtPre(), null) == null) {
	    loopInvStr[1] = "";
	} else {
	    loopInvStr[1] = loopInv.getVariant(loopInv.getInternalSelfTerm(),
		    loopInv.getInternalHeapAtPre(), null).toString();
	}

	if (loopInv.getModifies(loopInv.getInternalSelfTerm(), loopInv
	        .getInternalHeapAtPre(), null) == null) {
	    loopInvStr[2] = "";
	} else {
	    loopInvStr[2] = loopInv.getModifies(loopInv.getInternalSelfTerm(),
		    loopInv.getInternalHeapAtPre(), null).toString();
	}

	System.out.println("given inv:" + loopInvStr[0] + ", " + loopInvStr[1]
	        + ", " + loopInvStr[2]);

	if (!mapLoopsToInvariants.containsKey(loopInv.getLoop())) {
	    // add the given Invariant
	    invariants = new ArrayList<String[]>();
	    invariants.add(loopInvStr);
	    mapLoopsToInvariants.put(loopInv.getLoop(), invariants);
	    index = invariants.size() - 1;
	} else {
	    invariants = mapLoopsToInvariants.get(loopInv.getLoop());
	    // Check if the given invariant is in the list
	    if (!invariants.contains(loopInvStr)) {
		invariants.add(loopInvStr);
		index = invariants.size() - 1;
	    } else {
		// set the index to the currently used invariant
		index = invariants.indexOf(loopInvStr);
	    }
	}

	// Initialize the Parse
	final DefaultTermParser p = new DefaultTermParser();

	/*
	 * local class makes the dialog
	 */

	class dialog extends JDialog {
	    private JTabbedPane inputPane;

	    public dialog() {
		super(Main.getInstance(), true);

		setTitle("Invariant Configurator");
		getContentPane().setLayout(
		        new BoxLayout(getContentPane(), BoxLayout.PAGE_AXIS));
		inputPane = new JTabbedPane();

		

		// Create the loop Reprepsentation on top
		JScrollPane loopRepScrollPane = new JScrollPane();
		loopRepScrollPane.setLayout(new ScrollPaneLayout());
		String source = loopInv.getLoop().toSource();
		JTextArea loopRep = new JTextArea(source);
		loopRep.setEditable(false);
		loopRep.setBorder(BorderFactory.createTitledBorder("Loop"));
		loopRep.add(loopRepScrollPane);
		// loopPanel.add(loopPrint);
		// loopPanel.setLayout(new ScrollPaneLayout());

		getContentPane().add(loopRep);

		// Create the input panesgetContentPane
		JScrollPane scrollPane;

		JTextArea invarea = null;
		JTextArea modarea = null;
		JTextArea vararea = null;

		for (int i = 0; i < invariants.size(); i++) {

		    invarea = new JTextArea(invariants.get(i)[0]);
		    modarea = new JTextArea(invariants.get(i)[1]);
		    vararea = new JTextArea(invariants.get(i)[2]);

		    invarea.setBorder(new TitledBorder("Invariant:"));
		    modarea.setBorder(new TitledBorder("Modifies:"));
		    vararea.setBorder(new TitledBorder("Variant:"));

		    invarea.getDocument().addDocumentListener(
			    new DocumentListener() {
			        public void removeUpdate(DocumentEvent e) {
				    invUdatePerformed(e);
			        }
			        public void insertUpdate(DocumentEvent e) {
				    invUdatePerformed(e);
			        }
			        public void changedUpdate(DocumentEvent e) {
				    invUdatePerformed(e);
			        }
			    });
		    modarea.getDocument().addDocumentListener(
			    new DocumentListener() {
			        public void removeUpdate(DocumentEvent e) {
				    modUdatePerformed(e);
			        }
			        public void insertUpdate(DocumentEvent e) {
				    modUdatePerformed(e);
			        }
			        public void changedUpdate(DocumentEvent e) {
				    modUdatePerformed(e);
			        }
			    });
		    vararea.getDocument().addDocumentListener(
			    new DocumentListener() {
			        public void removeUpdate(DocumentEvent e) {
				    varUdatePerformed(e);
			        }
			        public void insertUpdate(DocumentEvent e) {
				    varUdatePerformed(e);
			        }
			        public void changedUpdate(DocumentEvent e) {
				    varUdatePerformed(e);
			        }
			    });
		    
		    

		    JPanel dummy = new JPanel();
		    dummy.add(invarea);
		    dummy.add(modarea);
		    dummy.add(vararea);
		    dummy.setLayout(new BoxLayout(dummy, BoxLayout.PAGE_AXIS));

		    scrollPane = new JScrollPane();
		    scrollPane.setLayout(new ScrollPaneLayout());
		    dummy.add(scrollPane);

		    inputPane.addTab("Inv " + i, dummy);

		}
		getContentPane().add(inputPane);

		// Add the buttons
		JPanel buttonPanel = new JPanel();
		buttonPanel.setLayout(new BoxLayout(buttonPanel,
		        BoxLayout.LINE_AXIS));
		JButton applyButton = new JButton("apply");
		JButton cancelButton = new JButton("cancel");
		JButton storeButton = new JButton("store");

		applyButton.addActionListener(new ActionListener() {
		    public void actionPerformed(ActionEvent e) {
			applyActionPerformed(e);
		    }
		});
		cancelButton.addActionListener(new ActionListener() {
		    public void actionPerformed(ActionEvent e) {
			cancelActionPerformed(e);
		    }
		});
		storeButton.addActionListener(new ActionListener() {
		    public void actionPerformed(ActionEvent e) {
			storeActionPerformed(e);
		    }
		});
	

		buttonPanel.add(applyButton);
		buttonPanel.add(storeButton);
		buttonPanel.add(cancelButton);
		getContentPane().add(buttonPanel);

		this.pack();
		this.setVisible(true);
	    }

	    // Actions
	    public void cancelActionPerformed(ActionEvent e) {
		this.dispose();

	    }

	    /**
	     * copy the current invariant to another tabe
	     * 
	     * @param e
	     */
	    public void storeActionPerformed(ActionEvent aE) {
		index = inputPane.getSelectedIndex();
		String[] invs = invariants.get(index).clone();
		
		JTextArea invarea = new JTextArea(invs[0]);
		JTextArea modarea = new JTextArea(invs[1]);
		JTextArea vararea = new JTextArea(invs[2]);
		
		invarea.setBorder(new TitledBorder("Invariant:"));
		modarea.setBorder(new TitledBorder("Modifies:"));
		vararea.setBorder(new TitledBorder("Variant:"));
		
		invarea.getDocument().addDocumentListener(
			    new DocumentListener() {
			        public void removeUpdate(DocumentEvent e) {
				    invUdatePerformed(e);
			        }
			        public void insertUpdate(DocumentEvent e) {
				    invUdatePerformed(e);
			        }
			        public void changedUpdate(DocumentEvent e) {
				    invUdatePerformed(e);
			        }
			    });
		    modarea.getDocument().addDocumentListener(
			    new DocumentListener() {
			        public void removeUpdate(DocumentEvent e) {
				    modUdatePerformed(e);
			        }
			        public void insertUpdate(DocumentEvent e) {
				    modUdatePerformed(e);
			        }
			        public void changedUpdate(DocumentEvent e) {
				    modUdatePerformed(e);
			        }
			    });
		    vararea.getDocument().addDocumentListener(
			    new DocumentListener() {
			        public void removeUpdate(DocumentEvent e) {
				    varUdatePerformed(e);
			        }
			        public void insertUpdate(DocumentEvent e) {
				    varUdatePerformed(e);
			        }
			        public void changedUpdate(DocumentEvent e) {
				    varUdatePerformed(e);
			        }
			    });
		    
		    

		    JPanel dummy = new JPanel();
		    dummy.add(invarea);
		    dummy.add(modarea);
		    dummy.add(vararea);
		    dummy.setLayout(new BoxLayout(dummy, BoxLayout.PAGE_AXIS));

		    JScrollPane scrollPane = new JScrollPane();
		    scrollPane.setLayout(new ScrollPaneLayout());
		    dummy.add(scrollPane);
		    inputPane.addTab("Inv " + (invariants.size()-1), dummy);


	    }

	    /**
	     * parse the current invariant and write it to newInvariant. If
	     * parsing fails, an error message is displayed.
	     * 
	     * @param e
	     */
	    public void applyActionPerformed(ActionEvent e) {
		index = inputPane.getSelectedIndex();
		parse();
	    }

	    public void invUdatePerformed(DocumentEvent d) {
		Document doc = d.getDocument();
		index = inputPane.getSelectedIndex();

		String[] inv = invariants.get(index);
		try {
		    inv[0] = doc.getText(0, doc.getLength());
		} catch (Exception e) {
		}

	    }
	    
	    public void modUdatePerformed(DocumentEvent d) {
		Document doc = d.getDocument();
		index = inputPane.getSelectedIndex();
		
		String[] inv = invariants.get(index);
		try { 
		    inv[1] = doc.getText(0, doc.getLength());
		}
		catch (Exception e) {
		}
	    }
	    public void varUdatePerformed(DocumentEvent d) {
		Document doc = d.getDocument();
		index = inputPane.getSelectedIndex();
		
		String[] inv = invariants.get(index);
		try { 
		    inv[2] = doc.getText(0, doc.getLength());
		}
		catch (Exception e) {
		}
	    }
	    
	    

	    /**
	     * Calls the parser and creates the Loopinvarant-attribute.
	     */
	    public void parse() {
		Term invariantTerm = null;
		Term variantTerm = null;
		Term modifiesTerm = null;
		try {
		    
		    invariantTerm = p.parse(new StringReader(invariants
			    .get(index)[0]), Sort.ANY, services, services.getNamespaces(), null);
		    variantTerm = p.parse(new StringReader(invariants
			    .get(index)[1]), Sort.ANY, services, services.getNamespaces(), null);
		    modifiesTerm = p.parse(new StringReader(invariants
			    .get(index)[2]), Sort.ANY, services, services.getNamespaces(), null);

		    /*
	             * Check if the Variant is required and empty
	             */
		    if (requiresVariant && variantTerm == null) {
			throw new ParserException("Variant is required!",
			        new Location(null, 2, 1));
		    }
		    newInvariant = new LoopInvariantImpl(loopInv.getLoop(),
			    invariantTerm, modifiesTerm, variantTerm, loopInv
			            .getInternalSelfTerm(), loopInv
			            .getInternalHeapAtPre());

		} catch (ParserException e) {
		    JOptionPane.showConfirmDialog(Main.getInstance(), e
			    .getMessage());
		}
	    }
	}

	// Create the Dialog
	dialog dia = new dialog();

	return newInvariant;
    }
}
