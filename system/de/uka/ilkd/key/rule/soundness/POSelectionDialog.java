// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.soundness;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Vector;

import javax.swing.*;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.rule.IteratorOfNoPosTacletApp;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.SetOfNoPosTacletApp;

public class POSelectionDialog extends JDialog {

    private JList tacletList;

    private final SetOfNoPosTacletApp tacs;
    private boolean okPressed = false;

    public POSelectionDialog (Frame parent,
			      SetOfNoPosTacletApp tacs) {  
	super(parent, "Load Taclets", true);

        this.tacs=tacs;

	layoutPODialog(); 
	
	pack();
	setLocation(70,70);
	setVisible(true);
    }

    private Object[] createTacletListContents () {
    	Vector res = new Vector ();
    	IteratorOfNoPosTacletApp it = tacs.iterator ();
    	
    	while ( it.hasNext () )
    	    res.add(it.next ());
    	    
    	Object[] taclets = res.toArray();
	//  	Arrays.sort(taclets);
    	
    	return taclets;
    }

   
    public NoPosTacletApp[] getSelectedTaclets() {
    	if ( !okPressed )
    	    return new NoPosTacletApp[0];
    	Object[] sels = tacletList.getSelectedValues();
    	NoPosTacletApp[] res = new NoPosTacletApp[sels.length];
        System.arraycopy(sels,0, res, 0, sels.length);
        return res;
    }


    /** lays out the configuration dialog */
    private void layoutPODialog() {	
	JPanel listPanel = new JPanel();
	listPanel.setBorder(new TitledBorder("Select the Taclets to Load"));

	tacletList = new JList (createTacletListContents());
	tacletList.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION);
	tacletList.setSelectionInterval(0, tacletList.getModel().getSize()-1);
	tacletList.setPrototypeCellValue("just_quite_a_long_taclet_name");
	tacletList.setCellRenderer(new DefaultListCellRenderer() {

		public Component getListCellRendererComponent
		    (JList list,
		     Object value,            // value to display
		     int index,               // cell index
		     boolean isSelected,      // is the cell selected
		     boolean cellHasFocus)    // the list and the 
		                              //cell have the focus
		{
		    if (value instanceof NoPosTacletApp) {
			value = ((NoPosTacletApp)value).taclet().name();
		    }
		    return super.getListCellRendererComponent(list, value, 
							      index, 
							      isSelected, 
							      cellHasFocus);
		}
	    });
	listPanel.add(new JScrollPane(tacletList));

	JButton ok = new JButton("OK");
	ok.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent ae) {
		    okPressed = true;
		    dispose();
		}
	    });
	JButton cancel = new JButton("Cancel");
	cancel.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent ae) {
		    dispose();
		}
	    });
	
	JPanel p = new JPanel(new GridBagLayout());
	GridBagConstraints c = new GridBagConstraints();
		
	c.insets = new Insets(5,20,5,20);
	c.gridx = 0;
	p.add(ok, c);    
		
	c.gridx = 1;
	p.add(cancel, c);    
	p.setAlignmentY(JPanel.BOTTOM_ALIGNMENT);
		
	p.add(ok);
	p.add(cancel);

	getContentPane().setLayout(new BorderLayout());
	getContentPane().add(listPanel, BorderLayout.CENTER);
	getContentPane().add(p, BorderLayout.SOUTH);

    }


}
