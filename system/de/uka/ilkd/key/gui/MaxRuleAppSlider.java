// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import java.util.Hashtable;
import java.util.LinkedList;
import java.util.Iterator;

import javax.swing.BorderFactory;
import javax.swing.JLabel;
import javax.swing.JSlider;
import javax.swing.SwingConstants;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

public class MaxRuleAppSlider extends JSlider {
    private static final int MAX_RULE_APPS_LOG10 = 5;
    private final static String TEXT = "Max. Rule Applications: ";
    private KeYMediator mediator;
    private static LinkedList<MaxRuleAppSlider> allInstances = new LinkedList<MaxRuleAppSlider>();

    public MaxRuleAppSlider(KeYMediator mediator) {
        super(SwingConstants.HORIZONTAL, 0, MAX_RULE_APPS_LOG10*9, 0);

        this.mediator = mediator;
        
        // set up slider labels
        Hashtable<Integer, JLabel> labelTable = new Hashtable<Integer, JLabel>();

        for ( int n = 0; n <= MAX_RULE_APPS_LOG10; n++ ) {
            int val = (int)Math.pow(10, n);
            JLabel l = new JLabel ( ""+val );
            l.setFont(l.getFont().deriveFont(9F));
            labelTable.put(new Integer ( n*9 ), l);
        }

        setLabelTable ( labelTable );
        setPaintLabels ( true );

        // show ticks
        setMajorTickSpacing ( 9 );
        setMinorTickSpacing ( 1 );
        setPaintTicks ( true );

        // add change listener
        addChangeListener( new ChangeListener() {
            public void stateChanged ( ChangeEvent e ) {
                int n = getValue();
                int major = n / 9;
                int minor = n % 9;
                int val = (minor+1)*(int)Math.pow(10, major);
                MaxRuleAppSlider.this.mediator.setMaxAutomaticSteps ( val );
                setTitle ( val );
		updateAllSliders();
            }
        });
	
        setTitle(0);

	allInstances.add(this);
    }
    
    public void setPos(int maxRuleApps) {
        if ( maxRuleApps > 0 ) {
            int major = (int)(Math.log ( maxRuleApps ) / Math.log ( 10 ));
            int minor = maxRuleApps / (int)Math.pow(10, major) - 1;
            int initPos = Math.max ( 0, Math.min ( MAX_RULE_APPS_LOG10*9,
                                                   major * 9 + minor ));
            setValue(initPos);
        }
    }
    
    private void setTitle(int maxRuleApps) {
        setBorder(BorderFactory.createTitledBorder(TEXT+maxRuleApps));
    }
    
    public void refresh() {
        final int steps = mediator.getMaxAutomaticSteps();
        setPos(steps);
        setTitle(steps);
    }

    private void updateAllSliders(){
	Iterator<MaxRuleAppSlider> it = allInstances.iterator();
	while(it.hasNext()){
	    it.next().refresh();
	}
    }

    public void setMediator(KeYMediator mediator) {
        this.mediator = mediator;
    }
}
