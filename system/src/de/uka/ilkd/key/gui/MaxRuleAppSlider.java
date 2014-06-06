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

package de.uka.ilkd.key.gui;

import java.util.Hashtable;
import java.util.LinkedList;

import javax.swing.BorderFactory;
import javax.swing.JLabel;
import javax.swing.JSlider;
import javax.swing.SwingConstants;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

public class MaxRuleAppSlider extends JSlider {
    /**
     * 
     */
    private static final long serialVersionUID = 5810499328583797609L;
    private static final int MAX_RULE_APPS_LOG10 = 6;
    private final String text;
    private KeYMediator mediator;
    private static LinkedList<MaxRuleAppSlider> allInstances = new LinkedList<MaxRuleAppSlider>();

    public MaxRuleAppSlider(KeYMediator mediator, String text) {
        super(SwingConstants.HORIZONTAL, 0, MAX_RULE_APPS_LOG10*9, 0);
        this.text = text;

        this.mediator = mediator;
        
        // set up slider labels
        Hashtable<Integer, JLabel> labelTable = new Hashtable<Integer, JLabel>();

        for ( int n = 0; n <= MAX_RULE_APPS_LOG10; n++ ) {
            int val = (int)Math.pow(10, n);
            String sval = ""+(val >= 10000? val >= 1000000? (val/1000000)+"M": (val/1000)+"k" : +val);
            JLabel l = new JLabel ( ""+sval );
            l.setFont(l.getFont().deriveFont(9F));
            labelTable.put(Integer.valueOf ( n*9 ), l);
        }

        setLabelTable ( labelTable );
        setPaintLabels (true);

        // show ticks
        setMajorTickSpacing ( 9 );
        setMinorTickSpacing ( 1 );
        setPaintTicks ( true );

        // add change listener
        addChangeListener( new ChangeListener() {
            public void stateChanged ( ChangeEvent e ) {
                int val = getPos();
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
    
    public int getPos() {
	int n = getValue();
	int major = n / 9;
	int minor = n % 9;
	int val = (minor+1)*(int)Math.pow(10, major);
	return val;
    }
    
    private void setTitle(int maxRuleApps) {
       setBorder(BorderFactory.createTitledBorder(text + ": " + maxRuleApps));
    }
    
    public void refresh() {
        final int steps = mediator.getMaxAutomaticSteps();
        setPos(steps);
        setTitle(steps);
    }

    private void updateAllSliders(){
        for (MaxRuleAppSlider allInstance : allInstances) {
            allInstance.refresh();
        }
    }

    public void setMediator(KeYMediator mediator) {
        this.mediator = mediator;
    }
}