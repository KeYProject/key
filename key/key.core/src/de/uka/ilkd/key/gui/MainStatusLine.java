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

import de.uka.ilkd.key.util.TipOfTheDay;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;
import java.awt.event.ComponentListener;

import javax.swing.*;
import javax.swing.border.BevelBorder;

class MainStatusLine extends JPanel {

    private static final long serialVersionUID = -4324361226332870737L;
    private JLabel       text;
    private JPanel       progressPanel;
    private JProgressBar progressBar;
    private int          max             = 0;
    private boolean      phantomBoxAdded = false;

    MainStatusLine ( String p_initialText,
                    Font   p_font ) {
        setLayout ( new BoxLayout ( this, BoxLayout.X_AXIS ) );

        setBorder(new BevelBorder(BevelBorder.LOWERED));
        setBackground(Color.gray);
        setFont(p_font);
        setOpaque(false);

        text = new JLabel( p_initialText );

        text.setIcon(IconFactory.keyLogo(35,20));

        add ( Box.createHorizontalGlue () );
        add ( text );
        add ( Box.createHorizontalGlue () );

        createProgressPanel ();
        progressPanel.setVisible ( false );
        add ( progressPanel );

        setVisible(true);
    }

    private void createProgressPanel () {
        Dimension s;

        progressPanel = new JPanel ();
        progressPanel.setLayout ( new BoxLayout ( progressPanel,
                        BoxLayout.X_AXIS ) );

        progressBar = new JProgressBar(0, max);
        progressBar.setValue(0);
        progressBar.setStringPainted(true);

        s = new Dimension ( Short.MAX_VALUE, Short.MAX_VALUE );
        progressBar.setMaximumSize ( s );

        progressBar.setEnabled(true);
        progressPanel.add(progressBar);

        s = new Dimension ( 100, Short.MAX_VALUE );
        progressPanel.setMaximumSize ( s );	    
    }

    /**
     * The following methods should only be called from the event
     * dispatching thread
     */

    /**
     * Make the status line display a standard message
     */
    public void reset () {
        setProgressPanelVisible ( false );
        setStatusText ("Hint: "+TipOfTheDay.get());
    }

    /**
     * Set the range of values the progress bar can display (see
     * <code>setMaximum</code> of <code>ProgressBar</code>)
     */
    public void setProgressBarMaximum(int value){
        progressBar.setMaximum(value);
    }

    /**
     * Set the value the progress bar currently displays
     */
    public void setProgress(final int value){
        SwingUtilities.invokeLater(new Runnable() {

            @Override
            public void run() {
                progressBar.setValue(value);
            }
        });
    }

    /**
     * Set the visibility of the progress bar and the abort button
     */
    public void setProgressPanelVisible ( boolean p_visible ) {
        progressPanel.setVisible ( p_visible );

        if ( p_visible ) {
            setProgress ( 0 );

            // To avoid later resizing of the status line, add an
            // invisible element with the same height as the abort button
            if ( !phantomBoxAdded ) {
                phantomBoxAdded = true;
                ComponentListener phantomAdder = new ComponentAdapter () {
                    @Override
                    public void componentResized(ComponentEvent e) {
                        progressPanel.removeComponentListener ( this );
                        Dimension s = progressPanel.getSize ();
                        s           = new Dimension ( 0, (int)s.getHeight () );
                        add(Box.createRigidArea(s));
                    }
                };
                progressPanel.addComponentListener ( phantomAdder );
            }
        }
    }

    /**
     * Make the status line display the given string, don't modify
     * anything else
     */
    public void setStatusText(String s) {
        text.setText(s);
    }
}