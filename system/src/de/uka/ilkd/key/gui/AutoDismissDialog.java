// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

/*
 * To change this template, choose Tools | Templates and open the template in
 * the editor.
 */
package de.uka.ilkd.key.gui;

import java.awt.Color;
import java.awt.Frame;
import java.util.Timer;
import java.util.TimerTask;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JPanel;



/**
 *
 * @author christoph
 */
public class AutoDismissDialog {

    public static final int DEFAULT_DELAY = 5000;
    public static final int DEFAULT_RATE = 25;
    public static final int DEFAULT_DELAY_START_TO_DISPOSE = 2000;
    public static final int DEFAULT_DELAY_DISPOSE_TO_END = 1000;
    private final JDialog dialog;
    private final JPanel messagePanel;
    private final Timer timer;
    private int remainingSteps;
    private final int delay, rate, delayStartToDispose;
    private final int steps;


    public AutoDismissDialog(Frame parent,
                             String message,
                             final int delay,
                             final int rate,
                             final int delayStartToDispose,
                             final int delayDisposeToEnd) {
        dialog = new JDialog(parent, "Message", false);
        messagePanel = new JPanel();
        messagePanel.add(new JLabel(message));
        messagePanel.setBackground(new Color(1, 0.7f, 0.7f));
        dialog.getContentPane().add(messagePanel);
        timer = new Timer();
        steps = (delay - delayStartToDispose - delayDisposeToEnd) / rate;
        remainingSteps = steps;
        this.delay = delay;
        this.rate = rate;
        this.delayStartToDispose = delayStartToDispose;
        dialog.pack();
    }


    public AutoDismissDialog(Frame parent,
                             String message) {
        this(parent, message, DEFAULT_DELAY, DEFAULT_RATE,
             DEFAULT_DELAY_START_TO_DISPOSE, DEFAULT_DELAY_DISPOSE_TO_END);
    }


    public AutoDismissDialog(String message) {
        this(null, message);
    }


    public void show() {
        timer.schedule(new TimerTask() {

            @Override
            public void run() {
                dialog.dispose();
                timer.cancel();
            }
        }, delay);
        timer.scheduleAtFixedRate(new TimerTask() {

            @Override
            public void run() {
                if (remainingSteps > 0) {
                    remainingSteps--;
                    float alpha = (float) remainingSteps / (float) steps;
                    float rgValue = 0.7f + 0.3f * (1 - alpha);
                    messagePanel.setBackground(new Color(1, rgValue, rgValue));
                }
            }
        }, delayStartToDispose, rate);
        dialog.setVisible(true);
    }
//    private void setPosition() {
//        if (dialog.getParent() != null
//                    && dialog.getParent().getBounds() != null) {
//                Container parent = dialog.getParent();
//                // dimension of scroll pane minus frame dimension
//                int x = parent.getBounds().width - INIT_SIZE.width;
//                int y = parent.getBounds().height - INIT_SIZE.height;
//                // plus parent positions
//                parent = parent.getParent();
//                while (parent != null) {
//                    x += parent.getBounds().x;
//                    y += parent.getBounds().y;
//                    parent = parent.getParent();
//                }
//                setLocation(x, y);
//                pack();
//            }
//    }
}