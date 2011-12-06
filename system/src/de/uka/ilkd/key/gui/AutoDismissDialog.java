/*
 * To change this template, choose Tools | Templates and open the template in
 * the editor.
 */
package de.uka.ilkd.key.gui;

import java.awt.Color;
import java.awt.Component;
import java.util.Timer;
import java.util.TimerTask;
import javax.swing.JDialog;
import javax.swing.JOptionPane;
import javax.swing.UIManager;



/**
 *
 * @author christoph
 */
public class AutoDismissDialog {

    public static final int DEFAULT_DELAY = 5000;
    public static final int DEFAULT_RATE = 100;
    public static final int DEFAULT_DELAY_TO_START_TO_DISPOSE = 3000;
    private JDialog dialog;
    private int remainingSteps;
    private int delay , rate, delayToStartToDispose;


    public AutoDismissDialog(Component parent,
                             Object message,
                             final int delay,
                             final int rate,
                             final int delayToStartToDispose) {
        final JOptionPane optionPane = new JOptionPane(message);
        String title = UIManager.getString("OptionPane.messageDialogTitle");
        dialog = optionPane.createDialog(parent, title);
        final int steps = (delay - delayToStartToDispose) / rate;
        remainingSteps = steps;
        this.delay = delay;
        this.rate = rate;
        this.delayToStartToDispose = delayToStartToDispose;
    }


    public AutoDismissDialog(Component parent,
                             Object message) {
        this(parent, message, DEFAULT_DELAY, DEFAULT_RATE,
             DEFAULT_DELAY_TO_START_TO_DISPOSE);
    }


    public AutoDismissDialog(Object message) {
        this(null, message);
    }


    public void show() {
        final int steps = (delay - delayToStartToDispose) / rate;
        Timer timer = new Timer();
        timer.schedule(new TimerTask() {

            @Override
            public void run() {
                dialog.dispose();
            }
        }, delay);
        timer.scheduleAtFixedRate(new TimerTask() {

            @Override
            public void run() {
                remainingSteps--;
                int alpha = (255 * remainingSteps) / steps;
                dialog.setBackground(new Color(200, 0, 0, alpha));
            }
        }, delayToStartToDispose, rate);

        if (dialog.isDisplayable()) {
            dialog.setVisible(true);
        }
    }
}
