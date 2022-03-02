/*
 * 1.1+Swing version.
 */

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.util.*;

public class Converter {
    ConversionPanel metricPanel, usaPanel;
    Unit[] metricDistances = new Unit[3];
    Unit[] usaDistances = new Unit[4];
    final static boolean COLORS = false;
    final static boolean DEBUG = false;
    final static String LOOKANDFEEL = null;
    ConverterRangeModel dataModel = new ConverterRangeModel();
    JPanel mainPane;

    /** 
     * Create the ConversionPanels (one for metric, another for U.S.).
     * I used "U.S." because although Imperial and U.S. distance
     * measurements are the same, this program could be extended to
     * include volume measurements, which aren't the same.
     *
     * Put the ConversionPanels into a frame, and bring up the frame.
     */
    public Converter() {
        //Create Unit objects for metric distances, and then 
        //instantiate a ConversionPanel with these Units.
        metricDistances[0] = new Unit("Centimeters", 0.01);
        metricDistances[1] = new Unit("Meters", 1.0);
        metricDistances[2] = new Unit("Kilometers", 1000.0);
        metricPanel = new ConversionPanel(this, "Metric System",
                                          metricDistances,
                                          dataModel);

        //Create Unit objects for U.S. distances, and then 
        //instantiate a ConversionPanel with these Units.
        usaDistances[0] = new Unit("Inches", 0.0254);
        usaDistances[1] = new Unit("Feet", 0.305);
        usaDistances[2] = new Unit("Yards", 0.914);
        usaDistances[3] = new Unit("Miles", 1613.0);
        usaPanel = new ConversionPanel(this, "U.S. System",
                                       usaDistances,
                                       new FollowerRangeModel(dataModel));

        //Create a JPanel, and add the ConversionPanels to it.
        mainPane = new JPanel();
        if (COLORS) {
            mainPane.setBackground(Color.red);
        }
        mainPane.setLayout(new GridLayout(2,1,5,5));
        mainPane.setBorder(BorderFactory.createEmptyBorder(5,5,5,5));
        mainPane.add(metricPanel);
        mainPane.add(usaPanel);
        resetMaxValues(true);
    }

    public void resetMaxValues(boolean resetCurrentValues) {
        double metricMultiplier = metricPanel.getMultiplier();
        double usaMultiplier = usaPanel.getMultiplier();
        int maximum = ConversionPanel.MAX;

        if (metricMultiplier > usaMultiplier) {
            maximum = (int)(ConversionPanel.MAX *
                      (usaMultiplier/metricMultiplier));
        }

        if (DEBUG) {
            System.out.println("in Converter resetMaxValues");
            System.out.println("  metricMultiplier = " 
                                + metricMultiplier
                             + "; usaMultiplier = "
                                + usaMultiplier
                             + "; maximum = " 
                                + maximum);
        }

        dataModel.setMaximum(maximum);

        if (resetCurrentValues) {
            dataModel.setDoubleValue(maximum);
        }
    }

    private static void initLookAndFeel() { 
        String lookAndFeel = null;

        if (LOOKANDFEEL != null) {
            if (LOOKANDFEEL.equals("Metal")) {
                lookAndFeel = UIManager.getCrossPlatformLookAndFeelClassName();
            } else if (LOOKANDFEEL.equals("System")) {
                lookAndFeel = UIManager.getSystemLookAndFeelClassName();
            } else if (LOOKANDFEEL.equals("Mac")) {
                lookAndFeel = "com.sun.java.swing.plaf.mac.MacLookAndFeel";
                //PENDING: check!
            } else if (LOOKANDFEEL.equals("Windows")) {
                lookAndFeel = "com.sun.java.swing.plaf.windows.WindowsLookAndFeel";
            } else if (LOOKANDFEEL.equals("Motif")) {
                lookAndFeel = "com.sun.java.swing.plaf.motif.MotifLookAndFeel";
            }

            if (DEBUG) {
                System.out.println("About to request look and feel: " 
                                   + lookAndFeel);
            }

            try {
                UIManager.setLookAndFeel(lookAndFeel);
            } catch (ClassNotFoundException e) {
                System.err.println("Couldn't find class for specified look and feel:"
                                   + lookAndFeel);
                System.err.println("Did you include the L&F library in the class path?");
                System.err.println("Using the default look and feel.");
            } catch (UnsupportedLookAndFeelException e) {
                System.err.println("Can't use the specified look and feel ("
                                   + lookAndFeel
                                   + ") on this platform.");
                System.err.println("Using the default look and feel.");
            } catch (Exception e) { 
                System.err.println("Couldn't get specified look and feel ("
                                   + lookAndFeel
                                   + "), for some reason.");
                System.err.println("Using the default look and feel.");
                e.printStackTrace();
            } 
        }
    }

    public static void main(String[] args) {
        initLookAndFeel();
        Converter converter = new Converter();

        //Create a new window.
        JFrame f = new JFrame("Converter");
        f.addWindowListener(new WindowAdapter() {
            public void windowClosing(WindowEvent e) {
                System.exit(0);
            }
        });

        //Add the JPanel to the window and display the window.
        //We can use a JPanel for the content pane because
        //JPanel is opaque.
        f.setContentPane(converter.mainPane);
        if (COLORS) {
           //This has no effect, since the JPanel completely
           //covers the content pane.
           f.getContentPane().setBackground(Color.green);
        }

        f.pack();        //Resizes the window to its natural size.
        f.setVisible(true);
    }
}
