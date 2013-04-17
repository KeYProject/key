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

package de.uka.ilkd.key.util;

import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.EventQueue;
import java.awt.Point;
import java.awt.TextArea;
import java.lang.reflect.InvocationTargetException;

import javax.swing.JComponent;
import javax.swing.JScrollPane;
import javax.swing.SwingUtilities;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.nodeviews.SequentView;

public class GuiUtilities {

    private static TextArea clipBoardTextArea;
    
    /**
     * The shared instance of the key file chooser.
     */
    private static KeYFileChooser fileChooser;

    private GuiUtilities() {
        throw new Error("Do not instantiate");
    }
    
    /** 
     * paints empty view with white background.
     */
    public static void paintEmptyViewComponent(JComponent pane, String name) {         
        pane.setBorder(new TitledBorder(name));
        pane.setBackground(Color.white);
        if (pane instanceof JScrollPane) {
            ((JScrollPane) pane).getViewport().setBackground(Color.white);
        }
        pane.setMinimumSize(new java.awt.Dimension(150,0));
    }

    /**
     * Invoke a runnable object on the AWT event thread and wait for the
     * execution to finish.
     * 
     * If an exception occurs during the run, the trace is printed to stderr.
     * 
     * @param runner
     *            Runnable capturing code to execute on the awt thread.
     */
    public static void invokeAndWait(Runnable runner) {
        if (SwingUtilities.isEventDispatchThread()) runner.run();
        else {
            try{
               SwingUtilities.invokeAndWait(runner);
            } catch(InterruptedException e) {
                System.err.println(e);
                e.printStackTrace();
            } catch(InvocationTargetException ite) {
               Throwable targetExc = ite.getTargetException();
               System.err.println(targetExc);
               targetExc.printStackTrace();
               ite.printStackTrace();
            }
        }
    }

    /**
     * Invoke a runnable object on the AWT event thread. Does not wait
     * necessarily for it to finish. If the current thread is already the event
     * queue, the {@link Runnable} object is simply executed.
     * 
     * @param runnable
     *            Runnable capturing code to execute on the awt thread.
     */
    public static void invokeOnEventQueue(Runnable runnable) {
        if(EventQueue.isDispatchThread()) {
            runnable.run();
        } else {
            SwingUtilities.invokeLater(runnable);
        }
    }

    // is this still needed?
    public static void copyHighlightToClipboard(SequentView view) {
        String s = view.getHighlightedText();
        // now CLIPBOARD
        java.awt.datatransfer.StringSelection ss = 
            new java.awt.datatransfer.StringSelection(s);
        final TextArea clipBoard = getClipBoardArea();
        clipBoard.getToolkit().getSystemClipboard().setContents(ss,ss);
        // now PRIMARY
        clipBoard.setText(s);
        clipBoard.selectAll();
    }

    // is this still needed?
    public static TextArea getClipBoardArea() {
        if (clipBoardTextArea == null) {
            clipBoardTextArea = new java.awt.TextArea(
        	    "",10,10,java.awt.TextArea.SCROLLBARS_NONE) {
        	/**
                     * 
                     */
                    private static final long serialVersionUID = 7729624612190406520L;

            public java.awt.Dimension getMaximumSize() {
        	    return new java.awt.Dimension(0,0);
        	}
            };
        }
        return clipBoardTextArea;
    }

    /**
     * Gets <b>the</b> file chooser for the prover.
     * 
     * The chooser is created lazily when first requested. It points to the
     * directory of the command line argument (if present), otherwise to the
     * user's home directory.
     * 
     * @param title
     *            the title of the key file chooser
     * 
     * @return the key file chooser
     */
    public static KeYFileChooser getFileChooser(String title) {
        if (fileChooser == null) {
            String initDir = Main.getFileNameOnStartUp() == null 
                             ? System.getProperty("user.dir")
                             : Main.getFileNameOnStartUp();
                             
            fileChooser = new KeYFileChooser(initDir);
        }
        
        fileChooser.setDialogTitle(title);
        fileChooser.prepare();
        return fileChooser;
    }

    /**
     * Center a component on the screen.
     * 
     * @param comp
     *            the component to be centered relative to the screen. It must
     *            already have its final size set.
     * @preconditions comp.getSize() as on screen.
     * @see #setCenter(Component, Component)
     */
    public static void setCenter(Component comp) {
        Dimension screenSize = comp.getToolkit().getScreenSize();
        Dimension frameSize = comp.getSize();
        if (frameSize.height > screenSize.height)
            frameSize.height = screenSize.height;
        if (frameSize.width > screenSize.width)
            frameSize.width = screenSize.width;
        comp.setLocation((screenSize.width - frameSize.width) / 2, (screenSize.height - frameSize.height) / 2);
    }

    /**
     * Center a component within a parental component.
     * 
     * @param comp
     *            the component to be centered.
     * @param parent
     *            center relative to what. <code>null</code> to center relative
     *            to screen.
     * @see #setCenter(Component)
     */
    public static void setCenter(Component comp, Component parent) {
        if (parent == null) {
            setCenter(comp);
            return;
        } 
        Dimension dlgSize = comp.getPreferredSize();
        Dimension frmSize = parent.getSize();
        Point	  loc = parent.getLocation();
        if (dlgSize.width < frmSize.width && dlgSize.height < frmSize.height)
            comp.setLocation((frmSize.width - dlgSize.width) / 2 + loc.x, (frmSize.height - dlgSize.height) / 2 + loc.y);
        else
            setCenter(comp);
    }
}