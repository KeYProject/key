
package de.uka.ilkd.key.gui.utilities;

import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.Point;
import java.awt.Toolkit;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.HashMap;

import javax.swing.JComponent;
import javax.swing.JScrollPane;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.gui.nodeviews.SequentView;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.*;

public final class GuiUtilities {
    public static final int LINE_WIDTH = 100;
    public static final int INDENT = 4;

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

    public static String writeTerm(Term term) {
        final NotationInfo ni = new NotationInfo();
        LogicPrinter p = new SequentViewLogicPrinter(new ProgramPrinter(), ni, null,
                new TermLabelVisibilityManager());
        p.setLineWidth(LINE_WIDTH);
        p.reset();

        try {
            p.printTerm(term);
        } catch (IOException ioe) {
            return term.toString();
        }
        return p.result().toString().trim();
    }

    private static int calculateParameterWidth(Iterable<String> args) {
        var width = 0;
        for (var k : args) {
            width = Math.max(k.length(), width);
        }

        return width;
    }

    private static String indentStringWith(String value, String indent) {
        return value.replaceAll("(?m)^", indent);
    }

    public static String writeCommand(String name, String firstArg, HashMap<String, String> args) {
        // indent parameters once
        StringWriter sout = new StringWriter();
        PrintWriter out = new PrintWriter(sout);

        out.format("%s %s", name, firstArg);

        var width = calculateParameterWidth(args.keySet()) + INDENT;
        var format = "%n%" + width + "s='%s'";

        // indent inner lines once again
        var innerIndent = " ".repeat(2 + width);
        args.forEach((k, v) ->  {
            out.format(format, k, indentStringWith(v, innerIndent).trim());
        });

        out.format(";%n");
        return sout.toString();
    }

    public static void copyTermToClipboard(PosInSequent pos) {
        var text = writeTerm(pos.getPosInOccurrence().subTerm());
        setClipboardText(text);
    }

    public static void copySelectMacroToClipboard(PosInSequent pos) {
        var where = pos.getPosInOccurrence().isInAntec() ? "antecedent" : "succedent";
        var args = new HashMap<String, String>(1);
        var term = writeTerm(pos.getPosInOccurrence().topLevel().subTerm());
        args.put("formula", term);
        var text = writeCommand("select", where, args);
        setClipboardText(text);
    }

    public static void copyHighlightToClipboard(SequentView view, PosInSequent pos) {
        // Replace nbsp; from html with normal spaces
        String s = view.getHighlightedText(pos).replace('\u00A0', ' ');
        // now CLIPBOARD
        setClipboardText(s);
    }

    public static void setClipboardText(String text) {
        java.awt.datatransfer.StringSelection ss =
                new java.awt.datatransfer.StringSelection(text);
        java.awt.Toolkit toolkit = Toolkit.getDefaultToolkit();
        toolkit.getSystemClipboard().setContents(ss, ss);
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
        if (frameSize.height > screenSize.height) {
            frameSize.height = screenSize.height;
        }
        if (frameSize.width > screenSize.width) {
            frameSize.width = screenSize.width;
        }
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
        if (dlgSize.width < frmSize.width && dlgSize.height < frmSize.height) {
            comp.setLocation((frmSize.width - dlgSize.width) / 2 + loc.x, (frmSize.height - dlgSize.height) / 2 + loc.y);
        } else {
            setCenter(comp);
        }
    }
}
