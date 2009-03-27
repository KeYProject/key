// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.gui.assistant;

import java.awt.*;
import java.awt.event.WindowListener;
import java.awt.geom.Arc2D;
import java.awt.geom.Area;
import java.awt.geom.RoundRectangle2D;

import javax.swing.*;

import de.uka.ilkd.key.gui.IconFactory;

/**
 * This class implements the user interface of the proof assistant.
 */
public class ProofAssistant extends JPanel {

    /** The background color of the bubble */
    private Color BACKGROUND_COLOR = new Color(1.0f,1.0f,0.8f);

    /** The amount of space around the bubble at top, left and right. */
    private int BORDER_WIDTH = 15;
    /** The rounding radius for the corners of the bubble. */
    private int ROUND_RADIUS = 15;
    /** The space between the bottom of the bubble and the bottom of
     * the window. */
    private int BOTTOM_HEIGHT = 80;

    /** The height of the Kiki image. */
    private int KIKI_HEIGHT = 60;
    /** The distance of Kiki's `mouth' from the top of the Kiki image. */
    private int KIKI_MOUTH_DESCENT = (int)(0.42 * KIKI_HEIGHT);

    /** An image of our friendly proof assistant */
    private Image KIKI_IMAGE = 
	IconFactory.keyAssistant(KIKI_HEIGHT, KIKI_HEIGHT).getImage();

    
    private JTextPane textPane;
    private JFrame frame;

    private static final String PREFIX = 
	"<html><body style=\"font-family:" +
	"'Times New Roman',Times,sans serif;font-size: 12pt;\">";

    private static final String POSTFIX = "</body></html>";

    /**
     * creates the assistant user interface
     */
    public ProofAssistant() {
	layoutAssistant();

	setText("Hi!<br>I am <strong>KiKi</strong> your " +
		"personal proof assistant. <br> You "+
		"can disable me in the <tt>Options</tt> menu.");

	// create the frame
	frame = new JFrame("Proof Assistant");
	frame.getContentPane().add(this);		
	frame.setDefaultCloseOperation
	    (WindowConstants.DO_NOTHING_ON_CLOSE);
	frame.pack();
	frame.setVisible(false);
    }
    
    /**
     * creates the layout for the proof assistant
     */

    private void layoutAssistant() {
	// These borders separate the scroll view from the window borders. 
	int border = ROUND_RADIUS + BORDER_WIDTH;
	int bottom = ROUND_RADIUS + BOTTOM_HEIGHT;
	setBorder(new javax.swing.border.EmptyBorder(border,border,
						     bottom,border));

 	BorderLayout layout = new BorderLayout();
	setLayout(layout);
	setBackground(Color.white);

	textPane = new JTextPane();
	textPane.setBackground(BACKGROUND_COLOR);
	textPane.setContentType("text/html");
	textPane.setEditable(false);

 	Dimension dim = new Dimension(200, 120);
 	JScrollPane scroll = 
 	    new JScrollPane(textPane,
 			    JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED,
 			    JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
 	scroll.setPreferredSize(dim);
	// The ScrollPane usually has a one pixel border, which we don't want.
	scroll.setBorder(new javax.swing.border.EmptyBorder(0,0,0,0));

 	add(scroll,BorderLayout.CENTER);
    }

    /** Paint the custom background for our component.
     * This consists of the rounded speech bubble and the Kiki image.
     */

    public void paintComponent(Graphics g) {
	// Paint the background white
	super.paintComponent(g);

	// Make a copy of the Graphics2D, so we can liberally change colors
	Graphics2D g2 = (Graphics2D)(g.create());

	Shape bubble = bubbleShape();

	g2.setColor(BACKGROUND_COLOR);
	g2.fill(bubble);
	g2.setColor(Color.black);
	g2.draw(bubble);

	// Draw the Kiki image, centered between the lower end of
	// the rounded box and the bottom of the window, and with the
	// right edge at the middle of the windows width.
	g2.drawImage(KIKI_IMAGE,getWidth()/2-KIKI_HEIGHT,
		     getHeight()-BOTTOM_HEIGHT+
		     (BOTTOM_HEIGHT-KIKI_HEIGHT)/2,null);
    }

    /** Return the shape of the bubble, depending on window size.  The
     * bubble consists of a top part in th form of a rounded
     * rectangle and a spike coming out on the lower side.
     */
    private Shape bubbleShape() {
	// The upper part
	Shape rbox = new RoundRectangle2D.Double(
            BORDER_WIDTH,BORDER_WIDTH,
	    getWidth()-2*BORDER_WIDTH,
	    getHeight()-BOTTOM_HEIGHT-BORDER_WIDTH,
	    ROUND_RADIUS,ROUND_RADIUS);

	// The spike is the difference of two elliptical arcs,
	// centered on the middle of the lower edge of the rounded box.

	int arcHeight = (BOTTOM_HEIGHT-KIKI_HEIGHT) + 2*KIKI_MOUTH_DESCENT;
	int bigArcWidth = arcHeight;

	// We make sure that the right arc of the spike doesn't
	// interfere with the rounding of the box.
	if (bigArcWidth > getWidth()-2*BORDER_WIDTH-2*ROUND_RADIUS) {
	    bigArcWidth = getWidth()-2*BORDER_WIDTH-2*ROUND_RADIUS;
	}
	int smallArcWidth = (int)(0.46*bigArcWidth);

	// We take the whole ellipse for the smaller arc, to be
	// sure that we erase enough from the larger one.
	Shape smallArc = new Arc2D.Double(getWidth()/2-smallArcWidth/2,
					  getHeight()-BOTTOM_HEIGHT-arcHeight/2,
					  smallArcWidth, arcHeight,
					  0,360,
					  Arc2D.CHORD);

	Shape bigArc = new Arc2D.Double(getWidth()/2-bigArcWidth/2,
					getHeight()-BOTTOM_HEIGHT-arcHeight/2,
					bigArcWidth, arcHeight,
					-90,180,
					Arc2D.CHORD);

	Area bubble = new Area(bigArc);
	bubble.subtract(new Area(smallArc));
	bubble.add(new Area(rbox));

	return bubble;
    }

    public int getWidth() {
	return frame.getWidth();
    }

    public void setLocation(int x, int y) {
	frame.setLocation(x, y);
    }

    public void tearUp() {
	frame.setVisible(true);	
	frame.setState(Frame.NORMAL);
	frame.toFront();	
    }

    public void tearDown() {
	frame.setVisible(false);
    }

    /**
     * adds the listener to the window listeners
     */
    public void addWindowListener(WindowListener l) {
	frame.addWindowListener(l);
    }

    /**
     * removes the listener from the window listeners
     */
    public void removeWindowListener(WindowListener l) {
	frame.removeWindowListener(l);
    }

    /**
     * sets the text tip to be shown 
     * @param text the String to be displayed
     */
    public void setText(String text) {
	textPane.setText(PREFIX+text+POSTFIX);
	textPane.setCaretPosition(0);
    }

    public static void main(String[] ags) {
	new ProofAssistant();
    }
}
