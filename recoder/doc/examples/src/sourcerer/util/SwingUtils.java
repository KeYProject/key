package sourcerer.util;

import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Insets;
import java.awt.Rectangle;
import java.awt.Window;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;

import javax.swing.AbstractButton;
import javax.swing.Action;
import javax.swing.BorderFactory;
import javax.swing.Icon;
import javax.swing.JButton;
import javax.swing.JCheckBoxMenuItem;
import javax.swing.JDesktopPane;
import javax.swing.JFrame;
import javax.swing.JInternalFrame;
import javax.swing.JMenu;
import javax.swing.JMenuItem;
import javax.swing.JPopupMenu;
import javax.swing.JWindow;
import javax.swing.KeyStroke;
import javax.swing.UIManager;
import javax.swing.UnsupportedLookAndFeelException;

/**
   Auxiliaries for Swing.
 */
public class SwingUtils {

    /**
      Workaround for swing bug.
    */
    public static JMenuItem addAction(JMenu menu, Action a) {
	JMenuItem item = menu.add(a);
	Object value = a.getValue(Action.ACCELERATOR_KEY);
	if (value != null) {
	    item.setAccelerator((KeyStroke)value);
	}
	return item;
    }

    /**
      Workaround for swing bug.
    */
    public static JCheckBoxMenuItem addCheckBoxAction(JMenu menu, Action a) {
	JCheckBoxMenuItem item = new JCheckBoxMenuItem();
	menu.add(item);
	setAction(item, a);
	return item;
    }

    /**
      Workaround for swing bug.
    */
    public static JMenuItem addAction(JPopupMenu menu, Action a) {
	JMenuItem item = menu.add(a);
	Object value = a.getValue(Action.ACCELERATOR_KEY);
	if (value != null) {
	    item.setAccelerator((KeyStroke)value);
	}
	return item;
    }

    /**
      1.2 compatibility
    */
    public static void setAction(AbstractButton b, Action a) {
	Object value = a.getValue(Action.NAME);
	if (value != null) {
	    b.setText(value.toString());
	}
	value = a.getValue(Action.MNEMONIC_KEY);
	if (value != null) {
	    b.setMnemonic(value.hashCode());
	}
	value = a.getValue(Action.SHORT_DESCRIPTION);
	if (value != null) {
	    b.setToolTipText(value.toString());
	}
	b.addActionListener(a);
    }

    /**
       Sets the system specific look and feel.
     */
    public static void setSystemLookAndFeel() {
	try {
	    UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
	} catch (ClassNotFoundException e1) {
	} catch (InstantiationException e2) {
	} catch (IllegalAccessException e3) {
	} catch (UnsupportedLookAndFeelException e4) {}
    }

   
    /*
       Replaces the default bold metal theme fonts.
       Also removes the borders from JSplitPanes.
    public static void setThinMetalTheme() {
    	MetalLookAndFeel.setCurrentTheme(SwingUtils.THIN_METAL_THEME);
	UIManager.put("SplitPane.border", BorderFactory.createEmptyBorder());
	UIManager.put("SplitPaneDivider.border", BorderFactory.createEmptyBorder());
    }
     */
    
    
    /**
       Sets the location of the window such that it is centered on the
       screen.
     */
    public static void centerOnScreen(Window w) {
	center(w, w.getGraphicsConfiguration().getBounds());
    }

    /**
       Sets the location of the window such that it is centered on the
       parent window.
     */
    public static void centerOnWindow(Window w, Window parent) {
        center(w, parent.getBounds());
    }

    private static void center(Window w, Rectangle parentBounds) {
        Dimension windowSize = w.getSize();
        w.setLocation((parentBounds.x + parentBounds.width - windowSize.width) / 2,
		      (parentBounds.y + parentBounds.height - windowSize.height) / 2);
    }
    
    /**
       Creates a splash screen, but does not open or close it yet.
     */
    public static Window createSplashScreen(Component content) {
	JWindow result = new JWindow();
        result.getContentPane().add(content);
        result.pack();
	centerOnScreen(result);
        return result;
    }

    private final static ThinLoweredBevelBorder THIN_LOWERED_BEVEL_BORDER = 
	new ThinLoweredBevelBorder();

    public static ThinLoweredBevelBorder createThinLoweredBevelBorder() {
	return THIN_LOWERED_BEVEL_BORDER;
    }
    
    public static class ThinLoweredBevelBorder extends javax.swing.border.AbstractBorder {

	protected Color highlight;
	protected Color shadow;

	public ThinLoweredBevelBorder() {}

	public ThinLoweredBevelBorder(Color highlight, Color shadow) {
	    this.shadow = shadow;
	    this.highlight = highlight;
	}

	public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
	    int w = width;
	    int h = height;	
	    g.translate(x, y);
	
	    g.setColor(getShadowColor(c));
	    g.drawLine(0, h-1, 0, 0);
	    g.drawLine(0, 0, w-1, 0);

	    g.setColor(getHighlightColor(c));
	    g.drawLine(0, h-1, w-1, h-1);
	    g.drawLine(w-1, h-1, w-1, 0);

	    g.translate(-x, -y);
	}

	public Insets getBorderInsets(Component c)       {
	    return new Insets(1, 1, 1, 1);
	}

	public Insets getBorderInsets(Component c, Insets insets) {
	    insets.left = insets.top = insets.right = insets.bottom = 1;
	    return insets;
	}

	public Color getHighlightColor(Component c)   {
	    return highlight != null? highlight : 
		c.getBackground().brighter();
	}
	
	public Color getHighlightColor()   {
	    return highlight;
	}

	public Color getShadowColor(Component c)   {
	    return shadow != null? shadow : c.getBackground().darker();
	}
	public Color getShadowColor()   {
	    return shadow;
	}	
    }

    public static class CloseButton extends JButton {
                
	public CloseButton() {
	    super(UIManager.getIcon("InternalFrame.closeIcon"));
	    setBorder(BorderFactory.createEmptyBorder());
	    setFocusPainted(false);
	}
            
	public boolean isFocusTraversable() {
	    return false;
	}   
    }

    public static class EmptyIcon implements Icon {
	int width;
	int height;

	public EmptyIcon(int width, int height) {
	    this.width = width;
	    this.height = height;
	}
       
	public final int getIconWidth() {
	    return width;
	}

	public final int getIconHeight() {
	    return height;
	}

	public final void paintIcon(Component c, Graphics g, int x, int y) {}
    }

    /*
      Aligns all menu items of the given menu (non-recursively) by
      inserting empty icons. The method does not attempt to align different
      icon widths.
     */
    public static void alignMenuItems(JMenu menu) {
	int c = menu.getItemCount();
	int maxWidth = 0;
	for (int i = 0; i < c; i++) {
	    JMenuItem item = menu.getItem(i);
	    if (item != null) {
		Icon icon = item.getIcon();
		if (icon != null) {
		    maxWidth = Math.max(maxWidth, icon.getIconWidth());
		}
	    }	    
	}
	if (maxWidth > 0) {
	    Icon emptyIcon = new EmptyIcon(maxWidth, 1);
	    for (int i = 0; i < c; i++) {
		JMenuItem item = menu.getItem(i);
		if (item != null && item.getIcon() == null) {
		    item.setIcon(emptyIcon);
		}
	    }
	}
    }
	
    /**
       Sets the location of the given internal frame and tries not to disturb
       other frames or icons on the given desktop.
       For this operation to work, the desktop must have a non-null
       size assigned already.
       The heuristic does not scale very well for huge numbers of frames,
       but this case is very unlikely to occur.
       In rare occasions, frames might overlap the right or bottom corner
       of the desktop; then, any other alternative would have been even more
       cruel, covering a lot of other frames.
       @param desktopPane the desktop to arrange the frame in.
       @param frame the frame to fit into the desktop; the frame
       may or may not be added to the desktop already.
     */
    public static void setGoodLocation(JDesktopPane desktopPane, 
				       JInternalFrame frame) {
	JInternalFrame[] frames = desktopPane.getAllFrames();
	Rectangle db = desktopPane.getBounds();
	db.x = db.y = 0;
	Rectangle[] frameBounds = new Rectangle[frames.length];
	int trialCount = frames.length;
	for (int i = frames.length - 1; i >= 0; i -= 1) {
	    JInternalFrame f = frames[i];
	    if (!f.isVisible() || f == frame) {
		frameBounds[i] = null;
		trialCount -= 1;
	    } else if (f.isIcon()) {
		frameBounds[i] = f.getDesktopIcon().getBounds();
		trialCount -= 1;
	    } else {
		frameBounds[i] = f.getBounds();
	    }
	}
	Rectangle tb = frame.getBounds();
	trialCount = 8 * trialCount + 4;
	int[] testx = new int[trialCount];
	int[] testy = new int[trialCount];
	testx[0] = 0;
	testy[0] = 0;
	testx[1] = Math.max(0, db.width - tb.width);
	testy[1] = 0;
	testx[2] = 0;
	testy[2] = Math.max(0, db.height - tb.height);
	testx[3] = Math.max(0, db.width - tb.width);
	testy[3] = Math.max(0, db.height - tb.height);
	for (int i = frameBounds.length - 1, j = 4; i >= 0; i -= 1) {
	    if (frames[i] == frame || frames[i].isIcon() || 
		!frames[i].isVisible()) {
		continue;
	    }
	    Rectangle r = frameBounds[i];
	    testx[j] = Math.max(0, r.x - tb.width);
	    testy[j++] = r.y;
	    testx[j] = Math.max(0, r.x - tb.width);
	    testy[j++] = Math.max(0, r.y + r.height - tb.height);
	    testx[j] = r.x;
	    testy[j++] = Math.max(0, r.y - tb.height);
	    testx[j] = Math.max(0, r.x + r.width - tb.width);
	    testy[j++] = Math.max(0, r.y - tb.height);
	    testx[j] = r.x + r.width;
	    testy[j++] = r.y;
	    testx[j] = r.x + r.width;
	    testy[j++] = Math.max(0, r.y + r.height - tb.height);
	    testx[j] = r.x;
	    testy[j++] = r.y + r.height;
	    testx[j] = Math.max(0, r.x + r.width - tb.width);
	    testy[j++] = r.y + r.height;
	}

	int bestx = 0;
	int besty = 0;
	long minBadness = Integer.MAX_VALUE;
	boolean coversTitle = false;
	for (int i = 0; i < testx.length; i += 1) {
	    long badness = testx[i] + 5L * testy[i];
	    tb.x = testx[i];
	    tb.y = testy[i];
	    boolean covers = false;
	    for (int j = frameBounds.length - 1; j >= 0; j -= 1) {
		Rectangle r = frameBounds[j];
		if (r != null && r.intersects(tb)) {
		    Rectangle xb = r.intersection(tb);
		    badness += 1000L * xb.width * xb.height;
		    if (xb.contains(r.x, r.y, 24, 24)) {
			covers = true;
		    }
		}
	    }
	    Rectangle xb = tb.intersection(db);	
	    badness += 10000L * (tb.width * tb.height - xb.width * xb.height);
	    if (badness < minBadness) {
		bestx = tb.x;
		besty = tb.y;
		minBadness = badness;
		coversTitle = covers;
	    }
	}
	if (coversTitle) {
	    besty += 32;
	}
	frame.setLocation(bestx, besty);
    }

    /**
       Rearranges all visible and not iconified internal frames in the given
       desktop pane. The method will temporarily remove all frames from
       the desktop and add them one by one in decreasing frame sizes,
       using the {@link #setGoodLocation} method.
       @param desktopPane the desktop to arrange all internal frames in.
     */
    public static void rearrangeFrames(JDesktopPane desktopPane) {
	JInternalFrame[] frames = desktopPane.getAllFrames();
	java.util.Vector v = new java.util.Vector();
	for (int i = frames.length - 1; i >= 0; i -= 1) {
	    if (frames[i].isVisible() && !frames[i].isIcon()) {
		v.addElement(frames[i]);
	    }
	}
	frames = new JInternalFrame[v.size()];
	v.copyInto(frames);
	// sort by size
	int[] size = new int[frames.length];
	for (int i = frames.length - 1; i >= 0; i -= 1) {	    
	    Dimension d = frames[i].getSize();
	    size[i] = d.width * d.height;
	}
	// sort by insertion: smallest frames to front
	for (int i = 1; i < frames.length; i += 1) {
	    JInternalFrame x = frames[i];
	    int s = size[i];
	    int j = i - 1;
	    while (j >= 0 && size[j] > s) {
		frames[j + 1] = frames[j];
		size[j + 1] = size[j];
		j -= 1;
	    }
	    frames[j + 1] = x;
	    size[j + 1] = s;
	}
	// remove from desktop
	for (int i = frames.length - 1; i >= 0; i -= 1) {	    
	    desktopPane.remove(frames[i]);
	}
	// add largest to smallest frames
	for (int i = frames.length - 1; i >= 0; i -= 1) {
	    setGoodLocation(desktopPane, frames[i]);
	    desktopPane.add(frames[i]);
	}	
	desktopPane.revalidate();
	desktopPane.repaint();
    }



    /**
       Test program.
     */
    static void main(String[] a) {
	JFrame f = new JFrame();
	f.setSize(960, 720);
	final JDesktopPane dpane = new JDesktopPane();
	f.getContentPane().add(dpane);
	f.setVisible(true);
	dpane.addMouseListener(new MouseAdapter() {
		public void mousePressed(MouseEvent e) {
		    int w = 0, h = 0;
		    if ((e.getModifiers() & MouseEvent.BUTTON1_MASK) != 0) {
			w = 80 + (int)(Math.random() * 560);
			h = 60 + (int)(Math.random() * 420);
		    } else if ((e.getModifiers() & MouseEvent.BUTTON2_MASK) != 0) {
			rearrangeFrames(dpane);
			return;
		    } else if ((e.getModifiers() & MouseEvent.BUTTON3_MASK) != 0) {
			w = 320;
			h = 240;
		    } else {
			return;
		    }
		    JInternalFrame fi = new JInternalFrame("" + w + " x " + h, true, true, true, true);
		    fi.setSize(w, h);
		    setGoodLocation(dpane, fi);
		    dpane.add(fi);
		    fi.setVisible(true);
		}
	    });
    }

    
}
