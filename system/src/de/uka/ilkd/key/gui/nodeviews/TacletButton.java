package de.uka.ilkd.key.gui.nodeviews;

import static de.uka.ilkd.key.gui.nodeviews.MainFrame.customRed;
import static de.uka.ilkd.key.gui.nodeviews.MainFrame.customRedLight;
import static de.uka.ilkd.key.gui.nodeviews.MainFrame.transparent;
import java.awt.Color;
import java.awt.Cursor;
import java.awt.Insets;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import javax.swing.JLabel;
import javax.swing.border.CompoundBorder;
import javax.swing.border.EmptyBorder;
import javax.swing.border.LineBorder;

/**
 *
 * @author Kai Wallisch
 */
public class TacletButton extends JLabel
        implements MouseListener {

    private static char turnstile = '\u22A2';
    private boolean isActivated = false;
    private boolean isTransparent = false;
    Color textColor, activatedColor, deactivatedColor;

    public void setTransparent(boolean b) {

        isTransparent = b;

        if (b) {
            textColor = transparent;
            activatedColor = transparent;
            deactivatedColor = transparent;
            setCursor(getParent().getCursor());
            this.setToolTipText(null);
        } else {
            textColor = Color.BLACK;
            activatedColor = customRed;
            deactivatedColor = customRedLight;
            setCursor(Cursor.getPredefinedCursor(Cursor.HAND_CURSOR));
            this.setToolTipText("Display applied rule information for Inner Nodes.");
        }

        setForeground(textColor);
        setBorder(new CompoundBorder(
                new LineBorder(activatedColor),
                new EmptyBorder(new Insets(2, 15, 2, 15))));
        setBackground(deactivatedColor);

    }

    public void setActivated(boolean b) {
        isActivated = b;
        if (isActivated) {
            setBackground(activatedColor);
        } else {
            setBackground(deactivatedColor);
        }
    }

    TacletButton() {
        setText(turnstile + "");
        setOpaque(true);
        addMouseListener(this);
        setTransparent(false);
    }

    public void mouseClicked(MouseEvent me) {
    }

    public void mousePressed(MouseEvent me) {
        if (!isTransparent) {
            setActivated(!isActivated);
            getParent().repaint();
        }
    }

    public void mouseReleased(MouseEvent me) {
    }

    public void mouseEntered(MouseEvent me) {
    }

    public void mouseExited(MouseEvent me) {
    }
}