package de.uka.ilkd.key.gui.nodeviews;

import de.uka.ilkd.key.gui.configuration.Config;
import static de.uka.ilkd.key.gui.nodeviews.MainFrame.customRed;
import static de.uka.ilkd.key.gui.nodeviews.MainFrame.customRedLight;
import static de.uka.ilkd.key.gui.nodeviews.MainFrame.transparent;
import static de.uka.ilkd.key.gui.nodeviews.SequentBorder.darkPurple;
import java.awt.Color;
import java.awt.Cursor;
import java.awt.Font;
import java.awt.Insets;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import javax.swing.JLabel;
import javax.swing.UIManager;
import javax.swing.border.CompoundBorder;
import javax.swing.border.EmptyBorder;
import javax.swing.border.LineBorder;

/**
 *
 * @author Kai Wallisch
 */
public class TitleButton extends JLabel
        implements MouseListener {

    private static char turnstile = '\u22A2';
    private boolean isActivated = false;
    Color borderColor;
    SequentView sequentView;

    public void setActivated(boolean b) {
        isActivated = b;
        if (isActivated) {
            setBackground(borderColor);
        } else {
            setBackground(transparent);
        }
    }

    public void setFontStyle(int style) {
        setFont(getFont().deriveFont(style));
    }

    public void setBorderColor(Color c) {
        borderColor = c;
        setBorder(new CompoundBorder(
                new LineBorder(borderColor),
                new EmptyBorder(new Insets(1, 5, 1, 5))));
    }

    TitleButton(SequentView sequentView) {

        this.sequentView = sequentView;

        setBorderColor(Color.GRAY);
        setBackground(transparent);
        setForeground(Color.BLACK);
        setOpaque(true);
        setText(sequentView.getTitle());
        setFont(new Font("Monospaced", Font.PLAIN, 14));
        setFontStyle(Font.PLAIN);
        setCursor(Cursor.getPredefinedCursor(Cursor.HAND_CURSOR));

        addMouseListener(this);
    }

    public void mouseClicked(MouseEvent me) {
    }

    public void mousePressed(MouseEvent me) {
        setActivated(!isActivated);
        getParent().repaint();
    }

    public void mouseReleased(MouseEvent me) {
    }

    public void mouseEntered(MouseEvent me) {
    }

    public void mouseExited(MouseEvent me) {
    }
}