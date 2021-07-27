package de.uka.ilkd.key.gui.fonticons;

import javax.swing.*;
import java.awt.*;
import java.util.ArrayList;

/**
 * @author Alexander Weigl
 * @version 1 (15.03.19)
 */
public class ShowIcons extends JFrame {
    private static final long serialVersionUID = 8775474163870717215L;
    //private Box box = new Box(BoxLayout.Y_AXIS);
    private JPanel box = new JPanel(new GridLayout(0, 10));
    private JPanel search = new JPanel();
    private ArrayList<JLabel> icons = new ArrayList<>();


    public ShowIcons() {
        setTitle("ShowIcons");
        setLayout(new BorderLayout());


        JLabel lblSearch = new JLabel("Search:");
        JTextField txtSearch = new JTextField(25);
        search.add(lblSearch);
        search.add(txtSearch);
        txtSearch.addActionListener(l -> filter(txtSearch.getText()));

        for (IconFont fa : FontAwesomeRegular.values()) add(fa);
        for (IconFont fa : FontAwesomeSolid.values()) add(fa);
        for (IconFont fa : Entypo.values()) add(fa);
        for (IconFont fa : Typicons.values()) add(fa);

        JScrollPane scroll = new JScrollPane(box);
        setSize(500, 500);
        scroll.setPreferredSize(getSize());
        add(scroll, BorderLayout.CENTER);
        add(search, BorderLayout.NORTH);
        filter("");
    }

    public static final void main(String[] args) {
        new ShowIcons().setVisible(true);
    }

    private void filter(String text) {
        box.removeAll();
        if (text.isEmpty()) {
            for (Component c : icons)
                box.add(c);
        } else {
            for (Component c : icons) {
                String toolTipText = ((JComponent) c).getToolTipText();
                if (toolTipText != null && toolTipText.toLowerCase().contains(text.toLowerCase()))
                    box.add(c);
            }
        }
        box.revalidate();
    }

    private void add(IconFont fa) {
        JLabel lbl = new JLabel();
        lbl.setIcon(IconFontSwing.buildIcon(fa, 32f));
        lbl.setToolTipText(fa.getClass().getName() + "." + fa);
        icons.add(lbl);
    }
}
