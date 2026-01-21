package de.uka.ilkd.key.gui.nodeviews;

import javax.swing.JCheckBox;

/**
 * {@link JCheckBox} indicating whether taclet info is displayed for inner nodes in proof tree.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class TacletInfoToggle extends JCheckBox {
    private static final long serialVersionUID = 1L;

    private InnerNodeView innerNodeView = null;

    public TacletInfoToggle() {
        setText("Show taclet info (inner nodes only)");
        addChangeListener(e -> {
            if (innerNodeView != null) {
                innerNodeView.tacletInfo.setVisible(isSelected());
            }
        });
        setName(getClass().getSimpleName());
    }

    @Override
    public void setSelected(boolean b) {
        super.setSelected(b);
        if (innerNodeView != null) {
            innerNodeView.tacletInfo.setVisible(isSelected());
        }
    }

    public void setSequentView(SequentView sequentView) {
        if (sequentView instanceof InnerNodeView) {
            innerNodeView = (InnerNodeView) sequentView;
            setEnabled(true);
            innerNodeView.tacletInfo.setVisible(isSelected());
        } else {
            innerNodeView = null;
            setEnabled(false);
        }
    }
}
