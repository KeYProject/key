/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.utilities;

import java.awt.*;
import java.util.ArrayList;
import java.util.LinkedList;
import javax.swing.*;
import javax.swing.event.HyperlinkEvent;
import javax.swing.text.html.HTMLDocument;
import javax.swing.text.html.HTMLEditorKit;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * A simple textpane that supports lines that can be clicked by the users in order to trigger
 * events. It can especially be used for messages that contain detailed information that should not
 * be showed all time, but that should be accessed by clicking on a short messages summarizing the
 * most important information.
 */
@NullMarked
public class ClickableMessageBox extends JTextPane {

    private static final long serialVersionUID = 7588093268080119674L;

    public interface ClickableMessageBoxListener {
        void eventMessageClicked(Object object);
    }

    private final ArrayList<Object> items = new ArrayList<>();
    private final LinkedList<ClickableMessageBoxListener> listeners =
        new LinkedList<>();
    private final HTMLEditorKit kit = new HTMLEditorKit();
    private final HTMLDocument doc = new HTMLDocument();

    /**
     * Creates the message box.
     *
     * <p>
     * The box installs its editor kit, document and hyperlink listener while the receiver is
     * still under initialization (EISOP initialization check); the listener only fires once the
     * box is displayed, after construction completes, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public ClickableMessageBox() {
        this.setEditorKit(kit);
        this.setDocument(doc);
        this.setEditable(false);
        this.addHyperlinkListener(e -> {
            if (e.getEventType() == HyperlinkEvent.EventType.ACTIVATED) {
                int index = Integer.parseInt(e.getDescription());
                Object item = items.get(index);
                for (ClickableMessageBoxListener listener : listeners) {
                    listener.eventMessageClicked(item);
                }
            }

        });
    }

    public void clear() {
        items.clear();
        this.setText("");
    }

    public void add(ClickableMessageBoxListener listener) {
        listeners.add(listener);
    }

    /**
     * Adds a message to the box, optionally as a clickable link.
     *
     * @param item the object to notify listeners about when the message is clicked, or
     *        {@code null} if the message is plain text without a link.
     * @param message the message text.
     * @param color the message color.
     *
     *         <p>
     *         A {@code null} item is stored in the index-aligned entry list but never delivered
     *         (only non-null items get a hyperlink); the layout call passes a {@code null}
     *         insert tag so the editor kit infers the tag from the HTML itself. Both deliberate
     *         {@code null}s are suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    public void add(@Nullable Object item, String message, Color color) {
        try {
            if (item != null) {
                kit.insertHTML(doc, doc.getLength(),
                    "<u><a href=\"" + items.size() + "\" style=\"color: rgb(" + color.getRed() + ","
                        + color.getGreen() + "," + color.getBlue() + ")\">" + message + "</a></u>",
                    0, 0, null);
            } else {
                kit.insertHTML(
                    doc, doc.getLength(), "<font color= rgb(" + color.getRed() + ","
                        + color.getGreen() + "," + color.getBlue() + ")\">" + message + "</font>",
                    0, 0, null);
            }
        } catch (Throwable e) {
            throw new RuntimeException(e);
        }
        items.add(item);

    }

}
