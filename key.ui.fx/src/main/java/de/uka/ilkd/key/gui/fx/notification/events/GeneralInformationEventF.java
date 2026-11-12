/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification.events;

import de.uka.ilkd.key.gui.fx.notification.NotificationEventIDF;

/**
 * If the system wants to inform the user it may emit this event. If the flavour of the
 * information is that of an error message, one should use the
 * {@link GeneralFailureEventF} instead.
 * <p>
 * Port of the Swing original {@code key.ui/src/main/java/de/uka/ilkd/key/gui/notification/
 * events/GeneralInformationEvent.java}.
 */
public class GeneralInformationEventF extends NotificationEventF {

    /** the message with the information to be displayed */
    private final String informationMessage;

    /** the context/ category of this message (e.g. used as window title) */
    private final String context;

    /**
     * Creates an event informing the user about the fact given as string
     *
     * @param context the String describing the context/category of the information (e.g. used as
     *        window title, head line etc.)
     * @param informationMessage the String containing the information
     */
    public GeneralInformationEventF(String context, String informationMessage) {
        super(NotificationEventIDF.GENERAL_INFORMATION);
        this.context = context;
        this.informationMessage = informationMessage;
    }

    /**
     * Creates an event informing the user about the fact given as string
     *
     * @param informationMessage the String containing the information
     */
    public GeneralInformationEventF(String informationMessage) {
        this("Information", informationMessage);
    }

    /**
     * returns the context as string
     */
    public String getContext() {
        return context;
    }

    /**
     * returns the information as string
     */
    public String getMessage() {
        return informationMessage;
    }
}
