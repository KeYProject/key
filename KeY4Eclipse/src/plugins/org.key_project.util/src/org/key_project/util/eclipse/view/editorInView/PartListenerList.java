/*******************************************************************************
 * Copyright (c) 2000, 2015 IBM Corporation and others.
 *
 * This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License 2.0
 * which accompanies this distribution, and is available at
 * https://www.eclipse.org/legal/epl-2.0/
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.key_project.util.eclipse.view.editorInView;

import org.eclipse.core.commands.common.EventManager;
import org.eclipse.core.runtime.SafeRunner;
import org.eclipse.jface.util.SafeRunnable;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.internal.misc.UIStats;

/**
 * Part listener list.
 */
/*
 * This class should be deleted when IPartListener and IPartListener2 renamed to
 * IPartListener.
 */
public class PartListenerList extends EventManager {

    /**
     * PartNotifier constructor comment.
     */
    public PartListenerList() {
        super();
    }

    /**
     * Adds an IPartListener to the part service.
     */
    public void addPartListener(IPartListener l) {
        addListenerObject(l);
    }

    /**
     * Calls a part listener with associated performance event instrumentation
     *
     * @param runnable
     * @param listener
     * @param part
     * @param description
     */
    private void fireEvent(SafeRunnable runnable, IPartListener listener, IWorkbenchPart part, String description) {
        String label = null;// for debugging
        if (UIStats.isDebugging(UIStats.NOTIFY_PART_LISTENERS)) {
            label = description + part.getTitle();
            UIStats.start(UIStats.NOTIFY_PART_LISTENERS, label);
        }
        SafeRunner.run(runnable);
        if (UIStats.isDebugging(UIStats.NOTIFY_PART_LISTENERS)) {
            UIStats.end(UIStats.NOTIFY_PART_LISTENERS, listener, label);
        }
    }

    /**
     * Notifies the listener that a part has been activated.
     */
    public void firePartActivated(final IWorkbenchPart part) {
        for (Object listener : getListeners()) {
            final IPartListener partListener = (IPartListener) listener;
            fireEvent(new SafeRunnable() {
                @Override
                public void run() {
                    partListener.partActivated(part);
                }
            }, partListener, part, "activated::"); //$NON-NLS-1$
        }
    }

    /**
     * Notifies the listener that a part has been brought to top.
     */
    public void firePartBroughtToTop(final IWorkbenchPart part) {
        for (Object listener : getListeners()) {
            final IPartListener partListener = (IPartListener) listener;
            fireEvent(new SafeRunnable() {
                @Override
                public void run() {
                    partListener.partBroughtToTop(part);
                }
            }, partListener, part, "broughtToTop::"); //$NON-NLS-1$
        }
    }

    /**
     * Notifies the listener that a part has been closed
     */
    public void firePartClosed(final IWorkbenchPart part) {
        for (Object element : getListeners()) {
            final IPartListener partListener = (IPartListener) element;
            fireEvent(new SafeRunnable() {
                @Override
                public void run() {
                    partListener.partClosed(part);
                }
            }, partListener, part, "closed::"); //$NON-NLS-1$
        }
    }

    /**
     * Notifies the listener that a part has been deactivated.
     */
    public void firePartDeactivated(final IWorkbenchPart part) {
        for (Object listener : getListeners()) {
            final IPartListener partListener = (IPartListener) listener;
            fireEvent(new SafeRunnable() {
                @Override
                public void run() {
                    partListener.partDeactivated(part);
                }
            }, partListener, part, "deactivated::"); //$NON-NLS-1$
        }
    }

    /**
     * Notifies the listener that a part has been opened.
     */
    public void firePartOpened(final IWorkbenchPart part) {
        for (Object listener : getListeners()) {
            final IPartListener partListener = (IPartListener) listener;
            fireEvent(new SafeRunnable() {
                @Override
                public void run() {
                    partListener.partOpened(part);
                }
            }, partListener, part, "opened::"); //$NON-NLS-1$
        }
    }

    /**
     * Removes an IPartListener from the part service.
     */
    public void removePartListener(IPartListener l) {
        removeListenerObject(l);
    }
}