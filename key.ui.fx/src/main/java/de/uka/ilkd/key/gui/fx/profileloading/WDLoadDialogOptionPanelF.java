/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.profileloading;

import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.wd.WdProfile;

/**
 * Additional UI components for the selection of the WD semantics — the provider for the FX
 * extension SPI, counter-part of {@code de.uka.ilkd.key.gui.profileloading.WDLoadDialogOptionPanel}
 * in the Swing module {@code key.ui} (WDLoadDialogOptionPanel.java:22-33).
 * <p>
 * The class mirrors the Swing provider shell: it carries the {@link KeYGuiExtensionF.Info}
 * annotation ({@code experimental = false}, no name — Swing parity,
 * WDLoadDialogOptionPanel.java:23-24), implements the {@link KeYGuiExtensionF.LoadOptionPanelF}
 * capability (Swing {@code KeYGuiExtension.LoadOptionPanel}, KeYGuiExtension.java:266-279) with
 * the WD profile {@link WdProfile#INSTANCE} (Swing {@code getProfile},
 * WDLoadDialogOptionPanel.java:32-34) and serves a fresh {@link WDLoadOptionPanelF} per
 * {@link #get()} call (Swing {@code get()} returns
 * {@code new WDLoadDialogOptionPanelImpl()}, WDLoadDialogOptionPanel.java:26-28 — one panel per
 * profile per loading-options host instantiation). The panel construction stays inside
 * {@link #get()} so that the provider itself instantiates toolkit-free and is testable headless
 * ({@link WDLoadOptionPanelF} builds FX controls in its constructor).
 * <p>
 * Registered in the service-loader file
 * {@code META-INF/services/de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF} (Swing:
 * the 13th line of
 * {@code META-INF/services/de.uka.ilkd.key.gui.extension.api.KeYGuiExtension}) and consumed by
 * {@code LoadingOptionsDialogF} via
 * {@link de.uka.ilkd.key.gui.fx.extension.KeYGuiExtensionFacadeF#createAdditionalOptionPanels()}
 * (Swing {@code KeYGuiExtensionFacade.createAdditionalOptionPanels},
 * KeYGuiExtensionFacade.java:410-418).
 */
@KeYGuiExtensionF.Info(experimental = false)
public class WDLoadDialogOptionPanelF
        implements KeYGuiExtensionF, KeYGuiExtensionF.LoadOptionPanelF {

    @Override
    public KeYGuiExtensionF.OptionPanelF get() {
        return new WDLoadOptionPanelF();
    }

    @Override
    public Profile getProfile() {
        return WdProfile.INSTANCE;
    }
}
