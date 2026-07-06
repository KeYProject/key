/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.proofreplay;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import java.util.Collection;
import java.util.List;

@KeYGuiExtension.Info(name = "Proof Replayer", experimental = false, optional = true,
        description = """
                UI to help replaying stored proofs on new KeY versions. 
                """
)
@NullMarked
public class ProofReapplicationExtension implements KeYGuiExtension, KeYGuiExtension.LeftPanel {
    private @Nullable ProofReapplicationView view;

    @Override
    public Collection<TabPanel> getPanels(MainWindow window, KeYMediator mediator) {
        if (view == null) {
            view = new ProofReapplicationView(window, mediator);
        }
        return List.of(view);
    }
}