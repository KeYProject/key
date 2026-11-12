/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;

/**
 * Instances of class implementing this interface are able to complete rule applications. At the
 * moment they are only responsible for built-in rule apps, but they should be generalized to treat
 * taclets as well.
 * <p>
 * Port of {@code de.uka.ilkd.key.gui.InteractiveRuleApplicationCompletion} in the Swing module
 * {@code key.ui} (that class lives in key.ui and is therefore not visible to this module; the
 * interface contract is copied verbatim). Implementations are registered at the dispatch chain of
 * {@link WindowUserInterfaceControlF#register(InteractiveRuleApplicationCompletionF)}, the FX
 * mirror of the Swing registry in the {@code WindowUserInterfaceControl} constructor
 * (WindowUserInterfaceControl.java:74-82).
 */
public interface InteractiveRuleApplicationCompletionF {

    /**
     * method called to complete the given builtin rule application
     *
     * @param app the app to complete
     * @param goal the goal where the app will be applied
     * @param forced a boolean indicating if the user shall be bothered if the instantiation is
     *        unique or can be chosen in a reasonable way as if unique
     * @return the completed app or null if completion was not possible
     */
    IBuiltInRuleApp complete(IBuiltInRuleApp app, Goal goal, boolean forced);

    /**
     * checks if this instance is responsible for the given app
     *
     * @param app the rule app
     * @return true iff this instance might be able to complete the app
     */
    boolean canComplete(IBuiltInRuleApp app);
}
