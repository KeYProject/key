/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.utilities;

import de.uka.ilkd.key.gui.utilities.CheckedUserInput.CheckedUserInputInspector;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.nparser.KeyIO;

/**
 * Inspects whether a given string can be translated into a formula.
 */
public class InspectorForFormulas implements CheckedUserInputInspector {

    private final Services services;



    public InspectorForFormulas(Services services) {
        super();
        this.services = services;
    }



    @Override
    public String check(String toBeChecked) {
        if (toBeChecked.isEmpty()) {
            return CheckedUserInputInspector.NO_USER_INPUT;
        }
        Term term = translate(services, toBeChecked);

        if (term == null) {
            return NO_USER_INPUT;
        }

        if (term.sort() != Sort.FORMULA) {
            return "Not a formula.";
        }
        return null;

    }

    public static Term translate(Services services, String toBeChecked) {
        try {
            return new KeyIO(services).parseExpression(toBeChecked);
        } catch (Throwable e) {
            return null;
        }
    }

}
