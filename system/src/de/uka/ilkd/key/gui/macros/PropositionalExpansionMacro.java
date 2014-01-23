// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.gui.macros;

import java.util.Set;

import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.utilities.KeyStrokeManager;

/**
 * The macro PropositionalExpansionMacro apply rules to decompose propositional
 * toplevel formulas; but does not split the goal.
 *
 * The rules that are applied can be set in {@link #ADMITTED_RULES}.
 *
 * @author mattias ulbrich
 */
public class PropositionalExpansionMacro extends AbstractPropositionalExpansionMacro {

    @Override
    public String getName() {
        return "Propositional expansion (w/o splits)";
    }

    @Override
    public String getDescription() {
        return "Apply rules to decompose propositional toplevel formulas; " +
                "does not split the goal.";
    }

    private static final String[] ADMITTED_RULES = {
        "andLeft", "orRight", "impRight", "notLeft", "notRight", "close",
        "closeTrue", "closeFalse", "true_left", "false_right"
    };

    private static final Set<String> ADMITTED_RULES_SET = asSet(ADMITTED_RULES);

    @Override
    protected Set<String> getAdmittedRuleNames() {
        return ADMITTED_RULES_SET;
    }

    @Override
    public KeyStroke getKeyStroke () {
	return KeyStrokeManager.get(this);
    }
}
