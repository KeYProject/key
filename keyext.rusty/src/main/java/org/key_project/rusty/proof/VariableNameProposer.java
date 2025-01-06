/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.logic.op.sv.SkolemTermSV;
import org.key_project.rusty.logic.op.sv.VariableSV;
import org.key_project.rusty.rule.TacletApp;
import org.key_project.util.collection.ImmutableList;

/**
 * Proposes names for variables (except program variables).
 */
public class VariableNameProposer implements InstantiationProposer {
    /**
     * An instance of VariableNameProposer.
     */
    public static final VariableNameProposer DEFAULT = new VariableNameProposer();

    private static final String SKOLEMTERM_VARIABLE_NAME_POSTFIX = "_";

    /**
     * Returns an instantiation proposal for the schema variable var. Currently supports names for
     * skolemterm SVs, variable SVs, and labels.
     */
    @Override
    public String getProposal(TacletApp app, SchemaVariable var, Services services, Node undoAnchor,
            ImmutableList<String> previousProposals) {
        if (var instanceof SkolemTermSV) {
            return getNameProposalForSkolemTermVariable(var, services,
                previousProposals);
        } else if (var instanceof VariableSV) {
            return getNameProposalForVariableSV(var, previousProposals);
        } else {
            return null;
        }
    }

    /**
     * Generates a proposal for the instantiation of the given term schema variable, which is
     * declared as skolem term SV.
     */
    private String getNameProposalForSkolemTermVariable(SchemaVariable p_var,
                                                        Services services, ImmutableList<String> previousProposals) {
        return getNameProposalForSkolemTermVariable(
            createBaseNameProposalBasedOnCorrespondence(p_var), services,
            previousProposals);
    }

    /**
     * Find a name for the variable <code>p_var</code>, based on the result of
     * <code>Taclet.getNameCorrespondent</code>
     */
    protected static String createBaseNameProposalBasedOnCorrespondence(SchemaVariable p_var) {
        // Use the name of the SkolemTermSV
        final String result = String.valueOf(p_var.name());

        // remove characters that should better not turn up in identifiers
        // more or less a HACK
        final Pattern pattern = Pattern.compile("[^_a-zA-Z0-9]");
        final Matcher matcher = pattern.matcher(result);

        final Pattern doubledUnderScores = Pattern.compile("__");

        return doubledUnderScores.matcher(matcher.replaceAll("_")).replaceAll("");
    }

    private String getNameProposalForSkolemTermVariable(String name, Services services,
            ImmutableList<String> previousProposals) {
        final NamespaceSet nss = services.getNamespaces();
        Name l_name;
        final String basename = name + SKOLEMTERM_VARIABLE_NAME_POSTFIX;
        int cnt = 0;
        do {
            name = basename + cnt;
            l_name = new Name(name);
            cnt++;
        } while (nss.lookup(l_name) != null && !previousProposals.contains(name));

        return name;
    }

    /**
     * Generates a proposal for the instantiation of the given schema variable, which is a variable
     * SV.
     *
     * The returned name is not necessarily globally unique, but that is not necessary for bound
     * variables.
     */
    private String getNameProposalForVariableSV(SchemaVariable var,
            ImmutableList<String> previousProposals) {
        String baseName = var.name().toString();
        if (previousProposals == null || !previousProposals.contains(baseName)) {
            return baseName;
        }

        for (int i = 1; i < Integer.MAX_VALUE; i++) {
            String name = baseName + "_" + i;
            if (!previousProposals.contains(name)) {
                return name;
            }
        }

        throw new Error("name proposer for " + baseName + " has run into infinite loop");
    }
}
