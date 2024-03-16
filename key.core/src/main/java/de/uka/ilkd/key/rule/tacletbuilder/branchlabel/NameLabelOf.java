/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.tacletbuilder.branchlabel;

import java.nio.file.Paths;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.SpecNameLabel;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.TacletApp;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * {@code NameLabelOf} tries to find a the {@link de.uka.ilkd.key.logic.label.TermLabel}
 * {@code name}
 * for the given instantiation specified schema variables.
 * <p>
 * If not name label is found. It fallbacks to the string representation of the instantiation.
 */
public class NameLabelOf implements BranchNamingFunction {
    private static final Logger LOGGER = LoggerFactory.getLogger(NameLabelOf.class);
    private final String matchedSchemaVariableName;

    public NameLabelOf(String matchedSchemaVariableName) {
        this.matchedSchemaVariableName = matchedSchemaVariableName;
    }

    public NameLabelOf(List<String> args) {
        this(args.get(1));
    }

    @Override
    public String getName(Services services, SequentChangeInfo currentSequent,
            TacletApp tacletApp,
            MatchConditions matchConditions) {
        var sv = matchConditions.getInstantiations().lookupVar(
            new Name(matchedSchemaVariableName));
        var value = matchConditions.getInstantiations().getInstantiation(sv);
        try {
            var term = (Term) value;
            var name = term.getLabel(SpecNameLabel.NAME);

            if (name != null) {
                return ((SpecNameLabel) name).getLabel();
                // return LogicPrinter.quickPrintTerm(term, services);
            }

            var originLabel = (OriginTermLabel) term.getLabel(OriginTermLabel.NAME);
            if (originLabel != null) {
                var origin = originLabel.getOrigin();
                if (origin instanceof OriginTermLabel.FileOrigin) {
                    var filename = ((OriginTermLabel.FileOrigin) origin).getFileName()
                            .map(it -> Paths.get(it).getFileName().toString())
                            .orElse("");
                    return origin.specType.toString() + ": " + filename
                        + "@" + ((OriginTermLabel.FileOrigin) origin).getLine();
                }
            }
            return LogicPrinter.quickPrintTerm(term, services);
        } catch (ClassCastException e) {
            LOGGER.info("Unexpected non-term value.", e);
            return value.toString();
        }
    }
}
