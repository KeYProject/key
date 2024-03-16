/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.net.URI;
import java.util.Collections;
import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabelFactory;
import de.uka.ilkd.key.logic.label.SpecNameLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.util.MiscTools;

import org.antlr.v4.runtime.ParserRuleContext;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This class maps a {@link ParserRuleContext} to a {@link TermLabel}.
 */
@NullMarked
public class LabeledParserRuleContext {
    public final ParserRuleContext first;
    public final List<TermLabel> second;

    public LabeledParserRuleContext(ParserRuleContext first, @Nullable TermLabel second) {
        this.first = Objects.requireNonNull(first);
        if (second != null) {
            this.second = Collections.singletonList(second);
        } else {
            this.second = Collections.emptyList();
        }
    }

    public LabeledParserRuleContext(ParserRuleContext first) {
        this(first, (TermLabel) null);
    }

    public static LabeledParserRuleContext createLabeledParserRuleContext(
            ParserRuleContext ctx, OriginTermLabel.SpecType specType, boolean attachOriginLabel,
            JmlParser.@Nullable Entity_nameContext name) {
        return attachOriginLabel
                ? new LabeledParserRuleContext(ctx, constructTermLabel(ctx, specType, name))
                : new LabeledParserRuleContext(ctx);
    }

    public LabeledParserRuleContext(@NonNull ParserRuleContext first, List<TermLabel> labels) {
        this.first = first;
        if (labels != null) {
            this.second = Collections.unmodifiableList(labels);
        } else {
            this.second = Collections.emptyList();
        }
    }

    private static List<TermLabel> constructTermLabel(ParserRuleContext ctx,
            OriginTermLabel.SpecType specType, JmlParser.@Nullable Entity_nameContext name) {
        URI filename = MiscTools.getURIFromTokenSource(ctx.start.getTokenSource());
        int line = ctx.start.getLine();
        OriginTermLabel.Origin origin = new OriginTermLabel.FileOrigin(specType, filename, line);
        var originLabel = new OriginTermLabelFactory().createOriginTermLabel(origin);
        if (name != null) {
            var nameLabel = new SpecNameLabel(name.ident().getText());
            return List.of(originLabel, nameLabel);
        }
        return List.of(originLabel);

    }
}
