/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.net.URI;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.util.MiscTools;

import org.antlr.v4.runtime.ParserRuleContext;

/**
 * This class maps a {@link ParserRuleContext} to a {@link TermLabel}.
 */
public class LabeledParserRuleContext {
    @Nonnull
    public final ParserRuleContext first;

    @Nullable
    public final List<TermLabel> second;

    public LabeledParserRuleContext(@Nonnull ParserRuleContext first, TermLabel second) {
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

    public LabeledParserRuleContext(ParserRuleContext ctx, OriginTermLabel.SpecType specType) {
        this(ctx, constructTermLabel(ctx, specType));
    }

    public LabeledParserRuleContext(@Nonnull ParserRuleContext first, List<TermLabel> second) {
        this.first = first;
        if (second != null) {
            this.second = Collections.unmodifiableList(second);
        } else {
            this.second = Collections.emptyList();
        }
    }

    private static TermLabel constructTermLabel(ParserRuleContext ctx,
            OriginTermLabel.SpecType specType) {
        URI filename = MiscTools.getURIFromTokenSource(ctx.start.getTokenSource());
        int line = ctx.start.getLine();
        OriginTermLabel.Origin origin = new OriginTermLabel.FileOrigin(specType, filename, line);
        return new OriginTermLabel(origin);
    }
}
