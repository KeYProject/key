/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser;

import java.net.URL;
import java.util.List;

import org.key_project.rusty.parser.builder.FindProblemInformation;
import org.key_project.rusty.parser.builder.IncludeFinder;
import org.key_project.rusty.proof.init.Includes;
import org.key_project.rusty.settings.Configuration;
import org.key_project.rusty.settings.ProofSettings;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.Interval;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public abstract class KeYAst<T extends ParserRuleContext> {
    final @NonNull T ctx;

    protected KeYAst(@NonNull T ctx) {
        this.ctx = ctx;
    }

    public <T> T accept(ParseTreeVisitor<T> visitor) {
        return ctx.accept(visitor);
    }

    /*
     * @Override
     * public String toString() {
     * return getClass().getName() + ": " + BuilderHelpers.getPosition(ctx);
     * }
     *
     * /*public Location getStartLocation() {
     * return Location.fromToken(ctx.start);
     * }
     */

    public String getText() {
        var interval = new Interval(ctx.start.getStartIndex(), ctx.stop.getStopIndex() + 1);
        return ctx.start.getInputStream().getText(interval);
    }

    public static class File extends KeYAst<KeYRustyParser.FileContext> {
        File(KeYRustyParser.FileContext ctx) {
            super(ctx);
        }

        public @Nullable ProofSettings findProofSettings() {
            return null;
        }

        public Includes getIncludes(URL base) {
            IncludeFinder finder = new IncludeFinder(base);
            accept(finder);
            return finder.getIncludes();
        }

        public ProblemInformation getProblemInformation() {
            FindProblemInformation fpi = new FindProblemInformation();
            ctx.accept(fpi);
            return fpi.getProblemInformation();
        }
    }

    public static class ConfigurationFile extends KeYAst<KeYRustyParser.CfileContext> {
        ConfigurationFile(KeYRustyParser.CfileContext ctx) {
            super(ctx);
        }

        public Configuration asConfiguration() {
            final var cfg = new ConfigurationBuilder();
            List<Object> res = cfg.visitCfile(ctx);
            if (!res.isEmpty())
                return (Configuration) res.get(0);
            else
                throw new RuntimeException();
        }
    }
}
