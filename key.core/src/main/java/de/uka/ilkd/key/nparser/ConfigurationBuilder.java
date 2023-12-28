/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.util.LinkedHashMap;

import org.jspecify.annotations.NonNull;

/**
 * Translates the configuration grammar (something like JSON) into a {@link Configuration} object.
 *
 * @author Alexander Weigl
 * @version 1 (03.04.23)
 * @see KeyAst.ConfigurationFile#asConfiguration()
 */
class ConfigurationBuilder extends KeYParserBaseVisitor<Object> {
    @Override
    public List<Object> visitCfile(KeYParser.CfileContext ctx) {
        return ctx.cvalue().stream().map(it -> it.accept(this)).collect(Collectors.toList());
    }

    @Override
    public String visitCkey(KeYParser.CkeyContext ctx) {
        if (ctx.STRING_LITERAL() != null)
            return sanitizeStringLiteral(ctx.STRING_LITERAL().getText());
        return ctx.IDENT().getText();
    }

    @Override
    public String visitCsymbol(KeYParser.CsymbolContext ctx) {
        return ctx.IDENT().getText();
    }


    @Override
    public String visitCstring(KeYParser.CstringContext ctx) {
        final var text = ctx.getText();
        return sanitizeStringLiteral(text);
    }

    @NonNull
    private static String sanitizeStringLiteral(String text) {
        return text.substring(1, text.length() - 1)
                .replace("\\\"", "\"")
                .replace("\\\\", "\\");
    }

    @Override
    public Long visitCintb(KeYParser.CintbContext ctx) {
        return Long.parseLong(ctx.getText(), 2);
    }

    @Override
    public Long visitCinth(KeYParser.CinthContext ctx) {
        return Long.parseLong(ctx.getText(), 16);
    }

    @Override
    public Long visitCintd(KeYParser.CintdContext ctx) {
        final var text = ctx.getText();
        if (text.endsWith("L") || text.endsWith("l")) {
            return Long.parseLong(text.substring(0, text.length() - 1), 10);
        } else {
            return Long.parseLong(text, 10);
        }
    }

    @Override
    public Double visitCfpf(KeYParser.CfpfContext ctx) {
        return Double.parseDouble(ctx.getText());
    }

    @Override
    public Double visitCfpd(KeYParser.CfpdContext ctx) {
        return Double.parseDouble(ctx.getText());
    }

    @Override
    public Double visitCfpr(KeYParser.CfprContext ctx) {
        return Double.parseDouble(ctx.getText());
    }

    @Override
    public Boolean visitCbool(KeYParser.CboolContext ctx) {
        return Boolean.parseBoolean(ctx.getText());
    }

    @Override
    public Configuration visitTable(KeYParser.TableContext ctx) {
        final var data = new LinkedHashMap<String, Object>();
        for (KeYParser.CkvContext context : ctx.ckv()) {
            var name = context.ckey().accept(this).toString();
            var val = context.cvalue().accept(this);
            data.put(name, val);
        }
        return new Configuration(data);
    }

    @Override
    public List<Object> visitList(KeYParser.ListContext ctx) {
        var seq = new ArrayList<>(ctx.children.size());
        for (KeYParser.CvalueContext context : ctx.cvalue()) {
            seq.add(context.accept(this));
        }
        return seq;
    }
}
